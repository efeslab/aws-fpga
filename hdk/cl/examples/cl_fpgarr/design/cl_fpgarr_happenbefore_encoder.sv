`include "cl_fpgarr_defs.svh"
`include "cl_fpgarr_packing_cfg.svh"
// This module encodes the happen-before information from a packed logging bus
// in a even more compact format.
// i.e. buffer standalong transaction ends (loge_valid) and encode them to
// transaction begins (logb_valid, logb_data)
//
// About almful:
// The almful is only meant for logb, since standalone loge will not be pushed
// to the fifo (it will instead be consumed right in this module and tracked by
// the `loge_valid_out`).
// The almful is generated from the fifo here and propogate all the way to the
// individual channel loggers.
// The in.logb_almful should be asserted if the remaining capacity in the fifo
// greater or equal to the maximum number of future logb_related data, which
// consists of
// 1. on-the-fly logb_related data
// 2. the pipelined propogation of the logb_almful itself
// The optimal resource utilization is achieved if the logb_almful is asserted
// when remaining capacity "equal to" all potential future packets.
// At this moment, the almful is affected by:
// 1. 2*RECORDER_PIPE_DEPTH, the pipeline from individual channel logger to the
//     logb packing module. almful is also pipelined
// 2. 2*MERGE_TREE_HEIGHT, the pipeline stages in the merge tree. almful is also
//    pipelined
module rr_packed2writeback_bus (
   input wire clk,
   input wire rstn,
   rr_packed_logging_bus_t.C in,
   rr_stream_bus_t.P out
);
// RR_LOGB_FIFO_ALMFUL_THRESHOLD:
// 16 is random value chosen to overprovision some resource and avoid
// calculating the accurate almful threshold
// RR_LOGB_FIFO_PTR_WIDTH:
// The number of the elements in the fifo should be a power of 2
// WATERMARK is (2**RR_LOGB_FIFO_PTR_WIDTH - RR_LOGB_FIFO_ALMFUL_THRESHOLD)
localparam int RR_LOGB_FIFO_ALMFUL_THRESHOLD =
   2*RECORDER_PIPE_DEPTH + 2*record_pkg::MERGE_TREE_HEIGHT + 16;
localparam int RR_LOGB_FIFO_PTR_WIDTH = 7;
// parameter check
generate
   if (in.LOGB_CHANNEL_CNT + in.LOGE_CHANNEL_CNT + in.LOGB_DATA_WIDTH
       != out.FULL_WIDTH)
    $error("Writeback FULL_WIDTH mismatch: logb W%d, loge W%d, packed_logb_data W%d, writeback W%d\n",
      in.LOGB_CHANNEL_CNT, in.LOGE_CHANNEL_CNT, in.LOGB_DATA_WIDTH,
      out.FULL_WIDTH);
   if (RR_LOGB_FIFO_ALMFUL_THRESHOLD >= 2**RR_LOGB_FIFO_PTR_WIDTH)
      $error("Invalid RR_LOGB_FIFO config: ALMFUL_THRESHOLD %d, PTR_WIDTH %d\n",
         RR_LOGB_FIFO_ALMFUL_THRESHOLD, RR_LOGB_FIFO_PTR_WIDTH);
   $info("LOGB FIFO config: in total %d entries, threshold is %d entries left\n",
      2**RR_LOGB_FIFO_PTR_WIDTH, RR_LOGB_FIFO_ALMFUL_THRESHOLD);
endgenerate
// forward declare logb_fifo control signals
logic fifo_push;
logic fifo_pop;

// loge_valid_output is the signal outputting to the writeback_bus, it should be
// in-sync with out.valid
// Invariant description of loge_valid_output:
// 1. loge_valid_output[i] shows whether one (and can only be one) transaction
// has finished on channel[i] between now (some logb_valid are true, but
// excluding the loge_valid happens at the same cycle) and the last time some
// logb are valid.
// 2. In other words, when out.valid is asserted, loge_valid_output[i] together
// with all historical loge_valid_output values, represents the number of
// transactions finished in each channel (count the 1s) before the start of the
// logb_{valid, data} in the out.data.
// if logb_valid[i] && loge_valid[i], which only happen if the transaction
// really lasts for only one cycle (ready was asserted in advance)
logic [in.LOGE_CHANNEL_CNT-1:0] loge_valid_out;

// buf loge_valid if there is no valid logb to send
always @(posedge clk)
if (!rstn)
   loge_valid_out <= 0;
else
   for (int i=0; i < in.LOGE_CHANNEL_CNT; i=i+1)
      // loge_valid_out can only be updated when
      //   (out.valid && out.ready): loge_valid accumulated so far is recorded
      //   in the trace, I should restart the accumulation.
      //   (!out.valid): I cannot write to trace at this moment, any standalone
      //   loge_valid should be accumulated and wait for the next write to the
      //   trace.
      if (fifo_push)
         // the incoming loge_valid is not related to the happen-before of
         // the current logb_valid. That will be deferred to the next
         // transmission
         loge_valid_out[i] <= in.loge_valid[i];
      else if (in.loge_valid[i]) begin
         // a standlone loge_valid comes
         loge_valid_out[i] <= 1;
         // there could only be at most 1 transaction finished between two
         // logging unit in the trace.
         no_loge_overwrite: assert(!loge_valid_out[i]);
      end

// The FIFO to handle almful
// MSB to LSB: out.data, out.len
logic fifo_oflow;
logic fifo_empty;
assign fifo_push = in.plogb.any_valid;
assign fifo_pop = out.valid && out.ready;
ram_fifo_ft #(
   .WIDTH(out.FULL_WIDTH + out.OFFSET_WIDTH),
   .PTR_WIDTH(RR_LOGB_FIFO_PTR_WIDTH),
   .WATERMARK(2**RR_LOGB_FIFO_PTR_WIDTH - RR_LOGB_FIFO_ALMFUL_THRESHOLD),
   .PIPELINE(1)
) logb_fifo (
   .clk(clk),
   .rst_n(rstn),
   .push(fifo_push),
   .push_data({
      in.plogb.data,      // -
      loge_valid_out,     //  |-> These become out.data
      in.logb_valid,      // -
      out.OFFSET_WIDTH'(
         in.plogb.len + in.LOGB_CHANNEL_CNT + in.LOGE_CHANNEL_CNT
      ) // this is the out.len
   }),
   `ifdef TEST_RECORD_FIFO_ALMFUL
   .wmark(),
   `else
   .wmark(in.logb_almful),
   `endif
   .pop(fifo_pop),
   // out.data from LSB to MSB:
   // logb_valid, loge_valid, packed_logb_data
   // i.e. assign out.data = {in.plogb.data, loge_valid_out, in.logb_valid};

   .pop_data({out.data, out.len}),
   .valid(out.valid),
   .free_entries(),
   .oflow(fifo_oflow),
   .empty(fifo_empty)
);

`ifdef TEST_RECORD_FIFO_ALMFUL
logic [1:0] cnt;
always_ff @(posedge clk)
   if (!rstn)
      cnt <= 0;
   else
      cnt <= cnt + 1;
assign in.logb_almful = cnt[1];
`endif
endmodule
