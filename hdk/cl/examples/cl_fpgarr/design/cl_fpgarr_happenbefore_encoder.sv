// This module encodes the happen-before information from a packed logging bus
// in a even more compact format.
// i.e. buffer standalong transaction ends (loge_valid) and encode them to
// transaction begins (logb_valid, logb_data)
module rr_packed2writeback_bus (
   input wire clk,
   input wire rstn,
   rr_packed_logging_bus_t.C in,
   rr_stream_bus_t.P out
);

// parameter check
generate
   if (in.LOGB_CHANNEL_CNT + in.LOGE_CHANNEL_CNT + in.FULL_WIDTH
       != out.FULL_WIDTH)
    $error("Writeback FULL_WIDTH mismatch: logb W%d, loge W%d, packed_logb_data W%d, writeback W%d\n",
      in.LOGB_CHANNEL_CNT, in.LOGE_CHANNEL_CNT, in.FULL_WIDTH, out.FULL_WIDTH);
endgenerate

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

assign out.valid = in.plogb.any_valid;
assign in.ready = out.ready;
assign out.len = out.valid?
   (in.plogb.len + out.OFFSET_WIDTH'(in.LOGB_CHANNEL_CNT + in.LOGE_CHANNEL_CNT))
   : 0;
// from LSB to MSB:
// logb_valid, loge_valid, packed_logb_data
assign out.data = {in.plogb.data, loge_valid_out, in.logb_valid};

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
      if (out.valid && out.ready)
         // the incoming loge_valid is not related to the happen-before of
         // the current logb_valid. That will be deferred to the next
         // transmission
         loge_valid_out[i] <= in.loge_valid[i];
      else if (!out.valid && in.loge_valid[i] && out.ready) begin
         // a standlone loge_valid comes
         loge_valid_out[i] <= 1;
         // there could only be at most 1 transaction finished between two
         // logging unit in the trace.
         no_loge_overwrite: assert(!loge_valid_out[i]);
      end
endmodule
