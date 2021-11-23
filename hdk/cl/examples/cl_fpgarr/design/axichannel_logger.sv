`ifdef FORMAL
`include "formal/properties.sv"
`endif
module axichannel_logger #(
  parameter DATA_WIDTH=32,
  parameter PIPE_DEPTH=4
) (
  input wire clk,
  input wire rstn,
  input wire in_valid,
  output wire in_ready,
  input wire [DATA_WIDTH-1:0] in_data,
  output wire out_valid,
  input wire out_ready,
  output wire [DATA_WIDTH-1:0] out_data,
  // pipelined logging output
  // backpressure comes from the logb_almful
  output wire logb_valid,
  output wire [DATA_WIDTH-1:0] logb_data,
  output wire loge_valid,
  input wire logb_almful
);

// The xxx_p version are the signals on the logger-side of the register
// pipeline
// The storage-backend-side of the register pipeline are wired to the output
// ports
wire logb_valid_p;
wire logb_ready_p;
wire [DATA_WIDTH-1:0] logb_data_p;
wire loge_valid_p;
wire logb_almful_p;
`ifdef FORMAL
// F_x is for formal properties
wire [DATA_WIDTH-1:0] F_loge_data_p;
wire [DATA_WIDTH-1:0] F_loge_data;
`endif
twowayhandshake_logger #(.DATA_WIDTH(DATA_WIDTH)) logger (
  .clk(clk),
  .rstn(rstn),
  .in_valid(in_valid),
  .in_ready(in_ready),
  .in_data(in_data),
  // logging traffic goes into the register pipeline
  .logb_valid(logb_valid_p),
  .logb_ready(logb_ready_p),
  .logb_data(logb_data_p),
  .loge_valid(loge_valid_p),
  // loge is not guarded by logb_almful
  // loge should also be guaranteed to not stall (see comments in
  // twowayhandshake_logger.sv for more details)
  .loge_ready(1'b1),
  .out_valid(out_valid),
  .out_ready(out_ready),
  .out_data(out_data)
);


// register pipeline, guarded by the logb_almful
// I prefer to pipeline individual signals instead of packing all together to
// ease the debugging. I guess the synthesizer will do whatever optimizations it
// likes.
// TODO: lib_pipe is still not the ideal implemention I want. Maybe consider
// reimplement my own version of lib_pipe
// 1. lib_pipe will not respond to rst if FPGA_LESS_RST is set (which is the case)
// 2. if no FPGA_LESS_RST, lib_pipe will
//     (1) generate asynchronous reset
//     (2) whether to do reset or not isn't configurable. sometimes I may only
//     want to reset the valid but not the data
assign logb_ready_p = !logb_almful_p;
lib_pipe #(
  .WIDTH(1), .STAGES(PIPE_DEPTH)
) logb_valid_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(logb_valid_p && logb_ready_p),  // valid && ready -> fifo conversion
  .out_bus(logb_valid)
);

lib_pipe #(
  .WIDTH(DATA_WIDTH), .STAGES(PIPE_DEPTH)
) logb_data_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(logb_data_p),
  .out_bus(logb_data)
);

lib_pipe #(
  .WIDTH(1), .STAGES(PIPE_DEPTH)
) loge_valid_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(loge_valid_p),
  .out_bus(loge_valid)
);
// for logb_almful
lib_pipe #(
  .WIDTH(1), .STAGES(PIPE_DEPTH)
) logb_almful_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(logb_almful),
  .out_bus(logb_almful_p)
);

`ifdef FORMAL
lib_pipe_pipe #(
  .WIDTH(DATA_WIDTH), .STAGES(PIPE_DEPTH)
) F_loge_data_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(F_loge_data_p)
  .out_bus(F_loge_data)
);
`endif

// TODO the proof for this module is no longer available after switching to BRAM

`ifdef FORMAL
assign F_loge_data_pipe = in_data;
`endif

`ifdef FORMAL
  `ifdef AXICHANNEL_LOGGER_SELF
    `define ASSUME assume
    `define ASSERT assert
  `else
    `define ASSUME assert
    `define ASSERT assume
  `endif
  ////////////////////////////////////////////////////////////////////////////
  // Init (assumption)
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  // reset properties
  `ifndef JASPERGOLD
  reg f_past_valid = 0;
  always @(posedge clk) begin
    if (!f_past_valid)
      `ASSUME(!rstn);
    f_past_valid <= 1;
  end
  `endif
  // }}} reset

  // Input AXI (assumption)
  `ASSUME property(RESET_CLEARS_VALID(clk, rstn, in_valid));
  `ASSUME property(HELD_VALID_DATA(clk, rstn, in_valid, in_ready, in_data));
  same_stall_signal: `ASSUME property (
    @(posedge clk) disable iff (!rstn) logb_ready == loge_ready
  );
  `ifndef JASPERGOLD
  // this is to fight the potential yosys bug
  always @(posedge clk)
  if (f_past_valid)
  if ($past(!rstn))
    `ASSUME(!in_valid);
  else if ($past(in_valid && !in_ready && rstn) && rstn)
    `ASSUME(in_valid && $stable(in_data));
  `endif

  // Output AXI (correctness)
  `ASSERT property(RESET_CLEARS_VALID(clk, rstn, out_valid));
  `ASSERT property(HELD_VALID_DATA(clk, rstn, out_valid, out_ready, out_data));
  
  // logging AXI (correctness)
  `ASSERT property(RESET_CLEARS_VALID(clk, rstn, logb_valid));
  `ASSERT property(HELD_VALID_DATA(clk, rstn, logb_valid, logb_ready, logb_data));
  `ASSERT property(RESET_CLEARS_VALID(clk, rstn, loge_valid));
  `ASSERT property(HELD_VALID_DATA(clk, rstn, loge_valid, loge_ready, F_loge_data));

  // sequence ordering input model (assumption)
  localparam F_CNTWIDTH=DATA_WIDTH;
  reg [F_CNTWIDTH-1:0] in_cnt;
  reg [F_CNTWIDTH-1:0] logb_cnt;
  reg [F_CNTWIDTH-1:0] loge_cnt;
  reg [F_CNTWIDTH-1:0] logb_cnt_pipe;
  reg [F_CNTWIDTH-1:0] loge_cnt_pipe;
  always @(posedge clk)
  if (!rstn) begin
    in_cnt <= 0;
  end
  else if (in_valid && in_ready) begin
    in_cnt <= in_cnt + 1;
  end

  always @(posedge clk)
  if (rstn && in_valid)
    input_inorder: `ASSUME(in_data == in_cnt);

  // stall asumptions
  always @(posedge clk)
  if (rstn)
    loge_never_stall: `ASSERT(!logger.loge_stall());

  // sequence ordering
  // intermediate twowayhandshake_logger output property(correctness)
  always @(posedge clk)
  if (!rstn) begin
    logb_cnt_pipe <= 0;
    loge_cnt_pipe <= 0;
  end
  else begin
    if (logb_valid_pipe && logb_ready_pipe) begin
      logb_cnt_pipe <= logb_cnt_pipe + 1;
    end
    if (logb_valid_pipe)
      pipe_in_logb_inorder: `ASSERT(logb_data_pipe == logb_cnt_pipe);
    if (loge_valid_pipe && loge_ready_pipe) begin
      loge_cnt_pipe <= loge_cnt_pipe + 1;
    end
    if (loge_valid_pipe)
      pipe_in_loge_inorder: `ASSERT(F_loge_data_pipe == loge_cnt_pipe);
  end

  // sequence ordering
  // transkidbuf pipeline output proeprty (correctness)
  always @(posedge clk)
    if (!rstn) begin
    logb_cnt <= 0;
    loge_cnt <= 0;
  end
  else begin
    if (logb_valid && logb_ready) begin
      logb_cnt <= logb_cnt + 1;
    end
    if (logb_valid)
      pipe_out_logb_inorder: `ASSERT(logb_data == logb_cnt);
    if (loge_valid && loge_ready) begin
      loge_cnt <= loge_cnt + 1;
    end
    if (loge_valid)
      pipe_out_loge_inorder: `ASSERT(F_loge_data == loge_cnt);
    intra_transaction_happenbefore: `ASSERT((logb_cnt == loge_cnt) || (logb_cnt == loge_cnt + 1));
  end

  ////////////////////////////////////////////////////////////////////////////
  // Proof
  ////////////////////////////////////////////////////////////////////////////
  // {{{
  // sequence ordering proof
  always @(posedge clk)
  if (rstn) begin
    if (logger.get_stall_logb())
      `ASSERT(logb_cnt_pipe == in_cnt + 1);
    else
      `ASSERT(logb_cnt_pipe == in_cnt);
    `ASSERT(logb_cnt_pipe == logb_pipe.in_cnt);
    `ASSERT(logb_cnt == logb_pipe.out_cnt);
    // we assume loge can never stall so loge finishes transactions at the same time as input
    `ASSERT(loge_cnt_pipe == in_cnt);
    `ASSERT(loge_cnt_pipe == loge_pipe.in_cnt);
    `ASSERT(loge_cnt == loge_pipe.out_cnt);
  end

  wire [F_CNTWIDTH-1:0] in_cnt_logb_pipe [PIPE_DEPTH-1:0];
  wire [F_CNTWIDTH-1:0] in_cnt_loge_pipe [PIPE_DEPTH-1:0];
  wire in_valid_logb_pipe [PIPE_DEPTH-1:0];
  genvar i;
  generate
    if (PIPE_DEPTH > 0) begin: proof_pipe_gen
      assign in_cnt_logb_pipe[0] = logb_pipe.pipe_gen.input_stage.in_cnt;
      assign in_cnt_loge_pipe[0] = loge_pipe.pipe_gen.input_stage.in_cnt;
      assign in_valid_logb_pipe[0] = logb_pipe.pipe_gen.input_stage.in_valid;
      for (i=1; i < PIPE_DEPTH; i=i+1) begin
        assign in_cnt_logb_pipe[i] = logb_pipe.pipe_gen.pipe_stages[i].pipe_stage.in_cnt;
        assign in_cnt_loge_pipe[i] = loge_pipe.pipe_gen.pipe_stages[i].pipe_stage.in_cnt;
        assign in_valid_logb_pipe[i] = logb_pipe.pipe_gen.pipe_stages[i].pipe_stage.in_valid;
      end
    end
    always @(posedge clk)
    if (rstn) begin
      for (int i=0; i < PIPE_DEPTH; i=i+1) begin: as_in_cnt_inv
        `ASSERT(
          (in_cnt_logb_pipe[i] == in_cnt_loge_pipe[i]) ||
          (in_cnt_logb_pipe[i] == in_cnt_loge_pipe[i] + 1)
        );
      end
    end
  endgenerate
  // loge never stall proof
  always @(posedge clk)
  if (rstn) begin
    if (logger.get_stall_logb())
      `ASSERT(loge_pipe.pipe_gen.input_stage.state != 'd2); // != FULL
  end
  // }}} // PROOF

`endif // FORMAL
endmodule
