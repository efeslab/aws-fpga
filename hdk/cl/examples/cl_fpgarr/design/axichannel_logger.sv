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
  output wire logb_valid,
  input wire logb_ready,
  output wire [DATA_WIDTH-1:0] logb_data,
  output wire loge_valid,
  input wire loge_ready
);

// the xxx_pipe version are the signal passed to the traskidbuffer pipeline
// the output of the transkidbuffer is wired to output ports
wire logb_valid_pipe;
wire logb_ready_pipe;
wire [DATA_WIDTH-1:0] logb_data_pipe;
wire loge_valid_pipe;
wire loge_ready_pipe;
`ifdef FORMAL
// F_x is for formal properties
wire [DATA_WIDTH-1:0] F_loge_data_pipe;
wire [DATA_WIDTH-1:0] F_loge_data;
`endif
twowayhandshake_logger #(.DATA_WIDTH(DATA_WIDTH)) logger (
  .clk(clk),
  .rstn(rstn),
  .in_valid(in_valid),
  .in_ready(in_ready),
  .in_data(in_data),
  // logging traffic goes into transkidbuffer
  .logb_valid(logb_valid_pipe),
  .logb_ready(logb_ready_pipe),
  .logb_data(logb_data_pipe),
  .loge_valid(loge_valid_pipe),
  .loge_ready(loge_ready_pipe),
  .out_valid(out_valid),
  .out_ready(out_ready),
  .out_data(out_data)
);

// logb pipe transparently pass all stalls
transkidbuf_pipeline #(
  .DATA_WIDTH(DATA_WIDTH),
  .PIPE_DEPTH(PIPE_DEPTH),
  .PASS_LAST_STALL(1)) logb_pipe (
  .clk(clk),
  .rstn(rstn),
  .in_valid(logb_valid_pipe),
  .in_ready(logb_ready_pipe),
  .in_data(logb_data_pipe),
  .out_valid(logb_valid),
  .out_ready(logb_ready),
  .out_data(logb_data)
);
// loge pipe transpartently pass all stalls except the last one
transkidbuf_pipeline #(
  .DATA_WIDTH(DATA_WIDTH),
  .PIPE_DEPTH(PIPE_DEPTH),
  .PASS_LAST_STALL(0)) loge_pipe (
  .clk(clk),
  .rstn(rstn),
  .in_valid(loge_valid_pipe),
  .in_ready(loge_ready_pipe),
`ifdef FORMAL
  .in_data(F_loge_data_pipe),
`else
  .in_data(),
`endif
  .out_valid(loge_valid),
  .out_ready(loge_ready),
`ifdef FORMAL
  .out_data(F_loge_data)
`else
  .out_data()
`endif
);

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
