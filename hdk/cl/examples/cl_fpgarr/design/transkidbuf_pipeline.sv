`include "formal/properties.sv"
module transkidbuf_pipeline #(
  parameter DATA_WIDTH=32,
  parameter PIPE_DEPTH=4,
  parameter PASS_LAST_STALL=0,
  parameter DEFAULT_PASS_STALL=1
) (
  input wire clk,
  input wire rstn,
  input wire in_valid,
  input wire [DATA_WIDTH-1:0] in_data,
  output wire in_ready,
  output wire out_valid,
  output wire [DATA_WIDTH-1:0] out_data,
  input wire out_ready
);
genvar i;
generate
  if (PIPE_DEPTH == 0) begin : pass_through
    assign in_ready = out_ready;
    assign out_valid = in_valid;
    assign out_data = in_data;
  end
  else if (PIPE_DEPTH > 0) begin : pipe_gen
    wire valid_pipe [PIPE_DEPTH-1:0];
    wire ready_pipe [PIPE_DEPTH-1:0];
    wire [DATA_WIDTH-1:0] data_pipe [PIPE_DEPTH-1:0];
    `ifdef FORMAL
    wire [DATA_WIDTH-1:0] in_cnt_pipe[PIPE_DEPTH-1:0];
    wire [DATA_WIDTH-1:0] out_cnt_pipe[PIPE_DEPTH-1:0];
    `endif
    localparam INIT_PASS_STALL =
      (PIPE_DEPTH==1)? PASS_LAST_STALL : DEFAULT_PASS_STALL;
    transkidbuf #(
      .DATA_WIDTH(DATA_WIDTH),
      .PASS_STALL(INIT_PASS_STALL)
    ) input_stage (
      .clk(clk),
      .rstn(rstn),
      .in_valid(in_valid),
      .in_data(in_data),
      .in_ready(in_ready),
      .out_valid(valid_pipe[0]),
      .out_data(data_pipe[0]),
      .out_ready(ready_pipe[0])
    );

    for (i=1; i < PIPE_DEPTH; i=i+1) begin: pipe_stages
      localparam PASS_STALL =
        (i==PIPE_DEPTH-1)? PASS_LAST_STALL : DEFAULT_PASS_STALL;
      transkidbuf #(
        .DATA_WIDTH(DATA_WIDTH),
        .PASS_STALL(PASS_STALL)
      ) pipe_stage (
        .clk(clk),
        .rstn(rstn),
        .in_valid(valid_pipe[i-1]),
        .in_data(data_pipe[i-1]),
        .in_ready(ready_pipe[i-1]),
        .out_valid(valid_pipe[i]),
        .out_data(data_pipe[i]),
        .out_ready(ready_pipe[i])
      );
    end

    assign ready_pipe[PIPE_DEPTH-1] = out_ready;
    assign out_valid = valid_pipe[PIPE_DEPTH-1];
    assign out_data = data_pipe[PIPE_DEPTH-1];
  end // PIPE_DEPTH > 0 generate
endgenerate
`ifdef FORMAL
  `ifdef TRANSKIDBUF_PIPELINE_SELF
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
  `ifdef TRANSKIDBUF_PIPELINE_SELF
  `ifndef JASPERGOLD
  reg f_past_valid = 0;
  always @(posedge clk) begin
    if (!f_past_valid)
      assume(!rstn);
    f_past_valid <= 1;
  end
  `endif
  `endif
  // }}} reset

  // Input AXI (assumption)
  `ASSUME property(RESET_CLEARS_VALID(clk, rstn, in_valid));
  `ASSUME property(HELD_VALID_DATA(clk, rstn, in_valid, in_ready, in_data));

  // Output AXI (correctness)
  `ASSERT property(RESET_CLEARS_VALID(clk, rstn, out_valid));
  `ASSERT property(HELD_VALID_DATA(clk, rstn, out_valid, out_ready, out_data));

  // sequence inorder behavior input model (assumption)
  localparam F_CNTWIDTH=DATA_WIDTH;
  reg [F_CNTWIDTH-1:0] in_cnt;
  reg [F_CNTWIDTH-1:0] out_cnt;
  function automatic [F_CNTWIDTH-1:0] get_in_cnt();
    get_in_cnt = in_cnt;
  endfunction
  function automatic [F_CNTWIDTH-1:0] get_out_cnt();
    get_out_cnt = out_cnt;
  endfunction
  always @(posedge clk)
  if (!rstn) begin
    in_cnt <= 0;
    out_cnt <= 0;
  end
  else begin
    if (in_valid && in_ready) begin
      in_cnt <= in_cnt + 1;
    `ASSUME(in_data == in_cnt);
    end
    if (out_valid && out_ready) begin
      out_cnt <= out_cnt + 1;
    end
  end

  // sequence inorder behavior property to verify (correctness)
  always @(posedge clk)
  if (rstn)
    if (out_valid && out_ready)
      `ASSERT(out_data == out_cnt);

  `ifdef TRANSKIDBUF_PIPELINE_SELF
  // sequence inorder behavior proof
  generate
    if (PIPE_DEPTH > 0) begin: proof_pipe_gen
        assign pipe_gen.in_cnt_pipe[0] = pipe_gen.input_stage.get_in_cnt();
        assign pipe_gen.out_cnt_pipe[0] = pipe_gen.input_stage.get_out_cnt();
        for (i=1; i < PIPE_DEPTH; i=i+1) begin
          assign pipe_gen.in_cnt_pipe[i] = pipe_gen.pipe_stages[i].pipe_stage.get_in_cnt();
          assign pipe_gen.out_cnt_pipe[i] = pipe_gen.pipe_stages[i].pipe_stage.get_out_cnt();
        end
        always @(posedge clk)
        if (rstn) begin
          `ASSERT(in_cnt == pipe_gen.in_cnt_pipe[0]);
          `ASSERT(pipe_gen.out_cnt_pipe[PIPE_DEPTH-1] == out_cnt);
          for (int i=1; i < PIPE_DEPTH; i=i+1) begin
            `ASSERT(pipe_gen.out_cnt_pipe[i-1] == pipe_gen.in_cnt_pipe[i]);
          end
        end
    end
  endgenerate
  `endif // end of inorder proof

  `ifdef TRANSKIDBUF_PIPELINE_SELF
  check_trace: cover property (@(posedge clk)
    disable iff (!rstn)
    (!out_valid && !in_valid)
    ##1 in_valid && out_ready [*3]
    ##1 in_valid && !out_ready [*3]
    ##[1:$] (out_cnt == 'd10)
  );
  `endif
`endif // FORMAL
endmodule