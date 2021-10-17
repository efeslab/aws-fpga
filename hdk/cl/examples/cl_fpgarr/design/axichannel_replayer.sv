// This is to use skidbuffer pipeline to transmit replay data to individual
// replayer
module axichannel_replayer #(
  parameter DATA_WIDTH,
  parameter PIPE_DEPTH,
  parameter LOGE_CHANNEL_CNT
) (
  input wire clk,
  input wire rstn,
  // the replay bus
  input wire in_valid,
  input wire logb_valid,
  input wire [DATA_WIDTH-1:0] logb_data,
  input wire [LOGE_CHANNEL_CNT-1:0] loge_valid,
  output wire in_ready,
  input wire [LOGE_CHANNEL_CNT-1:0] rt_loge_valid,
  output wire out_valid,
  input wire out_ready,
  output wire [DATA_WIDTH-1:0] out_data
);

// the input (part of a rr_replay_bus) goes into the skidbuffer pipeline, the
// output of the pipeline (XXX_pipe) goes to the twowayhandshake_replayer
logic valid_pipe, ready_pipe;
logic logb_valid_pipe;
logic [DATA_WIDTH-1:0] logb_data_pipe;
logic [LOGE_CHANNEL_CNT-1:0] loge_valid_pipe;
transkidbuf_pipeline #(
  .DATA_WIDTH(1 + DATA_WIDTH + LOGE_CHANNEL_CNT),
  .PIPE_DEPTH(PIPE_DEPTH),
  .PASS_LAST_STALL(0)
) replay_sbuf_pipe (
  .clk(clk), .rstn(rstn),
  .in_valid(in_valid),
  .in_ready(in_ready),
  .in_data({loge_valid, logb_data, logb_valid}),
  .out_valid(valid_pipe),
  .out_ready(ready_pipe),
  .out_data({loge_valid_pipe, logb_data_pipe, logb_valid_pipe})
);

twowayhandshake_replayer #(
  .DATA_WIDTH(DATA_WIDTH),
  .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT)
) replayer (
  .clk(clk), .rstn(rstn),
  .in_valid(valid_pipe), // TODO
  .logb_valid(logb_valid_pipe),
  .logb_data(logb_data_pipe),
  .loge_valid(loge_valid_pipe),
  .in_ready(ready_pipe),
  .rt_loge_valid(rt_loge_valid),
  .out_valid(out_valid),
  .out_ready(out_ready),
  .out_data(out_data)
  );
endmodule
