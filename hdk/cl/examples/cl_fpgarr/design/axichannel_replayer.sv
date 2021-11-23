`include "cl_fpgarr_defs.svh"
`include "cl_fpgarr_packing_cfg.svh"

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
  output wire in_almful,
  input wire [LOGE_CHANNEL_CNT-1:0] rt_loge_valid,
  output wire out_valid,
  input wire out_ready,
  output wire [DATA_WIDTH-1:0] out_data,
  output logic fifo_overflow,
  output logic fifo_underflow
);

// Illustration
//
//         rt_loge_valid
//               |
//               ˅
//   <------  -----------  valid  -------  almful  ------  almful   ---------
//  replayed | twoway    | <---- | FIFO  | -----> | reg  | ------> |         |
//     AXI   | handshake |       |   +   |        | pipe |         | decoder |
//   ------> | replayer  | ----> | almful| <----- | line | <------ |  tree   |
//            -----------  ready  -------   in_x   ------   in_x    ---------
// The XXX_p version are the signals on the replayer-side of the register
// pipeline
// The input (part of a rr_replay_bus) goes into the pipeline
logic in_valid_p;
logic logb_valid_p;
logic [DATA_WIDTH-1:0] logb_data_p;
logic [LOGE_CHANNEL_CNT-1:0] loge_valid_p;
logic in_almful_p;
// The XXX_f version are the signals coming out of the fifo
logic in_valid_f, in_ready_f;
logic logb_valid_f;
logic [DATA_WIDTH-1:0] logb_data_f;
logic [LOGE_CHANNEL_CNT-1:0] loge_valid_f;

// FIFO configuration
// 2 is a random value chosen to overprovision some resouce and avoid fifo
// overflow
localparam REPLAYER_FIFO_ALMFUL_THRESHOLD =
  2*REPLAYER_PIPE_DEPTH +
  2*(record_pkg::MERGE_TREE_HEIGHT - 1 + MERGETREE_OUT_QUEUE_NSTAGES) +
  2;
$info("Replayer FIFO config: in total %d entries, threshold is %d entries left\n",
  REPLAY_FIFO_DEPTH, REPLAYER_FIFO_ALMFUL_THRESHOLD);
xpm_fifo_sync_wrapper #(
  .WIDTH(1 + LOGE_CHANNEL_CNT + DATA_WIDTH),
  .DEPTH(REPLAY_FIFO_DEPTH),
  .ALMFUL_THRESHOLD(REPLAY_FIFO_DEPTH - REPLAYER_FIFO_ALMFUL_THRESHOLD)
) xpm_fifo_inst (
  .clk(clk), .rst(!rstn),
  .din({logb_data_p, loge_valid_p, logb_valid_p}),
  .wr_en(in_valid_p),
  .dout({logb_data_f, loge_valid_f, logb_valid_f}),
  .rd_en(in_valid_f && in_ready_f),
  .full(),
  .almful(in_almful_p),
  .dout_valid(in_valid_f),
  .empty(),
  .overflow(fifo_overflow),
  .underflow(fifo_underflow)
);

twowayhandshake_replayer #(
  .DATA_WIDTH(DATA_WIDTH),
  .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT)
) replayer (
  .clk(clk), .rstn(rstn),
  .in_valid(in_valid_f),
  .logb_valid(logb_valid_f),
  .logb_data(logb_data_f),
  .loge_valid(loge_valid_f),
  .in_ready(in_ready_f),
  .rt_loge_valid(rt_loge_valid),
  .out_valid(out_valid),
  .out_ready(out_ready),
  .out_data(out_data)
  );

// register pipeline
lib_pipe #(
  .WIDTH(1), .STAGES(PIPE_DEPTH)
) in_valid_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(in_valid), .out_bus(in_valid_p)
);

lib_pipe #(
  .WIDTH(1), .STAGES(PIPE_DEPTH)
) logb_valid_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(logb_valid), .out_bus(logb_valid_p)
);

lib_pipe #(
  .WIDTH(LOGE_CHANNEL_CNT), .STAGES(PIPE_DEPTH)
) loge_valid_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(loge_valid), .out_bus(loge_valid_p)
);

lib_pipe #(
  .WIDTH(DATA_WIDTH), .STAGES(PIPE_DEPTH)
) logb_data_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(logb_data), .out_bus(logb_data_p)
);
// for in_almful
lib_pipe #(
  .WIDTH(1), .STAGES(PIPE_DEPTH)
) almful_pipe (
  .clk(clk), .rst_n(rstn),
  .in_bus(in_almful_p),
  .out_bus(in_almful)
);
endmodule
