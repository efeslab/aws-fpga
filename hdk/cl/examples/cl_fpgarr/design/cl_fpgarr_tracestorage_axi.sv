`include "cl_fpgarr_defs.svh"

// There should be a single storage backend module.
// It is configured via an AXI Lite bus.
// It interacts with the storage backend via an AXI bus
// It may consume logging data in the record mode, or producing logging data in
// the replay mode. In both mode, it uses the rr_stream_bus_t interface.
// This module is offloaded to mjc to implement
module rr_storage_backend_axi #(
  parameter int LOGB_CHANNEL_CNT,
  parameter bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0] CHANNEL_WIDTHS,
  parameter int LOGE_CHANNEL_CNT
) (
  input wire clk,
  input wire rstn,
  rr_axi_lite_bus_t.master rr_cfg_bus,
  rr_axi_bus_t.slave storage_backend_bus,
  rr_stream_bus_t.C record_bus,
  rr_stream_bus_t.P replay_bus
);

// rr_steam_bus_t, packed data structure, LSB to MSB:
// logb_valid, loge_valid, packed_logb_data
function automatic int GET_FULL_WIDTH;
   GET_FULL_WIDTH = 0;
   for (int i=0; i < LOGB_CHANNEL_CNT; ++i)
      GET_FULL_WIDTH += CHANNEL_WIDTHS[i];
   GET_FULL_WIDTH += LOGB_CHANNEL_CNT;
   GET_FULL_WIDTH += LOGE_CHANNEL_CNT;
endfunction
localparam FULL_WIDTH = GET_FULL_WIDTH();
localparam OFFSET_WIDTH = $clog2(FULL_WIDTH+1);
// To parse one logging unit at a time from the backend storage, here is an
// helper function to tell how long a logging unit is.
// This function decodes the valid bitmap of logb_valid and aims to finish
// LOGB_CHANNEL_CNT constant additions in a cycle.
function automatic [OFFSET_WIDTH-1:0] GET_LEN
  (logic [FULL_WIDTH-1:0] packed_data);
  logic [LOGB_CHANNEL_CNT-1:0] logb_bitmap;
  logb_bitmap = packed_data[LOGB_CHANNEL_CNT-1:0];
  GET_LEN = LOGB_CHANNEL_CNT + LOGE_CHANNEL_CNT;
  for (int i=0; i < LOGB_CHANNEL_CNT; i=i+1)
    if (logb_bitmap[i])
      GET_LEN += OFFSET_WIDTH'(CHANNEL_WIDTHS[i]);
endfunction

// parameter check
generate
  if (FULL_WIDTH != record_bus.FULL_WIDTH)
    $error("FULL_WIDTH mismatches: from parameter %d, record_bus %d\n", FULL_WIDTH, record_bus.FULL_WIDTH);
  if (FULL_WIDTH != replay_bus.FULL_WIDTH)
    $error("FULL_WIDTH mismatches: from parameter %d, replay_bus %d\n", FULL_WIDTH, replay_bus.FULL_WIDTH);
endgenerate

// TODO
// placeholder for rr_cfg_bus
assign rr_cfg_bus.awready = 1'b1;
assign rr_cfg_bus.wready = 1'b1;
assign rr_cfg_bus.arready = 1'b1;
assign rr_cfg_bus.rvalid = 1'b1;
assign rr_cfg_bus.rdata = 32'b0;
assign rr_cfg_bus.rresp = 2'b0; // OKAY
assign rr_cfg_bus.bvalid = 1'b1;
assign rr_cfg_bus.bresp = 2'b0; // OKAY
// placeholder for storage_backend_bus
assign storage_backend_bus.awvalid = 1'b0;
assign storage_backend_bus.wvalid = 1'b0;
assign storage_backend_bus.arvalid = 1'b0;
assign storage_backend_bus.rready = 1'b1;
assign storage_backend_bus.bready = 1'b1;
// placeholder for record and replay
assign record_bus.ready = 1'b1;
assign replay_bus.valid = 1'b0;

// demo use of GET_LEN
logic [OFFSET_WIDTH-1:0] replay_data_len;
assign replay_data_len = GET_LEN(replay_bus.data);

endmodule
