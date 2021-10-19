`include "cl_fpgarr_defs.svh"

// There should be a single storage backend module.
// It is configured via an AXI Lite bus.
// It interacts with the storage backend via an AXI bus
// It may consume logging data in the record mode, or producing logging data in
// the replay mode. In both mode, it uses the rr_stream_bus_t interface.
// This module is offloaded to mjc to implement
// The parameter CHANNEL_WIDTHS is the original one instead of the shuffled one
module rr_storage_backend_axi #(
  parameter int LOGB_CHANNEL_CNT,
  parameter bit [LOGB_CHANNEL_CNT-1:0]
    [RR_CHANNEL_WIDTH_BITS-1:0] CHANNEL_WIDTHS,
  parameter int LOGE_CHANNEL_CNT
) (
  input wire clk,
  input wire rstn,
  rr_axi_bus_t.slave storage_backend_bus,
  rr_stream_bus_t.C record_bus,
  rr_stream_bus_t.P replay_bus,
  input storage_axi_csr_t csr
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
// The SHUFFLE_PLAN is used here to reorder CHANNEL_WIDTHS
function automatic bit [LOGB_CHANNEL_CNT-1:0]
  [RR_CHANNEL_WIDTH_BITS-1:0] GET_SHUFFLED_CHANNEL_WIDTHS();
  for (int i=0; i < LOGB_CHANNEL_CNT; i=i+1) begin
    GET_SHUFFLED_CHANNEL_WIDTHS[i] = CHANNEL_WIDTHS[SHUFFLE_PLAN[i][0]];
  end
endfunction
localparam bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
  SHUFFLED_CHANNEL_WIDTHS = GET_SHUFFLED_CHANNEL_WIDTHS();
function automatic [OFFSET_WIDTH-1:0] GET_LEN
  (logic [FULL_WIDTH-1:0] packed_data);
  logic [LOGB_CHANNEL_CNT-1:0] logb_bitmap;
  logb_bitmap = packed_data[LOGB_CHANNEL_CNT-1:0];
  GET_LEN = LOGB_CHANNEL_CNT + LOGE_CHANNEL_CNT;
  for (int i=0; i < LOGB_CHANNEL_CNT; i=i+1)
    if (logb_bitmap[i])
      GET_LEN += OFFSET_WIDTH'(SHUFFLED_CHANNEL_WIDTHS[i]);
endfunction

// parameter check
generate
  if (FULL_WIDTH != record_bus.FULL_WIDTH)
    $error("FULL_WIDTH mismatches: from parameter %d, record_bus %d\n",
      FULL_WIDTH, record_bus.FULL_WIDTH);
  if (FULL_WIDTH != replay_bus.FULL_WIDTH)
    $error("FULL_WIDTH mismatches: from parameter %d, replay_bus %d\n",
      FULL_WIDTH, replay_bus.FULL_WIDTH);
endgenerate

rr_writeback #(
  .WIDTH(record_bus.FULL_WIDTH),
  .AXI_WIDTH(512),
  .OFFSET_WIDTH(16),
  .AXI_ADDR_WIDTH(64),
  .LOGB_CHANNEL_CNT(LOGB_CHANNEL_CNT),
  .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT),
  .CHANNEL_WIDTHS(CHANNEL_WIDTHS)
) writeback (
  .clk(clk),
  .sync_rst_n(rstn),
  .cfg_max_payload(0),
  .record_din_valid(record_bus.valid),
  .record_din_ready(record_bus.ready),
  .record_finish(record_force_finish),
  .record_din(record_bus.data),
  .record_din_width(record_bus.len),
  .axi_out(storage_backend_bus),
  .write_buf_addr(csr.write_buf_addr),
  .write_buf_size(csr.write_buf_size),
  .write_buf_update(csr.write_buf_update),
  .read_buf_addr(csr.write_buf_addr),
  .read_buf_size(csr.write_buf_size),
  .read_buf_update(csr.write_buf_update),
  .write_interrupt(),
  .read_interrupt()
);

`ifdef WRITEBACK_DEBUG
always_ff @(posedge clk) begin
    if (record_bus.valid & record_bus.ready)
        $display("[record_bus]: width\t%d\tcalculated width\t%d\tdata\t%x", record_bus.len, GET_LEN(record_bus.data), record_bus.data);
end
`endif

// demo use of GET_LEN
logic [OFFSET_WIDTH-1:0] replay_data_len;
assign replay_data_len = GET_LEN(replay_bus.data);

// suggest:
// Should use this bram fifo lib to instantiate big buffer for interacting with
// PCIM. And only have one instance and dynamically configure it to be used in
// either record or replay.
// "hdk/cl/examples/cl_sde/lib/ram_fifo_ft.sv"

endmodule
