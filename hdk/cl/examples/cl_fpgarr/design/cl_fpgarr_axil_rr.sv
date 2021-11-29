`include "cl_fpgarr_types.svh"
`include "cl_fpgarr_defs.svh"

// There is no notion of input and outout between master and slave
// axil_recorder will record bi-directional traffic to two separate logging bus
module axil_recorder (
   input clk,
   input sync_rst_n,
   rr_axi_lite_bus_t.master M, // a slave intf drived by an external master
   rr_axi_lite_bus_t.slave S,  // a master intf drived by an external slave
   rr_logging_bus_t.P log_M2S, // AW, W, AR
   rr_logging_bus_t.P log_S2M  // R, B
);
// parameter check (M2S)
localparam int M2S_LOGB_CHANNEL_CNT = log_M2S.LOGB_CHANNEL_CNT;
localparam int M2S_LOGE_CHANNEL_CNT = log_M2S.LOGE_CHANNEL_CNT;
localparam bit [M2S_LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
   M2S_CHANNEL_WIDTHS = log_M2S.CHANNEL_WIDTHS;
`DEF_GET_OFFSET(M2S_GET_OFFSET, M2S_CHANNEL_WIDTHS)
if (M2S_LOGB_CHANNEL_CNT != 3)
   $error("Wrong M2S_LOGB_CHANNEL_CNT %d\n", M2S_LOGB_CHANNEL_CNT);
if (M2S_CHANNEL_WIDTHS[LOGB_AW] != AXIL_RR_AW_WIDTH)
   $error("AW Width mismatches: see %d, expected %d\n",
      M2S_CHANNEL_WIDTHS[LOGB_AW], AXIL_RR_AW_WIDTH);
if (M2S_CHANNEL_WIDTHS[LOGB_W] != AXIL_RR_W_WIDTH)
   $error("W Width mismatches: see %d, expected %d\n",
      M2S_CHANNEL_WIDTHS[LOGB_W], AXIL_RR_W_WIDTH);
if (M2S_CHANNEL_WIDTHS[LOGB_AR] != AXIL_RR_AR_WIDTH)
   $error("AR Width mismatches: see %d, expected %d\n",
      M2S_CHANNEL_WIDTHS[LOGB_AR], AXIL_RR_AR_WIDTH);
if (M2S_LOGE_CHANNEL_CNT != 5)
   $error("Wrong M2S_LOGE_CHANNEL_CNT %d\n", M2S_LOGE_CHANNEL_CNT);
// parmameter check (S2M)
localparam int S2M_LOGB_CHANNEL_CNT = log_S2M.LOGB_CHANNEL_CNT;
localparam int S2M_LOGE_CHANNEL_CNT = log_S2M.LOGE_CHANNEL_CNT;
localparam bit [S2M_LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
   S2M_CHANNEL_WIDTHS = log_S2M.CHANNEL_WIDTHS;
`DEF_GET_OFFSET(S2M_GET_OFFSET, S2M_CHANNEL_WIDTHS)
if (S2M_LOGB_CHANNEL_CNT != 2)
   $error("Wrong S2M_LOGB_CHANNEL_CNT %d\n", S2M_LOGB_CHANNEL_CNT);
if (S2M_CHANNEL_WIDTHS[LOGB_R] != AXIL_RR_R_WIDTH)
   $error("R Width mismatches: see %d, expected %d\n",
      S2M_CHANNEL_WIDTHS[LOGB_R], AXIL_RR_R_WIDTH);
if (S2M_CHANNEL_WIDTHS[LOGB_B] != AXIL_RR_B_WIDTH)
   $error("B Width mismatches: see %d, expected %d\n",
      S2M_CHANNEL_WIDTHS[LOGB_B], AXIL_RR_B_WIDTH);
if (S2M_LOGE_CHANNEL_CNT != 5)
   $error("Wrong S2M_LOGE_CHANNEL_CNT %d\n", S2M_LOGE_CHANNEL_CNT);

// common signals for both log_M2S and log_S2M
logic logb_almful;
assign logb_almful = log_M2S.logb_almful_lo || log_S2M.logb_almful_lo;
logic loge_valid [M2S_LOGE_CHANNEL_CNT-1:0];
assign log_M2S.loge_valid = loge_valid;
assign log_S2M.loge_valid = loge_valid;

// AW Channel, M2S
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_AW_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) AW_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(M.awvalid),
   .in_ready(M.awready),
   .in_data(axil_rr_AW_t'{M.awaddr}),
   .out_valid(S.awvalid),
   .out_ready(S.awready),
   .out_data(axil_rr_AW_t'{S.awaddr}),
   .logb_valid(log_M2S.logb_valid[LOGB_AW]),
   .logb_data(log_M2S.logb_data[
      M2S_GET_OFFSET(LOGB_AW) +: M2S_CHANNEL_WIDTHS[LOGB_AW]
   ]),
   .loge_valid(loge_valid[LOGE_AW]),
   .logb_almful(logb_almful),
   .logb_almful_imme(1'b0)
);
// W  Channel, M2S
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_W_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) W_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(M.wvalid),
   .in_ready(M.wready),
   .in_data(axil_rr_W_t'{M.wdata, M.wstrb}),
   .out_valid(S.wvalid),
   .out_ready(S.wready),
   .out_data(axil_rr_W_t'{S.wdata, S.wstrb}),
   .logb_valid(log_M2S.logb_valid[LOGB_W]),
   .logb_data(log_M2S.logb_data[
      M2S_GET_OFFSET(LOGB_W) +: M2S_CHANNEL_WIDTHS[LOGB_W]
   ]),
   .loge_valid(loge_valid[LOGE_W]),
   .logb_almful(logb_almful),
   .logb_almful_imme(1'b0)
);
// AR Channel, M2S
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_AR_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) AR_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(M.arvalid),
   .in_ready(M.arready),
   .in_data(axil_rr_AR_t'{M.araddr}),
   .out_valid(S.arvalid),
   .out_ready(S.arready),
   .out_data(axil_rr_AR_t'{S.araddr}),
   .logb_valid(log_M2S.logb_valid[LOGB_AR]),
   .logb_data(log_M2S.logb_data[
      M2S_GET_OFFSET(LOGB_AR) +: M2S_CHANNEL_WIDTHS[LOGB_AR]
   ]),
   .loge_valid(loge_valid[LOGE_AR]),
   .logb_almful(logb_almful),
   .logb_almful_imme(1'b0)
);
// B  Channel, S2M
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_B_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) B_logger(
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(S.bvalid),
   .in_ready(S.bready),
   .in_data(axil_rr_B_t'{S.bresp}),
   .out_valid(M.bvalid),
   .out_ready(M.bready),
   .out_data(axil_rr_B_t'{M.bresp}),
   .logb_valid(log_S2M.logb_valid[LOGB_B]),
   .logb_data(log_S2M.logb_data[
      S2M_GET_OFFSET(LOGB_B) +: S2M_CHANNEL_WIDTHS[LOGB_B]
   ]),
   .loge_valid(loge_valid[LOGE_B]),
   .logb_almful(logb_almful),
   .logb_almful_imme(1'b0)
);
// R  Channel, S2M
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_R_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) R_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(S.rvalid),
   .in_ready(S.rready),
   .in_data(axil_rr_R_t'{S.rdata, S.rresp}),
   .out_valid(M.rvalid),
   .out_ready(M.rready),
   .out_data(axil_rr_R_t'{M.rdata, M.rresp}),
   .logb_valid(log_S2M.logb_valid[LOGB_R]),
   .logb_data(log_S2M.logb_data[
      S2M_GET_OFFSET(LOGB_R) +: S2M_CHANNEL_WIDTHS[LOGB_R]
   ]),
   .loge_valid(loge_valid[LOGE_R]),
   .logb_almful(logb_almful),
   .logb_almful_imme(1'b0)
);
endmodule

module axil_slv_recorder (
   input clk,
   input sync_rst_n,
   rr_axi_lite_bus_t.slave inM,
   rr_axi_lite_bus_t.master outS,
   rr_logging_bus_t.P axil_log
);
localparam int LOGB_CHANNEL_CNT = axil_log.LOGB_CHANNEL_CNT;
localparam int LOGE_CHANNEL_CNT = axil_log.LOGE_CHANNEL_CNT;
localparam bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
   CHANNEL_WIDTHS = axil_log.CHANNEL_WIDTHS;
`DEF_GET_OFFSET(GET_OFFSET, CHANNEL_WIDTHS)
// parameter check
generate
   if (LOGB_CHANNEL_CNT != 2)
      $error("Wrong LOGB_CHANNEL_CNT %d\n", LOGB_CHANNEL_CNT);
   if (CHANNEL_WIDTHS[LOGB_R] != AXIL_RR_R_WIDTH)
      $error("R Width mismatches: see %d, expected %d\n",
         CHANNEL_WIDTHS[LOGB_R], AXIL_RR_R_WIDTH);
   if (CHANNEL_WIDTHS[LOGB_B] != AXIL_RR_B_WIDTH)
      $error("B Width mismatches: see %d, expected %d\n",
         CHANNEL_WIDTHS[LOGB_B], AXIL_RR_B_WIDTH);
   if (LOGE_CHANNEL_CNT != 5)
      $error("Wrong LOGE_CHANNEL_CNT %d\n", LOGE_CHANNEL_CNT);
endgenerate
// AW Channel, inM(shell) <= outS(cl)
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_AW_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) AW_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(outS.awvalid),
   .in_ready(outS.awready),
   .in_data(axil_rr_AW_t'{outS.awaddr}),
   .out_valid(inM.awvalid),
   .out_ready(inM.awready),
   .out_data(axil_rr_AW_t'{inM.awaddr}),
   .logb_valid(),
   .logb_data(),
   .loge_valid(axil_log.loge_valid[LOGE_AW]),
   .logb_almful(axil_log.logb_almful)
);
// W  Channel, inM(shell) <= outS(cl)
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_W_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) W_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(outS.wvalid),
   .in_ready(outS.wready),
   .in_data(axil_rr_W_t'{outS.wdata, outS.wstrb}),
   .out_valid(inM.wvalid),
   .out_ready(inM.wready),
   .out_data(axil_rr_W_t'{inM.wdata, inM.wstrb}),
   .logb_valid(),
   .logb_data(),
   .loge_valid(axil_log.loge_valid[LOGE_W]),
   .logb_almful(axil_log.logb_almful)
);
// AR Channel, inM(shell) <= outS(cl)
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_AR_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) AR_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(outS.arvalid),
   .in_ready(outS.arready),
   .in_data(axil_rr_AR_t'{outS.araddr}),
   .out_valid(inM.arvalid),
   .out_ready(inM.arready),
   .out_data(axil_rr_AR_t'{inM.araddr}),
   .logb_valid(),
   .logb_data(),
   .loge_valid(axil_log.loge_valid[LOGE_AR]),
   .logb_almful(axil_log.logb_almful)
);
// B  Channel, inM(shell) => outS(cl)
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_B_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) B_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(inM.bvalid),
   .in_ready(inM.bready),
   .in_data(axil_rr_B_t'{inM.bresp}),
   .out_valid(outS.bvalid),
   .out_ready(outS.bready),
   .out_data(axil_rr_B_t'{outS.bresp}),
   .logb_valid(axil_log.logb_valid[LOGB_B]),
   .logb_data(axil_log.logb_data[GET_OFFSET(LOGB_B) +: CHANNEL_WIDTHS[LOGB_B]]),
   .loge_valid(axil_log.loge_valid[LOGE_B]),
   .logb_almful(axil_log.logb_almful)
);
// R  CHannel, inM(shell) => outS(cl)
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_R_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) R_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(inM.rvalid),
   .in_ready(inM.rready),
   .in_data(axil_rr_R_t'{inM.rdata, inM.rresp}),
   .out_valid(outS.rvalid),
   .out_ready(outS.rready),
   .out_data(axil_rr_R_t'{outS.rdata, outS.rresp}),
   .logb_valid(axil_log.logb_valid[LOGB_R]),
   .logb_data(axil_log.logb_data[GET_OFFSET(LOGB_R) +: CHANNEL_WIDTHS[LOGB_R]]),
   .loge_valid(axil_log.loge_valid[LOGE_R]),
   .logb_almful(axil_log.logb_almful)
);
endmodule

module axil_mstr_replayer #(
   parameter int NUM_INTERFACES,
   parameter int LOGE_PER_AXI,
   parameter int INTF_ID
) (
   input clk,
   input sync_rst_n,
   rr_replay_bus_t.C rbus,
   rr_axi_lite_bus_t.slave outM,
   output logic [LOGE_PER_AXI-1:0] o_rt_loge_valid,
   input logic [NUM_INTERFACES-1:0] [LOGE_PER_AXI-1:0] i_rt_loge_valid,
   output logic fifo_overflow,
   output logic fifo_underflow
);
localparam LOGB_CHANNEL_CNT = rbus.LOGB_CHANNEL_CNT;
localparam [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
   CHANNEL_WIDTHS = rbus.CHANNEL_WIDTHS;
// the LOGE_CHANNEL_CNT here is for all channels from all interfaces
localparam LOGE_CHANNEL_CNT = rbus.LOGE_CHANNEL_CNT;
`DEF_GET_OFFSET(GET_OFFSET, CHANNEL_WIDTHS)

// parameter check
generate
   if (LOGB_CHANNEL_CNT != 3)
      $error("Wrong LOGB_CHANNEL_CNT %d\n", LOGB_CHANNEL_CNT);
   if (CHANNEL_WIDTHS[LOGB_AW] != AXIL_RR_AW_WIDTH)
      $error("AW Width mismatches: see %d, expected %d\n",
         CHANNEL_WIDTHS[LOGB_AW], AXIL_RR_AW_WIDTH);
   if (CHANNEL_WIDTHS[LOGB_W] != AXIL_RR_W_WIDTH)
      $error("W Width mismatches: see %d, expected %d\n",
         CHANNEL_WIDTHS[LOGB_W], AXIL_RR_W_WIDTH);
   if (CHANNEL_WIDTHS[LOGB_AR] != AXIL_RR_AR_WIDTH)
      $error("AR Width mismatches: see %d, expected %d\n",
         CHANNEL_WIDTHS[LOGB_AR], AXIL_RR_AR_WIDTH);
   if (LOGE_PER_AXI != 5)
      $error("Wrong LOGE_PER_AXI %d\n", LOGE_PER_AXI);
   if (LOGE_CHANNEL_CNT != NUM_INTERFACES * LOGE_PER_AXI)
      $error("Wrong LOGE_CHANNEL_CN %d, NUM_INTERFACES %d, LOGE_PER_AXI %d\n",
         LOGE_CHANNEL_CNT, NUM_INTERFACES, LOGE_PER_AXI);
   if (rbus.NUM_AXI_INTF != 1)
      $error("Replay bus wrong NUM_AXI_INTF %d", rbus.NUM_AXI_INTF);
endgenerate

logic rstn;
assign rstn = sync_rst_n;
logic [LOGB_CHANNEL_CNT-1:0] fifo_overflow_ch;
logic rdyrply_fifo_overflow;
assign fifo_overflow = |fifo_overflow_ch | rdyrply_fifo_overflow;
logic [LOGB_CHANNEL_CNT-1:0] fifo_underflow_ch;
logic rdyrply_fifo_underflow;
assign fifo_underflow = |fifo_underflow_ch | rdyrply_fifo_underflow;
// AW Channel
axichannel_valid_replayer #(
   .DATA_WIDTH(AXIL_RR_AW_WIDTH),
   .PIPE_DEPTH(REPLAYER_PIPE_DEPTH),
   .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT)
) AW_replayer (
   .clk(clk), .rstn(rstn),
   .in_valid(rbus.valid[LOGB_AW]),
   .logb_valid(rbus.logb_valid[LOGB_AW]),
   .logb_data(rbus.logb_data[GET_OFFSET(LOGB_AW) +: CHANNEL_WIDTHS[LOGB_AW]]),
   .loge_valid(rbus.loge_valid[LOGB_AW]),
   .in_almful(rbus.almful[LOGB_AW]),
   .rt_loge_valid(i_rt_loge_valid),
   .out_valid(outM.awvalid),
   .out_ready(outM.awready),
   .out_data(axil_rr_AW_t'{outM.awaddr}),
   .fifo_overflow(fifo_overflow_ch[LOGB_AW]),
   .fifo_underflow(fifo_underflow_ch[LOGB_AW])
);
assign o_rt_loge_valid[LOGE_AW] = outM.awvalid && outM.awready;

// W  Channel
axichannel_valid_replayer #(
   .DATA_WIDTH(AXIL_RR_W_WIDTH),
   .PIPE_DEPTH(REPLAYER_PIPE_DEPTH),
   .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT)
) W_replayer (
   .clk(clk), .rstn(rstn),
   .in_valid(rbus.valid[LOGB_W]),
   .logb_valid(rbus.logb_valid[LOGB_W]),
   .logb_data(rbus.logb_data[GET_OFFSET(LOGB_W) +: CHANNEL_WIDTHS[LOGB_W]]),
   .loge_valid(rbus.loge_valid[LOGB_W]),
   .in_almful(rbus.almful[LOGB_W]),
   .rt_loge_valid(i_rt_loge_valid),
   .out_valid(outM.wvalid),
   .out_ready(outM.wready),
   .out_data(axil_rr_W_t'{outM.wdata, outM.wstrb}),
   .fifo_overflow(fifo_overflow_ch[LOGB_W]),
   .fifo_underflow(fifo_underflow_ch[LOGB_W])
);
assign o_rt_loge_valid[LOGE_W] = outM.wvalid && outM.wready;

// AR Channel
axichannel_valid_replayer #(
   .DATA_WIDTH(AXIL_RR_AR_WIDTH),
   .PIPE_DEPTH(REPLAYER_PIPE_DEPTH),
   .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT)
) AR_replayer (
   .clk(clk), .rstn(rstn),
   .in_valid(rbus.valid[LOGB_AR]),
   .logb_valid(rbus.logb_valid[LOGB_AR]),
   .logb_data(rbus.logb_data[GET_OFFSET(LOGB_AR) +: CHANNEL_WIDTHS[LOGB_AR]]),
   .loge_valid(rbus.loge_valid[LOGB_AR]),
   .in_almful(rbus.almful[LOGB_AR]),
   .rt_loge_valid(i_rt_loge_valid),
   .out_valid(outM.arvalid),
   .out_ready(outM.arready),
   .out_data(axil_rr_AR_t'{outM.araddr}),
   .fifo_overflow(fifo_overflow_ch[LOGB_AR]),
   .fifo_underflow(fifo_underflow_ch[LOGB_AR])
);
assign o_rt_loge_valid[LOGE_AR] = outM.arvalid && outM.arready;

// Ready signal replay
// B  Channel
// R  Channel
localparam LOGE_IDX_BASE = INTF_ID * AWSF1_INTF_RRCFG::LOGE_PER_AXI;
axichannel_ready_replayer #(
   .PIPE_DEPTH(REPLAYER_PIPE_DEPTH),
   .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT),
   .NUM_RDYRPLY(2),
   .LOGE_IDX({
      LOGE_IDX_BASE + LOGE_B,
      LOGE_IDX_BASE + LOGE_R
   })
) rdy_replayer (
   .clk(clk), .rstn(rstn),
   .in_valid(rbus.rdyrply_valid[0]),
   .loge_valid(rbus.rdyrply_loge_valid[0]),
   .rt_loge_valid(i_rt_loge_valid),
   .in_almful(rbus.rdyrply_almful[0]),
   .o_ready('{outM.bready, outM.rready}),
   .fifo_overflow(rdyrply_fifo_overflow),
   .fifo_underflow(rdyrply_fifo_underflow)
);
assign o_rt_loge_valid[LOGE_B] = outM.bvalid && outM.bready;
assign o_rt_loge_valid[LOGE_R] = outM.rvalid && outM.rready;
endmodule

module axil_slv_replayer #(
   parameter int NUM_INTERFACES,
   parameter int LOGE_PER_AXI,
   parameter int INTF_ID
) (
   input clk,
   input sync_rst_n,
   rr_replay_bus_t.C rbus,
   rr_axi_lite_bus_t.master outS,
   output logic [LOGE_PER_AXI-1:0] o_rt_loge_valid,
   input logic [NUM_INTERFACES-1:0] [LOGE_PER_AXI-1:0] i_rt_loge_valid,
   output logic fifo_overflow,
   output logic fifo_underflow
);
localparam LOGB_CHANNEL_CNT = rbus.LOGB_CHANNEL_CNT;
localparam [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
   CHANNEL_WIDTHS = rbus.CHANNEL_WIDTHS;
localparam LOGE_CHANNEL_CNT = rbus.LOGE_CHANNEL_CNT;
`DEF_GET_OFFSET(GET_OFFSET, CHANNEL_WIDTHS)

// parameter check
generate
   if (LOGB_CHANNEL_CNT != 2)
      $error("Wrong LOGB_CHANNEL_CNT %d\n", LOGB_CHANNEL_CNT);
   if (CHANNEL_WIDTHS[LOGB_B] != AXIL_RR_B_WIDTH)
      $error("B Width mismatches: see %d, expected %d\n",
         CHANNEL_WIDTHS[LOGB_B], AXIL_RR_B_WIDTH);
   if (CHANNEL_WIDTHS[LOGB_R] != AXIL_RR_R_WIDTH)
      $error("R Width mismatches: see %d, expected %d\n",
         CHANNEL_WIDTHS[LOGB_R], AXIL_RR_R_WIDTH);
   if (LOGE_PER_AXI != 5)
      $error("Wrong LOGE_PER_AXI %d\n", LOGE_PER_AXI);
   if (LOGE_CHANNEL_CNT != NUM_INTERFACES * LOGE_PER_AXI)
      $error("Wrong LOGE_CHANNEL_CN %d, NUM_INTERFACES %d, LOGE_PER_AXI %d\n",
         LOGE_CHANNEL_CNT, NUM_INTERFACES, LOGE_PER_AXI);
   if (rbus.NUM_AXI_INTF != 1)
      $error("Replay bus wrong NUM_AXI_INTF %d", rbus.NUM_AXI_INTF);
endgenerate

logic rstn;
assign rstn = sync_rst_n;
logic [LOGB_CHANNEL_CNT-1:0] fifo_overflow_ch;
logic rdyrply_fifo_overflow;
assign fifo_overflow = |fifo_overflow_ch | rdyrply_fifo_overflow;
logic [LOGB_CHANNEL_CNT-1:0] fifo_underflow_ch;
logic rdyrply_fifo_underflow;
assign fifo_underflow = |fifo_underflow_ch | rdyrply_fifo_underflow;

// Ready signal replay
// AW  Channel
// W  Channel
// AR  Channel
localparam LOGE_IDX_BASE = INTF_ID * AWSF1_INTF_RRCFG::LOGE_PER_AXI;
axichannel_ready_replayer #(
   .PIPE_DEPTH(REPLAYER_PIPE_DEPTH),
   .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT),
   .NUM_RDYRPLY(3),
   .LOGE_IDX({
      LOGE_IDX_BASE + LOGE_AW,
      LOGE_IDX_BASE + LOGE_W,
      LOGE_IDX_BASE + LOGE_AR
   })
) rdy_replayer (
   .clk(clk), .rstn(rstn),
   .in_valid(rbus.rdyrply_valid[0]),
   .loge_valid(rbus.rdyrply_loge_valid[0]),
   .rt_loge_valid(i_rt_loge_valid),
   .in_almful(rbus.rdyrply_almful[0]),
   .o_ready('{outS.awready, outS.wready, outS.arready}),
   .fifo_overflow(rdyrply_fifo_overflow),
   .fifo_underflow(rdyrply_fifo_underflow)
);
assign o_rt_loge_valid[LOGE_AW] = outS.awvalid && outS.awready;
assign o_rt_loge_valid[LOGE_W] = outS.wvalid && outS.wready;
assign o_rt_loge_valid[LOGE_AR] = outS.arvalid && outS.arready;

// B  Channel
axichannel_valid_replayer #(
   .DATA_WIDTH(AXIL_RR_B_WIDTH),
   .PIPE_DEPTH(REPLAYER_PIPE_DEPTH),
   .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT)
) B_replayer (
   .clk(clk), .rstn(rstn),
   .in_valid(rbus.valid[LOGB_B]),
   .logb_valid(rbus.logb_valid[LOGB_B]),
   .logb_data(rbus.logb_data[GET_OFFSET(LOGB_B) +: CHANNEL_WIDTHS[LOGB_B]]),
   .loge_valid(rbus.loge_valid[LOGB_B]),
   .in_almful(rbus.almful[LOGB_B]),
   .rt_loge_valid(i_rt_loge_valid),
   .out_valid(outS.bvalid),
   .out_ready(outS.bready),
   .out_data(axil_rr_B_t'{outS.bresp}),
   .fifo_overflow(fifo_overflow_ch[LOGB_B]),
   .fifo_underflow(fifo_underflow_ch[LOGB_B])
);
assign o_rt_loge_valid[LOGE_B] = outS.bvalid && outS.bready;

// R  Channel
axichannel_valid_replayer #(
   .DATA_WIDTH(AXIL_RR_R_WIDTH),
   .PIPE_DEPTH(REPLAYER_PIPE_DEPTH),
   .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT)
) R_replayer (
   .clk(clk), .rstn(rstn),
   .in_valid(rbus.valid[LOGB_R]),
   .logb_valid(rbus.logb_valid[LOGB_R]),
   .logb_data(rbus.logb_data[GET_OFFSET(LOGB_R) +: CHANNEL_WIDTHS[LOGB_R]]),
   .loge_valid(rbus.loge_valid[LOGB_R]),
   .in_almful(rbus.valid[LOGB_R]),
   .rt_loge_valid(i_rt_loge_valid),
   .out_valid(outS.rvalid),
   .out_ready(outS.rready),
   .out_data(axil_rr_R_t'{outS.rdata, outS.rresp}),
   .fifo_overflow(fifo_overflow_ch[LOGB_R]),
   .fifo_underflow(fifo_underflow_ch[LOGB_R])
);
assign o_rt_loge_valid[LOGE_R] = outS.rvalid && outS.rready;
endmodule
