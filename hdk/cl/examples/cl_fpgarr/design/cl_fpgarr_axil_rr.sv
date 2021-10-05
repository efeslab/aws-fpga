`include "cl_fpgarr_types.svh"
`include "cl_fpgarr_defs.svh"

module axil_mstr_recorder (
   input clk,
   input sync_rst_n,
   rr_axi_lite_bus_t.master inS,
   rr_axi_lite_bus_t.slave outM,
   rr_logging_bus_t.P axil_log
);
localparam int LOGB_CHANNEL_CNT = axil_log.LOGB_CHANNEL_CNT;
localparam int LOGE_CHANNEL_CNT = axil_log.LOGE_CHANNEL_CNT;
localparam bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
   CHANNEL_WIDTHS = axil_log.CHANNEL_WIDTHS;
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
   if (LOGE_CHANNEL_CNT != 5)
      $error("Wrong LOGE_CHANNEL_CNT %d\n", LOGE_CHANNEL_CNT);
endgenerate

// AW Channel, inS(shell) => outM(cl)
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_AW_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) AW_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(inS.awvalid),
   .in_ready(inS.awready),
   .in_data(axil_rr_AW_t'{inS.awaddr}),
   .out_valid(outM.awvalid),
   .out_ready(outM.awready),
   .out_data(axil_rr_AW_t'{outM.awaddr}),
   .logb_valid(axil_log.logb_valid[LOGB_AW]),
   .logb_ready(axil_log.ready),
   .logb_data(axil_log.logb_data[GET_OFFSET(LOGB_AW) +: CHANNEL_WIDTHS[LOGB_AW]]),
   .loge_valid(axil_log.loge_valid[LOGE_AW]),
   .loge_ready(axil_log.ready)
);
// W  Channel, inS(shell) => outM(cl)
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_W_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) W_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(inS.wvalid),
   .in_ready(inS.wready),
   .in_data(axil_rr_W_t'{inS.wdata, inS.wstrb}),
   .out_valid(outM.wvalid),
   .out_ready(outM.wready),
   .out_data(axil_rr_W_t'{outM.wdata, outM.wstrb}),
   .logb_valid(axil_log.logb_valid[LOGB_W]),
   .logb_ready(axil_log.ready),
   .logb_data(axil_log.logb_data[GET_OFFSET(LOGB_W) +: CHANNEL_WIDTHS[LOGB_W]]),
   .loge_valid(axil_log.loge_valid[LOGE_W]),
   .loge_ready(axil_log.ready)
);
// AR Channel, inS(shell) => outM(cl)
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_AR_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) AR_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(inS.arvalid),
   .in_ready(inS.arready),
   .in_data(axil_rr_AR_t'{inS.araddr}),
   .out_valid(outM.arvalid),
   .out_ready(outM.arready),
   .out_data(axil_rr_AR_t'{outM.araddr}),
   .logb_valid(axil_log.logb_valid[LOGB_AR]),
   .logb_ready(axil_log.ready),
   .logb_data(axil_log.logb_data[GET_OFFSET(LOGB_AR) +: CHANNEL_WIDTHS[LOGB_AR]]),
   .loge_valid(axil_log.loge_valid[LOGE_AR]),
   .loge_ready(axil_log.ready)
);
// B  Channel, inS(shell) <= outM(cl)
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_B_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) B_logger(
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(outM.bvalid),
   .in_ready(outM.bready),
   .in_data(axil_rr_B_t'{outM.bresp}),
   .out_valid(inS.bvalid),
   .out_ready(inS.bready),
   .out_data(axil_rr_B_t'{inS.bresp}),
   .logb_valid(),
   .logb_ready(axil_log.ready),
   .logb_data(),
   .loge_valid(axil_log.loge_valid[LOGE_B]),
   .loge_ready(axil_log.ready)
);
// R  Channel, inS(shell) <= outM(cl)
axichannel_logger #(
   .DATA_WIDTH(AXIL_RR_R_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) R_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(outM.rvalid),
   .in_ready(outM.rready),
   .in_data(axil_rr_R_t'{outM.rdata, outM.rresp}),
   .out_valid(inS.rvalid),
   .out_ready(inS.rready),
   .out_data(axil_rr_R_t'{inS.rdata, inS.rresp}),
   .logb_valid(),
   .logb_ready(axil_log.ready),
   .logb_data(),
   .loge_valid(axil_log.loge_valid[LOGE_R]),
   .loge_ready(axil_log.ready)
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
   .logb_ready(axil_log.ready),
   .logb_data(),
   .loge_valid(axil_log.loge_valid[LOGE_AW]),
   .loge_ready(axil_log.ready)
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
   .logb_ready(axil_log.ready),
   .logb_data(),
   .loge_valid(axil_log.loge_valid[LOGE_W]),
   .loge_ready(axil_log.ready)
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
   .logb_ready(axil_log.ready),
   .logb_data(),
   .loge_valid(axil_log.loge_valid[LOGE_AR]),
   .loge_ready(axil_log.ready)
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
   .logb_ready(axil_log.ready),
   .logb_data(axil_log.logb_data[GET_OFFSET(LOGB_B) +: CHANNEL_WIDTHS[LOGB_B]]),
   .loge_valid(axil_log.loge_valid[LOGE_B]),
   .loge_ready(axil_log.ready)
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
   .logb_ready(axil_log.ready),
   .logb_data(axil_log.logb_data[GET_OFFSET(LOGB_R) +: CHANNEL_WIDTHS[LOGB_R]]),
   .loge_valid(axil_log.loge_valid[LOGE_R]),
   .loge_ready(axil_log.ready)
);
endmodule
