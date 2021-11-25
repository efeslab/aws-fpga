`include "cl_fpgarr_types.svh"
`include "cl_fpgarr_defs.svh"

// There is no notion of input and outout between master and slave
// axi_recorder will record bi-directional traffic to two separate logging bus
//
// parameter ENABLE_B_BUFFER will add an additional 64-element buffer to the
// B channel. It is useful in PCIM, where CL pcim write will compete with
// logging writeback (for the same sh_pcim write channel). Thus I need to make
// sure that for every AW sent from cl pcim, there will be enough space to hold
// the corresponding response so that the B channel packets won't block the
// interconnect which in turn blocks the writeback --> a deadlock.
// Note that there is no need to add additional buffer to R, since cl pcim read
// does not compete with the logging writeback (i.e. one uses sh pcim read
// channel, the other uses sh pcim write channel).
//
// parameter IS_CL_PCIM:
//     if is 0, then all channels will use logb_almful_lo
//     if is 1, special mechanism will be applied to the PCIM-M channel, which
//         will use logb_almful_hi while others still use logb_almful_lo
module axi_recorder #(
   parameter ENABLE_B_BUFFER = 0,
   parameter IS_CL_PCIM = 0
) (
   input clk,
   input sync_rst_n,
   rr_axi_bus_t.master M,      // a slave intf drived by an external master
   rr_axi_bus_t.slave S,       // a master intf drived by an external slave
   rr_logging_bus_t.P log_M2S, // AW, W, AR
   rr_logging_bus_t.P log_S2M, // R, B
   output logic [ENABLE_B_BUFFER-1:0] B_fifo_almful,
   output logic [ENABLE_B_BUFFER-1:0] B_fifo_overflow,
   output logic [ENABLE_B_BUFFER-1:0] B_fifo_underflow
);
// parameter check (M2S)
localparam int M2S_LOGB_CHANNEL_CNT = log_M2S.LOGB_CHANNEL_CNT;
localparam int M2S_LOGE_CHANNEL_CNT = log_M2S.LOGE_CHANNEL_CNT;
localparam bit [M2S_LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
   M2S_CHANNEL_WIDTHS = log_M2S.CHANNEL_WIDTHS;
`DEF_GET_OFFSET(M2S_GET_OFFSET, M2S_CHANNEL_WIDTHS)
if (M2S_LOGB_CHANNEL_CNT != 3)
   $error("Wrong M2S_LOGB_CHANNEL_CNT %d\n", M2S_LOGB_CHANNEL_CNT);
if (M2S_CHANNEL_WIDTHS[LOGB_AW] != AXI_RR_AW_WIDTH)
   $error("AW Width mismatches: see %d, expected %d\n",
      M2S_CHANNEL_WIDTHS[LOGB_AW], AXI_RR_AW_WIDTH);
if (M2S_CHANNEL_WIDTHS[LOGB_W] != AXI_RR_W_WIDTH)
   $error("W Width mismatches: see %d, expected %d\n",
      M2S_CHANNEL_WIDTHS[LOGB_W], AXI_RR_W_WIDTH);
if (M2S_CHANNEL_WIDTHS[LOGB_AR] != AXI_RR_AR_WIDTH)
   $error("AR Width mismatches: see %d, expected %d\n",
      M2S_CHANNEL_WIDTHS[LOGB_AR], AXI_RR_AR_WIDTH);
if (M2S_LOGE_CHANNEL_CNT != 5)
   $error("Wrong M2S_LOGE_CHANNEL_CNT %d\n", M2S_LOGE_CHANNEL_CNT);
// parameter check (S2M)
localparam int S2M_LOGB_CHANNEL_CNT = log_S2M.LOGB_CHANNEL_CNT;
localparam int S2M_LOGE_CHANNEL_CNT = log_S2M.LOGE_CHANNEL_CNT;
localparam bit [S2M_LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
   S2M_CHANNEL_WIDTHS = log_S2M.CHANNEL_WIDTHS;
`DEF_GET_OFFSET(S2M_GET_OFFSET, S2M_CHANNEL_WIDTHS)
if (S2M_LOGB_CHANNEL_CNT != 2)
   $error("Wrong S2M_LOGB_CHANNEL_CNT %d\n", S2M_LOGB_CHANNEL_CNT);
if (S2M_CHANNEL_WIDTHS[LOGB_R] != AXI_RR_R_WIDTH)
   $error("R Width mismatches: see %d, expected %d\n",
      S2M_CHANNEL_WIDTHS[LOGB_R], AXI_RR_R_WIDTH);
if (S2M_CHANNEL_WIDTHS[LOGB_B] != AXI_RR_B_WIDTH)
   $error("B Width mismatches: see %d, expected %d\n",
      S2M_CHANNEL_WIDTHS[LOGB_B], AXI_RR_B_WIDTH);
if (S2M_LOGE_CHANNEL_CNT != 5)
   $error("Wrong S2M_LOGE_CHANNEL_CNT %d\n", S2M_LOGE_CHANNEL_CNT);

// common signals for both log_M2S and log_S2M
// logb_almful is shared across both M2S logging and S2M logging because the
// loge_valid is shared (single source, which is from all channels)
logic nonW_logb_almful;
assign nonW_logb_almful = log_M2S.logb_almful_lo || log_S2M.logb_almful_lo;

logic W_logb_almful;
if (IS_CL_PCIM)
   assign W_logb_almful = log_M2S.logb_almful_hi || log_S2M.logb_almful_hi;
else
   assign W_logb_almful = nonW_logb_almful;

logic loge_valid [M2S_LOGE_CHANNEL_CNT-1:0];
assign log_M2S.loge_valid = loge_valid;
assign log_S2M.loge_valid = loge_valid;
// B_buf_almful is for the ENABLE_B_BUFFER
logic B_buf_almful;

// AW Channel, M2S
axichannel_logger #(
   .DATA_WIDTH(AXI_RR_AW_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) AW_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(M.awvalid),
   .in_ready(M.awready),
   .in_data(axi_rr_AW_t'{M.awid, M.awaddr, M.awlen, M.awsize}),
   .out_valid(S.awvalid),
   .out_ready(S.awready),
   .out_data(axi_rr_AW_t'{S.awid, S.awaddr, S.awlen, S.awsize}),
   .logb_valid(log_M2S.logb_valid[LOGB_AW]),
   .logb_data(log_M2S.logb_data[
      M2S_GET_OFFSET(LOGB_AW) +: M2S_CHANNEL_WIDTHS[LOGB_AW]
   ]),
   .loge_valid(loge_valid[LOGE_AW]),
   .logb_almful(nonW_logb_almful),
   .logb_almful_imme(B_buf_almful)
);
// W  Channel, M2S
axichannel_logger #(
   .DATA_WIDTH(AXI_RR_W_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) W_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(M.wvalid),
   .in_ready(M.wready),
   .in_data(axi_rr_W_t'{M.wid, M.wdata, M.wstrb, M.wlast}),
   .out_valid(S.wvalid),
   .out_ready(S.wready),
   .out_data(axi_rr_W_t'{S.wid, S.wdata, S.wstrb, S.wlast}),
   .logb_valid(log_M2S.logb_valid[LOGB_W]),
   .logb_data(log_M2S.logb_data[
      M2S_GET_OFFSET(LOGB_W) +: M2S_CHANNEL_WIDTHS[LOGB_W]
   ]),
   .loge_valid(loge_valid[LOGE_W]),
   .logb_almful(W_logb_almful),
   .logb_almful_imme(B_buf_almful)
);
// AR Channel, M2S
axichannel_logger #(
   .DATA_WIDTH(AXI_RR_AR_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) AR_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(M.arvalid),
   .in_ready(M.arready),
   .in_data(axi_rr_AR_t'{M.arid, M.araddr, M.arlen, M.arsize}),
   .out_valid(S.arvalid),
   .out_ready(S.arready),
   .out_data(axi_rr_AR_t'{S.arid, S.araddr, S.arlen, S.arsize}),
   .logb_valid(log_M2S.logb_valid[LOGB_AR]),
   .logb_data(log_M2S.logb_data[
      M2S_GET_OFFSET(LOGB_AR) +: M2S_CHANNEL_WIDTHS[LOGB_AR]
   ]),
   .loge_valid(loge_valid[LOGE_AR]),
   .logb_almful(nonW_logb_almful),
   .logb_almful_imme(B_buf_almful)
);

// B  Channel, S2M
logic S_bvalid;
logic S_bready;
logic [$bits(S.bid)-1:0] S_bid;
logic [$bits(S.bresp)-1:0] S_bresp;
if (ENABLE_B_BUFFER) begin : enable_B_buffer
   localparam B_BUF_SIZE = 64;
   logic fifo_full;
   xpm_fifo_sync_wrapper #(
      .WIDTH(AXI_RR_B_WIDTH),
      .DEPTH(B_BUF_SIZE),
      // 4 is a random number for overprovision
      .ALMFUL_HI_THRESHOLD(B_BUF_SIZE - MAX_WR_BURSTS - 4)
   ) B_fifo_buf (
      .clk(clk), .rst(!sync_rst_n),
      .din(axi_rr_B_t'{S.bid, S.bresp}),
      .wr_en(S.bvalid && S.bready),
      .dout(axi_rr_B_t'{S_bid, S_bresp}),
      .rd_en(S_bvalid && S_bready),
      .dout_valid(S_bvalid),
      .full(fifo_full),
      .almful_hi(B_buf_almful),
      .almful_lo(/*not used*/),
      .empty(),
      .overflow(B_fifo_overflow),
      .underflow(B_fifo_underflow)
   );
   assign S.bready = !fifo_full;
   assign B_fifo_almful = B_buf_almful;
end
else begin : no_B_buffer
   assign S_bvalid = S.bvalid;
   assign S.bready = S_bready;
   assign S_bid = S.bid;
   assign S_bresp = S.bresp;
   assign B_buf_almful = 1'b0;
end
axichannel_logger #(
   .DATA_WIDTH(AXI_RR_B_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) B_logger(
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(S_bvalid),
   .in_ready(S_bready),
   .in_data(axi_rr_B_t'{S_bid, S_bresp}),
   .out_valid(M.bvalid),
   .out_ready(M.bready),
   .out_data(axi_rr_B_t'{M.bid, M.bresp}),
   .logb_valid(log_S2M.logb_valid[LOGB_B]),
   .logb_data(log_S2M.logb_data[
      S2M_GET_OFFSET(LOGB_B) +: S2M_CHANNEL_WIDTHS[LOGB_B]
   ]),
   .loge_valid(loge_valid[LOGE_B]),
   .logb_almful(nonW_logb_almful),
   .logb_almful_imme(1'b0)
);
// R  Channel, S2M
axichannel_logger #(
   .DATA_WIDTH(AXI_RR_R_WIDTH),
   .PIPE_DEPTH(RECORDER_PIPE_DEPTH)
) R_logger (
   .clk(clk),
   .rstn(sync_rst_n),
   .in_valid(S.rvalid),
   .in_ready(S.rready),
   .in_data(axi_rr_R_t'{S.rid, S.rdata, S.rresp, S.rlast}),
   .out_valid(M.rvalid),
   .out_ready(M.rready),
   .out_data(axi_rr_R_t'{M.rid, M.rdata, M.rresp, M.rlast}),
   .logb_valid(log_S2M.logb_valid[LOGB_R]),
   .logb_data(log_S2M.logb_data[
      S2M_GET_OFFSET(LOGB_R) +: S2M_CHANNEL_WIDTHS[LOGB_R]
   ]),
   .loge_valid(loge_valid[LOGE_R]),
   .logb_almful(nonW_logb_almful),
   .logb_almful_imme(1'b0)
);
endmodule

module axi_mstr_replayer #(
   parameter int NUM_INTERFACES
) (
   input clk,
   input sync_rst_n,
   rr_replay_bus_t.C rbus,
   rr_axi_bus_t.slave outM,
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
   if (CHANNEL_WIDTHS[LOGB_AW] != AXI_RR_AW_WIDTH)
      $error("AW Width mismatches: see %d, expected %d\n",
         CHANNEL_WIDTHS[LOGB_AW], AXI_RR_AW_WIDTH);
   if (CHANNEL_WIDTHS[LOGB_W] != AXI_RR_W_WIDTH)
      $error("W Width mismatches: see %d, expected %d\n",
         CHANNEL_WIDTHS[LOGB_W], AXI_RR_W_WIDTH);
   if (CHANNEL_WIDTHS[LOGB_AR] != AXI_RR_AR_WIDTH)
      $error("AR Width mismatches: see %d, expected %d\n",
         CHANNEL_WIDTHS[LOGB_AR], AXI_RR_AR_WIDTH);
   if (LOGE_PER_AXI != 5)
      $error("Wrong LOGE_PER_AXI %d\n", LOGE_PER_AXI);
   if (LOGE_CHANNEL_CNT != NUM_INTERFACES * LOGE_PER_AXI)
      $error("Wrong LOGE_CHANNEL_CN %d, NUM_INTERFACES %d, LOGE_PER_AXI %d\n",
         LOGE_CHANNEL_CNT, NUM_INTERFACES, LOGE_PER_AXI);
endgenerate

logic rstn;
assign rstn = sync_rst_n;
logic [LOGB_CHANNEL_CNT-1:0] fifo_overflow_ch;
assign fifo_overflow = |fifo_overflow_ch;
logic [LOGB_CHANNEL_CNT-1:0] fifo_underflow_ch;
assign fifo_underflow = |fifo_underflow_ch;
// AW Channel
axichannel_replayer #(
   .DATA_WIDTH(AXI_RR_AW_WIDTH),
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
   .out_data(axi_rr_AW_t'{outM.awid, outM.awaddr, outM.awlen, outM.awsize}),
   .fifo_overflow(fifo_overflow_ch[LOGB_AW]),
   .fifo_underflow(fifo_underflow_ch[LOGB_AW])
);
assign o_rt_loge_valid[LOGE_AW] = outM.awvalid && outM.awready;

// W  Channel
axichannel_replayer #(
   .DATA_WIDTH(AXI_RR_W_WIDTH),
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
   .out_data(axi_rr_W_t'{outM.wid, outM.wdata, outM.wstrb, outM.wlast}),
   .fifo_overflow(fifo_overflow_ch[LOGB_W]),
   .fifo_underflow(fifo_underflow_ch[LOGB_W])
);
assign o_rt_loge_valid[LOGE_W] = outM.wvalid && outM.wready;

// AR Channel
axichannel_replayer #(
   .DATA_WIDTH(AXI_RR_AR_WIDTH),
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
   .out_data(axi_rr_AR_t'{outM.arid, outM.araddr, outM.arlen, outM.arsize}),
   .fifo_overflow(fifo_overflow_ch[LOGB_AR]),
   .fifo_underflow(fifo_underflow_ch[LOGB_AR])
);
assign o_rt_loge_valid[LOGE_AR] = outM.arvalid && outM.arready;

// ignore slave response during master replay
// B  Channel
assign outM.bready = 1;
assign o_rt_loge_valid[LOGE_B] = outM.bvalid && outM.bready;
// R  Channel
assign outM.rready = 1;
assign o_rt_loge_valid[LOGE_R] = outM.rvalid && outM.rready;
endmodule

module axi_slv_replayer #(
   parameter int NUM_INTERFACES
) (
   input clk,
   input sync_rst_n,
   rr_replay_bus_t.C rbus,
   rr_axi_bus_t.master outS,
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
   if (CHANNEL_WIDTHS[LOGB_B] != AXI_RR_B_WIDTH)
      $error("B Width mismatches: see %d, expected %d\n",
         CHANNEL_WIDTHS[LOGB_B], AXI_RR_B_WIDTH);
   if (CHANNEL_WIDTHS[LOGB_R] != AXI_RR_R_WIDTH)
      $error("R Width mismatches: see %d, expected %d\n",
         CHANNEL_WIDTHS[LOGB_R], AXI_RR_R_WIDTH);
   if (LOGE_PER_AXI != 5)
      $error("Wrong LOGE_PER_AXI %d\n", LOGE_PER_AXI);
   if (LOGE_CHANNEL_CNT != NUM_INTERFACES * LOGE_PER_AXI)
      $error("Wrong LOGE_CHANNEL_CN %d, NUM_INTERFACES %d, LOGE_PER_AXI %d\n",
         LOGE_CHANNEL_CNT, NUM_INTERFACES, LOGE_PER_AXI);
endgenerate
logic rstn;
assign rstn = sync_rst_n;
logic [LOGB_CHANNEL_CNT-1:0] fifo_overflow_ch;
assign fifo_overflow = |fifo_overflow_ch;
logic [LOGB_CHANNEL_CNT-1:0] fifo_underflow_ch;
assign fifo_underflow = |fifo_underflow_ch;
// AW Channel
assign outS.awready = 1;
assign o_rt_loge_valid[LOGE_AW] = outS.awvalid && outS.awready;
// W  Channel
assign outS.wready = 1;
assign o_rt_loge_valid[LOGE_W] = outS.wvalid && outS.wready;
// AR Channel
assign outS.arready = 1;
assign o_rt_loge_valid[LOGE_AR] = outS.arvalid && outS.arready;

// B  Channel
axichannel_replayer #(
   .DATA_WIDTH(AXI_RR_B_WIDTH),
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
   .out_data(axi_rr_B_t'{outS.bid, outS.bresp}),
   .fifo_overflow(fifo_overflow_ch[LOGB_B]),
   .fifo_underflow(fifo_underflow_ch[LOGB_B])
);
assign o_rt_loge_valid[LOGE_B] = outS.bvalid && outS.bready;

// R  Channel
axichannel_replayer #(
   .DATA_WIDTH(AXI_RR_R_WIDTH),
   .PIPE_DEPTH(REPLAYER_PIPE_DEPTH),
   .LOGE_CHANNEL_CNT(LOGE_CHANNEL_CNT)
) R_replayer (
   .clk(clk), .rstn(rstn),
   .in_valid(rbus.valid[LOGB_R]),
   .logb_valid(rbus.logb_valid[LOGB_R]),
   .logb_data(rbus.logb_data[GET_OFFSET(LOGB_R) +: CHANNEL_WIDTHS[LOGB_R]]),
   .loge_valid(rbus.loge_valid[LOGB_R]),
   .in_almful(rbus.almful[LOGB_R]),
   .rt_loge_valid(i_rt_loge_valid),
   .out_valid(outS.rvalid),
   .out_ready(outS.rready),
   .out_data(axi_rr_R_t'{outS.rid, outS.rdata, outS.rresp, outS.rlast}),
   .fifo_overflow(fifo_overflow_ch[LOGB_R]),
   .fifo_underflow(fifo_underflow_ch[LOGB_R])
);
assign o_rt_loge_valid[LOGE_R] = outS.rvalid && outS.rready;
endmodule
