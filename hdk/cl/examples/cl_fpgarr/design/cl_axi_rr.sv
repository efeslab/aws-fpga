`include "cl_fpgarr_types.svh"
`include "cl_fpgarr_defs.svh"

module axi_mstr_recorder (
   input clk,
   input sync_rst_n,
   axi_bus_t.master inS,
   axi_bus_t.slave outM,
   axi_mstr_rec_bus_t.P rec_out
);

// pass through B Channel
assign inS.bid = outM.bid;
assign inS.bresp = outM.bresp;
assign inS.bvalid = outM.bvalid;
assign outM.bready = inS.bready;

// pass through R Channel
assign inS.rid = outM.rid;
assign inS.rdata = outM.rdata;
assign inS.rresp = outM.rresp;
assign inS.rlast = outM.rlast;
assign inS.rvalid = outM.rvalid;
assign outM.rready = inS.rready;

// Channels to record (AW, W, AR)
logic bubble_en;
logic siderec_ready;
logic [2:0] rec_valid;  // 0:AW, 1:W, 2:AR
logic [2:0] new_packet; // 0:AW, 1:W, 2:AR
assign rec_out.valid = &rec_valid;
assign siderec_ready = &rec_valid && rec_out.ready; // FIXME double check
assign bubble_en = |new_packet;

// AW Channel
channel_siderec #(.DEPTH(RECORDER_FIFO_DEPTH), .WIDTH(AXI_RR_AW_WIDTH))
CHANNEL_AW (
   .clk(clk),
   .sync_rst_n(sync_rst_n),
   .din({inS.awid, inS.awaddr, inS.awlen, inS.awsize}),
   .sh_valid(inS.awvalid),
   .cl_ready(outM.awready),
   .bubble_en(bubble_en),
   .ispkt_out(rec_out.hdr.AW.valid),
   .busy_out(rec_out.hdr.AW.busy),
   .dout(rec_out.AW),
   .rec_valid(rec_valid[0]),
   .rec_ready(siderec_ready),
   .sh_ready(inS.awready),
   .new_packet(new_packet[0])
);
assign outM.awid = inS.awid;
assign outM.awaddr = inS.awaddr;
assign outM.awlen = inS.awlen;
assign outM.awsize = inS.awsize;
assign outM.awvalid = inS.awvalid;
// W  Channel
channel_siderec #(.DEPTH(RECORDER_FIFO_DEPTH), .WIDTH(AXI_RR_W_WIDTH))
CHANNEL_W (
   .clk(clk),
   .sync_rst_n(sync_rst_n),
   .din({inS.wid, inS.wdata, inS.wstrb, inS.wlast}),
   .sh_valid(inS.wvalid),
   .cl_ready(outM.wready),
   .bubble_en(bubble_en),
   .ispkt_out(rec_out.hdr.W.valid),
   .busy_out(rec_out.hdr.W.busy),
   .dout(rec_out.W),
   .rec_valid(rec_valid[1]),
   .rec_ready(siderec_ready),
   .sh_ready(inS.wready),
   .new_packet(new_packet[1])
);
assign outM.wid = inS.wid;
assign outM.wdata = inS.wdata;
assign outM.wstrb = inS.wstrb;
assign outM.wlast = inS.wlast;
assign outM.wvalid = inS.wvalid;
// AR Channel
channel_siderec #(.DEPTH(RECORDER_FIFO_DEPTH), .WIDTH(AXI_RR_AR_WIDTH))
CHANNEL_AR (
   .clk(clk),
   .sync_rst_n(sync_rst_n),
   .din({inS.arid, inS.araddr, inS.arlen, inS.arsize}),
   .sh_valid(inS.arvalid),
   .cl_ready(outM.arready),
   .bubble_en(bubble_en),
   .ispkt_out(rec_out.hdr.AR.valid),
   .busy_out(rec_out.hdr.AR.busy),
   .dout(rec_out.AR),
   .rec_valid(rec_valid[2]),
   .rec_ready(siderec_ready),
   .sh_ready(inS.arready),
   .new_packet(new_packet[2])
);
assign outM.arid = inS.arid;
assign outM.araddr = inS.araddr;
assign outM.arlen = inS.arlen;
assign outM.arsize = inS.arsize;
assign outM.arvalid = inS.arvalid;
endmodule

module axi_slv_recorder (
   input clk,
   input sync_rst_n,
   axi_bus_t.slave inM,
   axi_bus_t.master outS,
   axi_slv_rec_bus_t.P rec_out
);
// pass through AW Channel
assign inM.awid = outS.awid;
assign inM.awaddr = outS.awaddr;
assign inM.awlen = outS.awlen;
assign inM.awsize = outS.awsize;
assign inM.awvalid = outS.awvalid;
assign outS.awready = inM.awready;
// pass through W  Channel
assign inM.wid = outS.wid;
assign inM.wdata = outS.wdata;
assign inM.wstrb = outS.wstrb;
assign inM.wlast = outS.wlast;
assign inM.wvalid = outS.wvalid;
assign outS.wready = inM.wready;
// pass through AR Channel
assign inM.arid = outS.arid;
assign inM.araddr = outS.araddr;
assign inM.arlen = outS.arlen;
assign inM.arsize = outS.arsize;
assign inM.arvalid = outS.arvalid;
assign outS.arready = inM.arready;

// Channes to record (B, R)
logic bubble_en;
logic siderec_ready;
logic [1:0] rec_valid;   // 0:B, 1:R
logic [1:0] new_packet;  // 0:B, 1:R
assign rec_out.valid = &rec_valid;

assign siderec_ready = &rec_valid && rec_out.ready; // FIXME double check combinational path validity
assign bubble_en = |new_packet;

// B Channel
channel_siderec #(.DEPTH(RECORDER_FIFO_DEPTH), .WIDTH(AXI_RR_B_WIDTH))
CHANNEL_B (
   .clk(clk),
   .sync_rst_n(sync_rst_n),
   .din({inM.bid, inM.bresp}),
   .sh_valid(inM.bvalid),
   .cl_ready(outS.bready),
   .bubble_en(bubble_en),
   .ispkt_out(rec_out.hdr.B.valid),
   .busy_out(rec_out.hdr.B.busy),
   .dout(rec_out.B),
   .rec_valid(rec_valid[0]),
   .rec_ready(siderec_ready),
   .sh_ready(inM.bready),
   .new_packet(new_packet[0])
);
assign outS.bid = inM.bid;
assign outS.bresp = inM.bresp;
assign outS.bvalid = inM.bvalid;

// R Channel
channel_siderec #(.DEPTH(RECORDER_FIFO_DEPTH), .WIDTH(AXI_RR_R_WIDTH))
CHANNEL_R (
   .clk(clk),
   .sync_rst_n(sync_rst_n),
   .din({inM.rid, inM.rdata, inM.rresp, inM.rlast}),
   .sh_valid(inM.rvalid),
   .cl_ready(outS.rready),
   .bubble_en(bubble_en),
   .ispkt_out(rec_out.hdr.R.valid),
   .busy_out(rec_out.hdr.R.busy),
   .dout(rec_out.R),
   .rec_valid(rec_valid[1]),
   .rec_ready(siderec_ready),
   .sh_ready(inM.rready),
   .new_packet(new_packet[1])
);
assign outS.rid = inM.rid;
assign outS.rdata = inM.rdata;
assign outS.rresp = inM.rresp;
assign outS.rlast = inM.rlast;
assign outS.rvalid = inM.rvalid;
endmodule
