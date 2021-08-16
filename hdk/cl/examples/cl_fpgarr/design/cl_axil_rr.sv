`include "cl_fpgarr_types.svh"

module axil_mstr_recorder (
   input clk,
   input sync_rst_n,
   axi_lite_bus_t.master inS,
   axi_lite_bus_t.slave outM,
   axi_lite_mstr_rec_bus_t.P rec_out
);
parameter FIFO_DEPTH=32;

// pass through B Channel
assign inS.bresp = outM.bresp;
assign inS.bvalid = outM.bvalid;
assign outM.bready = inS.bready;

// pass through R Channel
assign inS.rdata = outM.rdata;
assign inS.rresp = outM.rresp;
assign inS.rvalid = outM.rvalid;
assign outM.rready = inS.rready;

logic bubble_en;
logic siderec_ready;
logic [2:0] rec_valid;  // 0:AW, 1:W, 2:AR
logic [2:0] new_packet; // 0:AW, 1:W, 2:AR
assign rec_out.valid = &rec_valid;
// FIXME this might violate AXI's spec that there should be no combinational
// paths between inputs (rec_valid) to outputs (siderec_ready) in the master
// or subordinate interfaces.
assign siderec_ready = &rec_valid && rec_out.ready;
assign bubble_en = &new_packet;

// AW Channel
logic AW_rec_valid, AW_new_packet;
channel_siderec #(.DEPTH(FIFO_DEPTH), .WIDTH($bits(axil_rr_AW_t))) CHANNEL_AW (
   .clk(clk),
   .sync_rst_n(sync_rst_n),
   .din(inS.awaddr),
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
assign outM.awvalid = inS.awvalid;

// W  Channel
logic W_rec_valid, W_new_packet;
channel_siderec #(.DEPTH(FIFO_DEPTH), .WIDTH($bits(axil_rr_W_t))) CHANNEL_W (
   .clk(clk),
   .sync_rst_n(sync_rst_n),
   .din({inS.wdata, inS.wstrb}),
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
endmodule
