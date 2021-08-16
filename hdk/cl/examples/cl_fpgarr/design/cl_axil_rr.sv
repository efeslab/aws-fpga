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
/*
//                                         ----------------------
//                                         | FIFO for recording |
// -------------------------               ----------------------
// | In-coming AXI Channel |  ===mirror==>
// -------------------------               -----------------------
//                                         | FIFO for forwarding |
//                                         -----------------------
mirror_fifo #(.DEPTH(FIFO_DEPTH), .WIDTH($bits(axil_rr_AW_t))) MIRROR_AW (
   .clk(clk),
   .sync_rst_n(sync_rst_n),
   .din(inS.awaddr),
   .validin(inS.awvalid),
   .readyin(inS.awready),
   .douta(rec_out.AW.awaddr),
   .valida(rec_valid),
   .readya(rec_out.ready),
   .doutb(outM.awaddr),
   .validb(outM.awvalid),
   .readyb(outM.awready)
);
assign outM.awvalid = inS.awvalid;
assign outM.awaddr = inS.awaddr;
// special handle of outM.awready => inS.awready
logic new_AW_packet;
assign new_AW_packet = !rec_out.hdr.AW.busy && inS.awvalid;
// TODO: do I really need two-way handshake? can header serve as valid?
// Do I only need ready?
always_ff@(posedge clk)
   if (!sync_rst_n) begin
      outM.awvalid <= 0;
      inS.awready <= 0;
      rec_out.hdr.AW.valid <= 0;
      rec_out.hdr.AW.busy <= 0;
   end
   else begin
      if (rec_out.hdr.AW.valid) begin
         if (rec_out.ready) begin
            rec_out.hdr.AW.valid <= new_AW_packet;
            rec_out.AW.awaddr <= inS.awaddr;
         end
      end
      else begin
         rec_out.hdr.AW.valid <= new_AW_packet;
         rec_out.AW.awaddr <= inS.awaddr;
      end
      rec_out.hdr.AW.busy <= inS.awvalid && !inS.awready;
   end

endmodule
*/

`ifdef 0
///
/// Bellow were used for testing
/// old code, kept for reference
///
module axil_record_mstr (
   input clk,
   input sync_rst_n,
   axi_lite_bus_t.master axil_in,
   
   axi_lite_bus_t.slave axil_out
);
// -------------------------------------
// test, use the output in some way
// -------------------------------------
axil_rr_mstr_hdr_t rr_hdr;
// [31:0] AW
// [67:32] W
// [99:68] AR
logic [AXIL_RR_MSTR_WIDTH-1:0] packed_out;
// test pass through AW Channel
assign axil_out.awaddr = axil_in.awaddr;
assign axil_out.awvalid = axil_in.awvalid;
assign axil_in.awready = axil_out.awready;
// test pass through W Channel
reduction_and #(
   .IN_WIDTH($bits(axil_in.wdata)+$bits(packed_out)+$bits(rr_hdr)),
   .OUT_WIDTH($bits(axil_out.wdata)))
   adhoc_wdata(
      .in({axil_in.wdata, packed_out, rr_hdr}),
      .out(axil_out.wdata));
//assign axil_out.wdata = axil_in.wdata;
assign axil_out.wstrb = axil_in.wstrb;
assign axil_out.wvalid = axil_in.wvalid;
assign axil_in.wready = axil_out.wready;
// test pass through AR Channel
assign axil_out.araddr = axil_in.araddr;
assign axil_out.arvalid = axil_in.arvalid;
assign axil_in.arready = axil_out.arready;
// --------------------------------------
// End of test
// --------------------------------------

// pass through B Channel
assign axil_in.bresp = axil_out.bresp;
assign axil_in.bvalid = axil_out.bvalid;
assign axil_out.bready = axil_in.bready;
// pass through R Channel
assign axil_in.rdata = axil_out.rdata;
assign axil_in.rresp = axil_out.rresp;
assign axil_in.rvalid = axil_out.rvalid;
assign axil_out.rready = axil_in.rready;

axil_rr_mstr_hdr_t hdr[1:0];
axil_rr_AW_t rr_AW[1:0];
axil_rr_W_t rr_W[1:0];
axil_rr_AR_t rr_AR[1:0];
// stage 1: save all info to be recorded
always_ff@(posedge clk)
   if (!sync_rst_n) begin
      hdr[0] <= 0;
      rr_AW[0] <= 0;
      rr_W[0] <= 0;
      rr_AR[0] <= 0;
   end
   else begin
      hdr[0].hasAW <= axil_in.awvalid;
      if (axil_in.awvalid) begin
         rr_AW[0].awaddr <= axil_in.awaddr;
      end
      hdr[0].hasW <= axil_in.wvalid;
      if (axil_in.wvalid) begin
         rr_W[0].wdata <= axil_in.wdata;
         rr_W[0].wstrb <= axil_in.wstrb;
      end
      hdr[0].hasAR <= axil_in.arvalid;
      if (axil_in.arvalid) begin
         rr_AR[0].araddr <= axil_in.araddr;
      end
   end
// stage 2: calculate accumulated offset in the packed stream
logic [$clog2(AXIL_RR_MSTR_WIDTH)-1:0] offset_AW;
logic [$clog2(AXIL_RR_MSTR_WIDTH)-1:0] offset_W;
logic [$clog2(AXIL_RR_MSTR_WIDTH)-1:0] offset_AR;
always_ff@(posedge clk)
   if (!sync_rst_n) begin
      offset_AW <= 0;
      offset_W <= 0;
      offset_AR <= 0;
      hdr[1] <= 0;
      rr_AW[1] <= 0;
      rr_W[1] <= 0;
      rr_AR[1] <= 0;
   end
   else begin
      hdr[1] <= hdr[0];
      rr_AW[1] <= rr_AW[0];
      rr_W[1] <= rr_W[0];
      rr_AR[1] <= rr_AR[0];
      offset_AW <= 0;
      offset_W <= hdr[0].hasAW ? AXIL_RR_AW_WIDTH : 0;
      offset_AR <= hdr[0].hasAW ?
                     (hdr[0].hasW ?
                        AXIL_RR_AW_WIDTH + AXIL_RR_W_WIDTH : AXIL_RR_AW_WIDTH)
                     :
                     (hdr[0].hasW ?
                        AXIL_RR_W_WIDTH : 0);
   end
// stage 3: pack
always_ff@(posedge clk)
   if (!sync_rst_n) begin
      packed_out <= 0;
      rr_hdr <= 0;
   end
   else begin
      if (hdr[1].hasAW)
         packed_out[offset_AW +: AXIL_RR_AW_WIDTH] <= rr_AW[1];
      if (hdr[1].hasW)
         packed_out[offset_W +: AXIL_RR_W_WIDTH] <= rr_W[1];
      if (hdr[1].hasAR)
         packed_out[offset_AR +: AXIL_RR_AR_WIDTH] <= rr_AR[1];
      rr_hdr <= hdr[1];
   end
endmodule
`endif
