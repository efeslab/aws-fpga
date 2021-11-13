`include "cl_fpgarr_defs.svh"

module axi_to_axil_master(
   rr_axi_bus_t.master axi,
   rr_axi_lite_bus_t.slave axil);
   // AW Channel
   assign axil.awaddr = axi.awaddr[31:0];
   assign axil.awvalid = axi.awvalid;
   assign axi.awready = axil.awready;
   // W  Channel
   assign axil.wdata = axi.wdata[31:0];
   assign axil.wstrb = axi.wstrb[3:0];
   assign axil.wvalid = axi.wvalid;
   assign axi.wready = axil.wready;
   // B  Channel
   assign axi.bresp = axil.bresp;
   assign axi.bvalid = axil.bvalid;
   assign axil.bready = axi.bready;
   // AR Channel
   assign axil.araddr = axi.araddr[31:0];
   assign axil.arvalid = axi.arvalid;
   assign axi.arready = axil.arready;
   // R  Channel
   assign axi.rdata[31:0] = axil.rdata;
   assign axi.rresp = axil.rresp;
   assign axi.rvalid = axil.rvalid;
   assign axil.rready = axi.rready;
endmodule


////////////////////////////////////////////////////////////////////////////////
// reduction_and is to establish fake depenencies to prevent synthesizer from
// optimizing out circuits under test. This was useful when I wanted to
// estimate the timing/resource usage of unfinished circuits.
////////////////////////////////////////////////////////////////////////////////
module reduction_and #(
   parameter IN_WIDTH,
   parameter OUT_WIDTH) (
   input logic [IN_WIDTH-1:0] in,
   output logic [OUT_WIDTH-1:0] out);
   localparam REMAIN = IN_WIDTH % OUT_WIDTH;
   integer i;
   always_comb begin
      out = {OUT_WIDTH{1'b0}};
      for (i=OUT_WIDTH; i < IN_WIDTH; i+=OUT_WIDTH) begin
         out = out & in[i-1 -: OUT_WIDTH];
      end
      if (REMAIN > 0)
         out = out & {{OUT_WIDTH-REMAIN{1'b0}}, in[IN_WIDTH-REMAIN +: REMAIN]};
   end
endmodule

module rr_axi_register_slice (
   input wire clk,
   input wire rstn,
   rr_axi_bus_t.master slv,
   rr_axi_bus_t.slave mstr
);
   axi_register_slice axi_reg (
       .aclk          (clk),
       .aresetn       (rstn),
       .s_axi_awid    (slv.awid),
       .s_axi_awaddr  (slv.awaddr),
       .s_axi_awlen   (slv.awlen),
       .s_axi_awvalid (slv.awvalid),
       .s_axi_awsize  (slv.awsize),
       .s_axi_awready (slv.awready),
       .s_axi_wdata   (slv.wdata),
       .s_axi_wstrb   (slv.wstrb),
       .s_axi_wlast   (slv.wlast),
       .s_axi_wvalid  (slv.wvalid),
       .s_axi_wready  (slv.wready),
       .s_axi_bid     (slv.bid),
       .s_axi_bresp   (slv.bresp),
       .s_axi_bvalid  (slv.bvalid),
       .s_axi_bready  (slv.bready),
       .s_axi_arid    (slv.arid),
       .s_axi_araddr  (slv.araddr),
       .s_axi_arlen   (slv.arlen),
       .s_axi_arvalid (slv.arvalid),
       .s_axi_arsize  (slv.arsize),
       .s_axi_arready (slv.arready),
       .s_axi_rid     (slv.rid),
       .s_axi_rdata   (slv.rdata),
       .s_axi_rresp   (slv.rresp),
       .s_axi_rlast   (slv.rlast),
       .s_axi_rvalid  (slv.rvalid),
       .s_axi_rready  (slv.rready),

       .m_axi_awid    (mstr.awid),
       .m_axi_awaddr  (mstr.awaddr),
       .m_axi_awlen   (mstr.awlen),
       .m_axi_awvalid (mstr.awvalid),
       .m_axi_awsize  (mstr.awsize),
       .m_axi_awready (mstr.awready),
       .m_axi_wdata   (mstr.wdata),
       .m_axi_wstrb   (mstr.wstrb),
       .m_axi_wvalid  (mstr.wvalid),
       .m_axi_wlast   (mstr.wlast),
       .m_axi_wready  (mstr.wready),
       .m_axi_bresp   (mstr.bresp),
       .m_axi_bvalid  (mstr.bvalid),
       .m_axi_bid     (mstr.bid),
       .m_axi_bready  (mstr.bready),
       .m_axi_arid    (mstr.arid),
       .m_axi_araddr  (mstr.araddr),
       .m_axi_arlen   (mstr.arlen),
       .m_axi_arsize  (mstr.arsize),
       .m_axi_arvalid (mstr.arvalid),
       .m_axi_arready (mstr.arready),
       .m_axi_rid     (mstr.rid),
       .m_axi_rdata   (mstr.rdata),
       .m_axi_rresp   (mstr.rresp),
       .m_axi_rlast   (mstr.rlast),
       .m_axi_rvalid  (mstr.rvalid),
       .m_axi_rready  (mstr.rready)
   );
endmodule

module rr_axi_register_slice_lite (
   input wire clk,
   input wire rstn,
   rr_axi_lite_bus_t.master slv,
   rr_axi_lite_bus_t.slave mstr
);
   axi_register_slice_light axil_reg (
    .aclk          (clk),
    .aresetn       (rstn),
    .s_axi_awaddr  (slv.awaddr),
    .s_axi_awvalid (slv.awvalid),
    .s_axi_awready (slv.awready),
    .s_axi_wdata   (slv.wdata),
    .s_axi_wstrb   (slv.wstrb),
    .s_axi_wvalid  (slv.wvalid),
    .s_axi_wready  (slv.wready),
    .s_axi_bresp   (slv.bresp),
    .s_axi_bvalid  (slv.bvalid),
    .s_axi_bready  (slv.bready),
    .s_axi_araddr  (slv.araddr),
    .s_axi_arvalid (slv.arvalid),
    .s_axi_arready (slv.arready),
    .s_axi_rdata   (slv.rdata),
    .s_axi_rresp   (slv.rresp),
    .s_axi_rvalid  (slv.rvalid),
    .s_axi_rready  (slv.rready),

    .m_axi_awaddr  (mstr.awaddr),
    .m_axi_awvalid (mstr.awvalid),
    .m_axi_awready (mstr.awready),
    .m_axi_wdata   (mstr.wdata),
    .m_axi_wstrb   (mstr.wstrb),
    .m_axi_wvalid  (mstr.wvalid),
    .m_axi_wready  (mstr.wready),
    .m_axi_bresp   (mstr.bresp),
    .m_axi_bvalid  (mstr.bvalid),
    .m_axi_bready  (mstr.bready),
    .m_axi_araddr  (mstr.araddr),
    .m_axi_arvalid (mstr.arvalid),
    .m_axi_arready (mstr.arready),
    .m_axi_rdata   (mstr.rdata),
    .m_axi_rresp   (mstr.rresp),
    .m_axi_rvalid  (mstr.rvalid),
    .m_axi_rready  (mstr.rready)
   );
endmodule

module rr_cfg_bar1_interconnect (
   input wire clk,
   input wire rstn,
   rr_axi_lite_bus_t.master from_sh_bar1_bus,
   rr_axi_lite_bus_t.slave to_cl_bar1_bus,
   rr_axi_lite_bus_t.slave rr_cfg_bus
);
// M00 is to_cl_bar1_bus (low 1MB)
// M01 is rr_cfg_bus (high 1MB)
// S00 is from_sh_bar1_bus (2MB in total)
(* dont_touch = "true" *) rr_cfg_axil_interconnect bar1_interconnect_inst (
   .ACLK(clk),
   .ARESETN(rstn),
   /* the bar1 output pass through to cl */
   .M00_AXI_araddr(to_cl_bar1_bus.araddr),
   .M00_AXI_arprot(),
   .M00_AXI_arready(to_cl_bar1_bus.arready),
   .M00_AXI_arvalid(to_cl_bar1_bus.arvalid),
   .M00_AXI_awaddr(to_cl_bar1_bus.awaddr),
   .M00_AXI_awprot(),
   .M00_AXI_awready(to_cl_bar1_bus.awready),
   .M00_AXI_awvalid(to_cl_bar1_bus.awvalid),
   .M00_AXI_bready(to_cl_bar1_bus.bready),
   .M00_AXI_bresp(to_cl_bar1_bus.bresp),
   .M00_AXI_bvalid(to_cl_bar1_bus.bvalid),
   .M00_AXI_rdata(to_cl_bar1_bus.rdata),
   .M00_AXI_rready(to_cl_bar1_bus.rready),
   .M00_AXI_rresp(to_cl_bar1_bus.rresp),
   .M00_AXI_rvalid(to_cl_bar1_bus.rvalid),
   .M00_AXI_wdata(to_cl_bar1_bus.wdata),
   .M00_AXI_wready(to_cl_bar1_bus.wready),
   .M00_AXI_wstrb(to_cl_bar1_bus.wstrb),
   .M00_AXI_wvalid(to_cl_bar1_bus.wvalid),
   /* the bar1 bus for rr configuration */
   .M01_AXI_araddr(rr_cfg_bus.araddr),
   .M01_AXI_arprot(),
   .M01_AXI_arready(rr_cfg_bus.arready),
   .M01_AXI_arvalid(rr_cfg_bus.arvalid),
   .M01_AXI_awaddr(rr_cfg_bus.awaddr),
   .M01_AXI_awprot(),
   .M01_AXI_awready(rr_cfg_bus.awready),
   .M01_AXI_awvalid(rr_cfg_bus.awvalid),
   .M01_AXI_bready(rr_cfg_bus.bready),
   .M01_AXI_bresp(rr_cfg_bus.bresp),
   .M01_AXI_bvalid(rr_cfg_bus.bvalid),
   .M01_AXI_rdata(rr_cfg_bus.rdata),
   .M01_AXI_rready(rr_cfg_bus.rready),
   .M01_AXI_rresp(rr_cfg_bus.rresp),
   .M01_AXI_rvalid(rr_cfg_bus.rvalid),
   .M01_AXI_wdata(rr_cfg_bus.wdata),
   .M01_AXI_wready(rr_cfg_bus.wready),
   .M01_AXI_wstrb(rr_cfg_bus.wstrb),
   .M01_AXI_wvalid(rr_cfg_bus.wvalid),
   /* the bar1 bus directly coming from the shell */
   .S00_AXI_araddr(from_sh_bar1_bus.araddr),
   .S00_AXI_arprot(3'b0),
   .S00_AXI_arready(from_sh_bar1_bus.arready),
   .S00_AXI_arvalid(from_sh_bar1_bus.arvalid),
   .S00_AXI_awaddr(from_sh_bar1_bus.awaddr),
   .S00_AXI_awprot(3'b0),
   .S00_AXI_awready(from_sh_bar1_bus.awready),
   .S00_AXI_awvalid(from_sh_bar1_bus.awvalid),
   .S00_AXI_bready(from_sh_bar1_bus.bready),
   .S00_AXI_bresp(from_sh_bar1_bus.bresp),
   .S00_AXI_bvalid(from_sh_bar1_bus.bvalid),
   .S00_AXI_rdata(from_sh_bar1_bus.rdata),
   .S00_AXI_rready(from_sh_bar1_bus.rready),
   .S00_AXI_rresp(from_sh_bar1_bus.rresp),
   .S00_AXI_rvalid(from_sh_bar1_bus.rvalid),
   .S00_AXI_wdata(from_sh_bar1_bus.wdata),
   .S00_AXI_wready(from_sh_bar1_bus.wready),
   .S00_AXI_wstrb(from_sh_bar1_bus.wstrb),
   .S00_AXI_wvalid(from_sh_bar1_bus.wvalid)
);
endmodule

module dbg_print_rr_logging_bus_CW #(
   parameter int LOGB_CHANNEL_CNT,
   parameter bit [LOGB_CHANNEL_CNT-1:0]
   [RR_CHANNEL_WIDTH_BITS-1:0] CHANNEL_WIDTHS,
   parameter string PREFIX
) ();
$info("%s\n%d,%h", PREFIX, LOGB_CHANNEL_CNT, CHANNEL_WIDTHS);
endmodule
