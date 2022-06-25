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

module axi_direct_to_axi(
   rr_axi_bus_t.master axiM,
   rr_axi_bus_t.slave axiS
);
// AW
assign axiS.awid = axiM.awid;
assign axiS.awaddr = axiM.awaddr;
assign axiS.awlen = axiM.awlen;
assign axiS.awsize = axiM.awsize;
assign axiS.awvalid = axiM.awvalid;
assign axiM.awready = axiS.awready;
// W
assign axiS.wid = axiM.wid;
assign axiS.wdata = axiM.wdata;
assign axiS.wstrb = axiM.wstrb;
assign axiS.wlast = axiM.wlast;
assign axiS.wvalid = axiM.wvalid;
assign axiM.wready = axiS.wready;
// B
assign axiM.bid = axiS.bid;
assign axiM.bresp = axiS.bresp;
assign axiM.bvalid = axiS.bvalid;
assign axiS.bready = axiM.bready;
// AR
assign axiS.arid = axiM.arid;
assign axiS.araddr = axiM.araddr;
assign axiS.arlen = axiM.arlen;
assign axiS.arsize = axiM.arsize;
assign axiS.arvalid = axiM.arvalid;
assign axiM.arready = axiS.arready;
// R
assign axiM.rid = axiS.rid;
assign axiM.rdata = axiS.rdata;
assign axiM.rresp = axiS.rresp;
assign axiM.rlast = axiS.rlast;
assign axiM.rvalid = axiS.rvalid;
assign axiS.rready = axiM.rready;
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
   assign mstr.wid = $bits(mstr.wid)'(0);
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
rr_cfg_axil_interconnect bar1_interconnect_inst (
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

module dbg_print_rr_logging_bus_CW (
   rr_logging_bus_t record_bus,
   rr_logging_bus_t validate_bus
);
int fd;
`ifndef EXPORT_MERGE_TREE_INFO_FILE
  `define EXPORT_MERGE_TREE_INFO_FILE tree.dbg.txt
`endif
parameter string FILE_PATH = `"`EXPORT_MERGE_TREE_INFO_FILE`";
initial begin
   fd = $fopen(FILE_PATH, "w");
   $fdisplay(fd, "%s,%d,%d,%d,%h,%h,%h", "record",
      record_bus.LOGB_CHANNEL_CNT, record_bus.LOGE_CHANNEL_CNT,
      $clog2(record_bus.FULL_WIDTH+1),
      record_bus.CHANNEL_WIDTHS,
      record_bus.LOGB_CHANNEL_NAMES, record_bus.LOGE_CHANNEL_NAMES);
   $fdisplay(fd, "%s,%d,%d,%d,%h,%h,%h", "validate",
      validate_bus.LOGB_CHANNEL_CNT, validate_bus.LOGE_CHANNEL_CNT,
      $clog2(validate_bus.FULL_WIDTH+1),
      validate_bus.CHANNEL_WIDTHS,
      validate_bus.LOGB_CHANNEL_NAMES, validate_bus.LOGE_CHANNEL_NAMES);
   $fclose(fd);
   $display("Please see %s for tree structure debugging info", FILE_PATH);
   $finish;
end
endmodule

module pcim_dbg_cnt(
   input clk,
   input rstn,
   rr_axi_bus_t bus
);
logic [63:0] aw_cnt;
logic [63:0] w_cnt;
logic [63:0] w_last_cnt;
logic [63:0] b_cnt;
always_ff @(posedge clk)
   if (!rstn) begin
      aw_cnt <= 0;
      w_cnt <= 0;
      w_last_cnt <= 0;
      b_cnt <= 0;
   end
   else begin
      if (bus.awvalid && bus.awready)
         aw_cnt <= aw_cnt + 1;
      if (bus.wvalid && bus.wready) begin
         w_cnt <= w_cnt + 1;
         w_last_cnt <= w_last_cnt + bus.wlast;
      end
      if (bus.bvalid && bus.bready)
         b_cnt <= b_cnt + 1;
   end
endmodule

module valid_ready_dbg_cnt #(
   parameter int CNTWIDTH=64
) (
   input clk,
   input rstn,
   input logic valid,
   input logic ready
);
logic [CNTWIDTH-1:0] cnt;
always_ff @(posedge clk)
   if (!rstn)
      cnt <= 0;
   else if (valid && ready)
      cnt <= cnt + 1;
endmodule

// drop all axi transactions
module axi_slv_blackhole (
  rr_axi_bus_t.master outS
);
  assign outS.awready = 1;
  assign outS.wready = 1;
  assign outS.bvalid = 0;
  assign outS.arready = 1;
  assign outS.rvalid = 0;
endmodule

// drive silent axi master with no transactions
module axi_mstr_whitehole (
  rr_axi_bus_t.slave outM
);
  assign outM.awvalid = 0;
  assign outM.wvalid = 0;
  assign outM.bready = 1;
  assign outM.arvalid = 0;
  assign outM.rready = 1;
endmodule

// drop all axil transactions
module axil_slv_blackhole (
  rr_axi_lite_bus_t.master outS
);
  assign outS.awready = 1;
  assign outS.wready = 1;
  assign outS.bvalid = 0;
  assign outS.arready = 1;
  assign outS.rvalid = 0;
endmodule

// drive silent axil master with no transactions
module axil_mstr_whitehole (
  rr_axi_lite_bus_t.slave outM
);
  assign outM.awvalid = 0;
  assign outM.wvalid = 0;
  assign outM.bready = 1;
  assign outM.arvalid = 0;
  assign outM.rready = 1;
endmodule
