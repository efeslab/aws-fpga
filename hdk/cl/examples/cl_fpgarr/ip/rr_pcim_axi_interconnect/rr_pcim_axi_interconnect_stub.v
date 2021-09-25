// Copyright 1986-2020 Xilinx, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------
// Tool Version: Vivado v.2020.2 (lin64) Build 3064766 Wed Nov 18 09:12:47 MST 2020
// Date        : Fri Sep 24 21:46:20 2021
// Host        : cilantro running 64-bit Ubuntu 20.04.3 LTS
// Command     : write_verilog -force -mode synth_stub
//               /mnt/storage/gefeizuo/FPGA/FPGARR/aws-fpga/hdk/cl/examples/cl_fpgarr/ip/rr_pcim_axi_interconnect/rr_pcim_axi_interconnect_stub.v
// Design      : rr_pcim_axi_interconnect
// Purpose     : Stub declaration of top-level module interface
// Device      : xcvu9p-flgb2104-2-i
// --------------------------------------------------------------------------------

// This empty module with port declaration file causes synthesis tools to infer a black box for IP.
// The synthesis directives are for Synopsys Synplify support to prevent IO buffer insertion.
// Please paste the declaration into a Verilog source file or add the file as an additional source.
module rr_pcim_axi_interconnect(ACLK, ARESETN, M00_AXI_araddr, M00_AXI_arburst, 
  M00_AXI_arcache, M00_AXI_arid, M00_AXI_arlen, M00_AXI_arlock, M00_AXI_arprot, 
  M00_AXI_arqos, M00_AXI_arready, M00_AXI_arregion, M00_AXI_arsize, M00_AXI_arvalid, 
  M00_AXI_awaddr, M00_AXI_awburst, M00_AXI_awcache, M00_AXI_awid, M00_AXI_awlen, 
  M00_AXI_awlock, M00_AXI_awprot, M00_AXI_awqos, M00_AXI_awready, M00_AXI_awregion, 
  M00_AXI_awsize, M00_AXI_awvalid, M00_AXI_bid, M00_AXI_bready, M00_AXI_bresp, 
  M00_AXI_bvalid, M00_AXI_rdata, M00_AXI_rid, M00_AXI_rlast, M00_AXI_rready, M00_AXI_rresp, 
  M00_AXI_rvalid, M00_AXI_wdata, M00_AXI_wlast, M00_AXI_wready, M00_AXI_wstrb, 
  M00_AXI_wvalid, S00_AXI_araddr, S00_AXI_arburst, S00_AXI_arcache, S00_AXI_arid, 
  S00_AXI_arlen, S00_AXI_arlock, S00_AXI_arprot, S00_AXI_arqos, S00_AXI_arready, 
  S00_AXI_arregion, S00_AXI_arsize, S00_AXI_arvalid, S00_AXI_awaddr, S00_AXI_awburst, 
  S00_AXI_awcache, S00_AXI_awid, S00_AXI_awlen, S00_AXI_awlock, S00_AXI_awprot, 
  S00_AXI_awqos, S00_AXI_awready, S00_AXI_awregion, S00_AXI_awsize, S00_AXI_awvalid, 
  S00_AXI_bid, S00_AXI_bready, S00_AXI_bresp, S00_AXI_bvalid, S00_AXI_rdata, S00_AXI_rid, 
  S00_AXI_rlast, S00_AXI_rready, S00_AXI_rresp, S00_AXI_rvalid, S00_AXI_wdata, S00_AXI_wlast, 
  S00_AXI_wready, S00_AXI_wstrb, S00_AXI_wvalid, S01_AXI_araddr, S01_AXI_arburst, 
  S01_AXI_arcache, S01_AXI_arid, S01_AXI_arlen, S01_AXI_arlock, S01_AXI_arprot, 
  S01_AXI_arqos, S01_AXI_arready, S01_AXI_arregion, S01_AXI_arsize, S01_AXI_arvalid, 
  S01_AXI_awaddr, S01_AXI_awburst, S01_AXI_awcache, S01_AXI_awid, S01_AXI_awlen, 
  S01_AXI_awlock, S01_AXI_awprot, S01_AXI_awqos, S01_AXI_awready, S01_AXI_awregion, 
  S01_AXI_awsize, S01_AXI_awvalid, S01_AXI_bid, S01_AXI_bready, S01_AXI_bresp, 
  S01_AXI_bvalid, S01_AXI_rdata, S01_AXI_rid, S01_AXI_rlast, S01_AXI_rready, S01_AXI_rresp, 
  S01_AXI_rvalid, S01_AXI_wdata, S01_AXI_wlast, S01_AXI_wready, S01_AXI_wstrb, 
  S01_AXI_wvalid)
/* synthesis syn_black_box black_box_pad_pin="ACLK,ARESETN,M00_AXI_araddr[63:0],M00_AXI_arburst[1:0],M00_AXI_arcache[3:0],M00_AXI_arid[15:0],M00_AXI_arlen[7:0],M00_AXI_arlock[0:0],M00_AXI_arprot[2:0],M00_AXI_arqos[3:0],M00_AXI_arready,M00_AXI_arregion[3:0],M00_AXI_arsize[2:0],M00_AXI_arvalid,M00_AXI_awaddr[63:0],M00_AXI_awburst[1:0],M00_AXI_awcache[3:0],M00_AXI_awid[15:0],M00_AXI_awlen[7:0],M00_AXI_awlock[0:0],M00_AXI_awprot[2:0],M00_AXI_awqos[3:0],M00_AXI_awready,M00_AXI_awregion[3:0],M00_AXI_awsize[2:0],M00_AXI_awvalid,M00_AXI_bid[15:0],M00_AXI_bready,M00_AXI_bresp[1:0],M00_AXI_bvalid,M00_AXI_rdata[511:0],M00_AXI_rid[15:0],M00_AXI_rlast,M00_AXI_rready,M00_AXI_rresp[1:0],M00_AXI_rvalid,M00_AXI_wdata[511:0],M00_AXI_wlast,M00_AXI_wready,M00_AXI_wstrb[63:0],M00_AXI_wvalid,S00_AXI_araddr[63:0],S00_AXI_arburst[1:0],S00_AXI_arcache[3:0],S00_AXI_arid[14:0],S00_AXI_arlen[7:0],S00_AXI_arlock[0:0],S00_AXI_arprot[2:0],S00_AXI_arqos[3:0],S00_AXI_arready,S00_AXI_arregion[3:0],S00_AXI_arsize[2:0],S00_AXI_arvalid,S00_AXI_awaddr[63:0],S00_AXI_awburst[1:0],S00_AXI_awcache[3:0],S00_AXI_awid[14:0],S00_AXI_awlen[7:0],S00_AXI_awlock[0:0],S00_AXI_awprot[2:0],S00_AXI_awqos[3:0],S00_AXI_awready,S00_AXI_awregion[3:0],S00_AXI_awsize[2:0],S00_AXI_awvalid,S00_AXI_bid[14:0],S00_AXI_bready,S00_AXI_bresp[1:0],S00_AXI_bvalid,S00_AXI_rdata[511:0],S00_AXI_rid[14:0],S00_AXI_rlast,S00_AXI_rready,S00_AXI_rresp[1:0],S00_AXI_rvalid,S00_AXI_wdata[511:0],S00_AXI_wlast,S00_AXI_wready,S00_AXI_wstrb[63:0],S00_AXI_wvalid,S01_AXI_araddr[63:0],S01_AXI_arburst[1:0],S01_AXI_arcache[3:0],S01_AXI_arid[14:0],S01_AXI_arlen[7:0],S01_AXI_arlock[0:0],S01_AXI_arprot[2:0],S01_AXI_arqos[3:0],S01_AXI_arready,S01_AXI_arregion[3:0],S01_AXI_arsize[2:0],S01_AXI_arvalid,S01_AXI_awaddr[63:0],S01_AXI_awburst[1:0],S01_AXI_awcache[3:0],S01_AXI_awid[14:0],S01_AXI_awlen[7:0],S01_AXI_awlock[0:0],S01_AXI_awprot[2:0],S01_AXI_awqos[3:0],S01_AXI_awready,S01_AXI_awregion[3:0],S01_AXI_awsize[2:0],S01_AXI_awvalid,S01_AXI_bid[14:0],S01_AXI_bready,S01_AXI_bresp[1:0],S01_AXI_bvalid,S01_AXI_rdata[511:0],S01_AXI_rid[14:0],S01_AXI_rlast,S01_AXI_rready,S01_AXI_rresp[1:0],S01_AXI_rvalid,S01_AXI_wdata[511:0],S01_AXI_wlast,S01_AXI_wready,S01_AXI_wstrb[63:0],S01_AXI_wvalid" */;
  input ACLK;
  input ARESETN;
  output [63:0]M00_AXI_araddr;
  output [1:0]M00_AXI_arburst;
  output [3:0]M00_AXI_arcache;
  output [15:0]M00_AXI_arid;
  output [7:0]M00_AXI_arlen;
  output [0:0]M00_AXI_arlock;
  output [2:0]M00_AXI_arprot;
  output [3:0]M00_AXI_arqos;
  input M00_AXI_arready;
  output [3:0]M00_AXI_arregion;
  output [2:0]M00_AXI_arsize;
  output M00_AXI_arvalid;
  output [63:0]M00_AXI_awaddr;
  output [1:0]M00_AXI_awburst;
  output [3:0]M00_AXI_awcache;
  output [15:0]M00_AXI_awid;
  output [7:0]M00_AXI_awlen;
  output [0:0]M00_AXI_awlock;
  output [2:0]M00_AXI_awprot;
  output [3:0]M00_AXI_awqos;
  input M00_AXI_awready;
  output [3:0]M00_AXI_awregion;
  output [2:0]M00_AXI_awsize;
  output M00_AXI_awvalid;
  input [15:0]M00_AXI_bid;
  output M00_AXI_bready;
  input [1:0]M00_AXI_bresp;
  input M00_AXI_bvalid;
  input [511:0]M00_AXI_rdata;
  input [15:0]M00_AXI_rid;
  input M00_AXI_rlast;
  output M00_AXI_rready;
  input [1:0]M00_AXI_rresp;
  input M00_AXI_rvalid;
  output [511:0]M00_AXI_wdata;
  output M00_AXI_wlast;
  input M00_AXI_wready;
  output [63:0]M00_AXI_wstrb;
  output M00_AXI_wvalid;
  input [63:0]S00_AXI_araddr;
  input [1:0]S00_AXI_arburst;
  input [3:0]S00_AXI_arcache;
  input [14:0]S00_AXI_arid;
  input [7:0]S00_AXI_arlen;
  input [0:0]S00_AXI_arlock;
  input [2:0]S00_AXI_arprot;
  input [3:0]S00_AXI_arqos;
  output S00_AXI_arready;
  input [3:0]S00_AXI_arregion;
  input [2:0]S00_AXI_arsize;
  input S00_AXI_arvalid;
  input [63:0]S00_AXI_awaddr;
  input [1:0]S00_AXI_awburst;
  input [3:0]S00_AXI_awcache;
  input [14:0]S00_AXI_awid;
  input [7:0]S00_AXI_awlen;
  input [0:0]S00_AXI_awlock;
  input [2:0]S00_AXI_awprot;
  input [3:0]S00_AXI_awqos;
  output S00_AXI_awready;
  input [3:0]S00_AXI_awregion;
  input [2:0]S00_AXI_awsize;
  input S00_AXI_awvalid;
  output [14:0]S00_AXI_bid;
  input S00_AXI_bready;
  output [1:0]S00_AXI_bresp;
  output S00_AXI_bvalid;
  output [511:0]S00_AXI_rdata;
  output [14:0]S00_AXI_rid;
  output S00_AXI_rlast;
  input S00_AXI_rready;
  output [1:0]S00_AXI_rresp;
  output S00_AXI_rvalid;
  input [511:0]S00_AXI_wdata;
  input S00_AXI_wlast;
  output S00_AXI_wready;
  input [63:0]S00_AXI_wstrb;
  input S00_AXI_wvalid;
  input [63:0]S01_AXI_araddr;
  input [1:0]S01_AXI_arburst;
  input [3:0]S01_AXI_arcache;
  input [14:0]S01_AXI_arid;
  input [7:0]S01_AXI_arlen;
  input [0:0]S01_AXI_arlock;
  input [2:0]S01_AXI_arprot;
  input [3:0]S01_AXI_arqos;
  output S01_AXI_arready;
  input [3:0]S01_AXI_arregion;
  input [2:0]S01_AXI_arsize;
  input S01_AXI_arvalid;
  input [63:0]S01_AXI_awaddr;
  input [1:0]S01_AXI_awburst;
  input [3:0]S01_AXI_awcache;
  input [14:0]S01_AXI_awid;
  input [7:0]S01_AXI_awlen;
  input [0:0]S01_AXI_awlock;
  input [2:0]S01_AXI_awprot;
  input [3:0]S01_AXI_awqos;
  output S01_AXI_awready;
  input [3:0]S01_AXI_awregion;
  input [2:0]S01_AXI_awsize;
  input S01_AXI_awvalid;
  output [14:0]S01_AXI_bid;
  input S01_AXI_bready;
  output [1:0]S01_AXI_bresp;
  output S01_AXI_bvalid;
  output [511:0]S01_AXI_rdata;
  output [14:0]S01_AXI_rid;
  output S01_AXI_rlast;
  input S01_AXI_rready;
  output [1:0]S01_AXI_rresp;
  output S01_AXI_rvalid;
  input [511:0]S01_AXI_wdata;
  input S01_AXI_wlast;
  output S01_AXI_wready;
  input [63:0]S01_AXI_wstrb;
  input S01_AXI_wvalid;
endmodule
