// Copyright 1986-2020 Xilinx, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------
// Tool Version: Vivado v.2020.2 (lin64) Build 3064766 Wed Nov 18 09:12:47 MST 2020
// Date        : Wed Sep 29 23:46:58 2021
// Host        : cilantro running 64-bit Ubuntu 20.04.3 LTS
// Command     : write_verilog -force -mode synth_stub
//               /mnt/storage/gefeizuo/FPGA/FPGARR/aws-fpga/hdk/cl/examples/cl_fpgarr/ip/rr_cfg_axil_interconnect/rr_cfg_axil_interconnect_stub.v
// Design      : rr_cfg_axil_interconnect
// Purpose     : Stub declaration of top-level module interface
// Device      : xcvu9p-flgb2104-2-i
// --------------------------------------------------------------------------------

// This empty module with port declaration file causes synthesis tools to infer a black box for IP.
// The synthesis directives are for Synopsys Synplify support to prevent IO buffer insertion.
// Please paste the declaration into a Verilog source file or add the file as an additional source.
module rr_cfg_axil_interconnect(ACLK, ARESETN, M00_AXI_araddr, M00_AXI_arprot, 
  M00_AXI_arready, M00_AXI_arvalid, M00_AXI_awaddr, M00_AXI_awprot, M00_AXI_awready, 
  M00_AXI_awvalid, M00_AXI_bready, M00_AXI_bresp, M00_AXI_bvalid, M00_AXI_rdata, 
  M00_AXI_rready, M00_AXI_rresp, M00_AXI_rvalid, M00_AXI_wdata, M00_AXI_wready, 
  M00_AXI_wstrb, M00_AXI_wvalid, M01_AXI_araddr, M01_AXI_arprot, M01_AXI_arready, 
  M01_AXI_arvalid, M01_AXI_awaddr, M01_AXI_awprot, M01_AXI_awready, M01_AXI_awvalid, 
  M01_AXI_bready, M01_AXI_bresp, M01_AXI_bvalid, M01_AXI_rdata, M01_AXI_rready, 
  M01_AXI_rresp, M01_AXI_rvalid, M01_AXI_wdata, M01_AXI_wready, M01_AXI_wstrb, 
  M01_AXI_wvalid, S00_AXI_araddr, S00_AXI_arprot, S00_AXI_arready, S00_AXI_arvalid, 
  S00_AXI_awaddr, S00_AXI_awprot, S00_AXI_awready, S00_AXI_awvalid, S00_AXI_bready, 
  S00_AXI_bresp, S00_AXI_bvalid, S00_AXI_rdata, S00_AXI_rready, S00_AXI_rresp, 
  S00_AXI_rvalid, S00_AXI_wdata, S00_AXI_wready, S00_AXI_wstrb, S00_AXI_wvalid)
/* synthesis syn_black_box black_box_pad_pin="ACLK,ARESETN,M00_AXI_araddr[31:0],M00_AXI_arprot[2:0],M00_AXI_arready[0:0],M00_AXI_arvalid[0:0],M00_AXI_awaddr[31:0],M00_AXI_awprot[2:0],M00_AXI_awready[0:0],M00_AXI_awvalid[0:0],M00_AXI_bready[0:0],M00_AXI_bresp[1:0],M00_AXI_bvalid[0:0],M00_AXI_rdata[31:0],M00_AXI_rready[0:0],M00_AXI_rresp[1:0],M00_AXI_rvalid[0:0],M00_AXI_wdata[31:0],M00_AXI_wready[0:0],M00_AXI_wstrb[3:0],M00_AXI_wvalid[0:0],M01_AXI_araddr[31:0],M01_AXI_arprot[2:0],M01_AXI_arready[0:0],M01_AXI_arvalid[0:0],M01_AXI_awaddr[31:0],M01_AXI_awprot[2:0],M01_AXI_awready[0:0],M01_AXI_awvalid[0:0],M01_AXI_bready[0:0],M01_AXI_bresp[1:0],M01_AXI_bvalid[0:0],M01_AXI_rdata[31:0],M01_AXI_rready[0:0],M01_AXI_rresp[1:0],M01_AXI_rvalid[0:0],M01_AXI_wdata[31:0],M01_AXI_wready[0:0],M01_AXI_wstrb[3:0],M01_AXI_wvalid[0:0],S00_AXI_araddr[31:0],S00_AXI_arprot[2:0],S00_AXI_arready[0:0],S00_AXI_arvalid[0:0],S00_AXI_awaddr[31:0],S00_AXI_awprot[2:0],S00_AXI_awready[0:0],S00_AXI_awvalid[0:0],S00_AXI_bready[0:0],S00_AXI_bresp[1:0],S00_AXI_bvalid[0:0],S00_AXI_rdata[31:0],S00_AXI_rready[0:0],S00_AXI_rresp[1:0],S00_AXI_rvalid[0:0],S00_AXI_wdata[31:0],S00_AXI_wready[0:0],S00_AXI_wstrb[3:0],S00_AXI_wvalid[0:0]" */;
  input ACLK;
  input ARESETN;
  output [31:0]M00_AXI_araddr;
  output [2:0]M00_AXI_arprot;
  input [0:0]M00_AXI_arready;
  output [0:0]M00_AXI_arvalid;
  output [31:0]M00_AXI_awaddr;
  output [2:0]M00_AXI_awprot;
  input [0:0]M00_AXI_awready;
  output [0:0]M00_AXI_awvalid;
  output [0:0]M00_AXI_bready;
  input [1:0]M00_AXI_bresp;
  input [0:0]M00_AXI_bvalid;
  input [31:0]M00_AXI_rdata;
  output [0:0]M00_AXI_rready;
  input [1:0]M00_AXI_rresp;
  input [0:0]M00_AXI_rvalid;
  output [31:0]M00_AXI_wdata;
  input [0:0]M00_AXI_wready;
  output [3:0]M00_AXI_wstrb;
  output [0:0]M00_AXI_wvalid;
  output [31:0]M01_AXI_araddr;
  output [2:0]M01_AXI_arprot;
  input [0:0]M01_AXI_arready;
  output [0:0]M01_AXI_arvalid;
  output [31:0]M01_AXI_awaddr;
  output [2:0]M01_AXI_awprot;
  input [0:0]M01_AXI_awready;
  output [0:0]M01_AXI_awvalid;
  output [0:0]M01_AXI_bready;
  input [1:0]M01_AXI_bresp;
  input [0:0]M01_AXI_bvalid;
  input [31:0]M01_AXI_rdata;
  output [0:0]M01_AXI_rready;
  input [1:0]M01_AXI_rresp;
  input [0:0]M01_AXI_rvalid;
  output [31:0]M01_AXI_wdata;
  input [0:0]M01_AXI_wready;
  output [3:0]M01_AXI_wstrb;
  output [0:0]M01_AXI_wvalid;
  input [31:0]S00_AXI_araddr;
  input [2:0]S00_AXI_arprot;
  output [0:0]S00_AXI_arready;
  input [0:0]S00_AXI_arvalid;
  input [31:0]S00_AXI_awaddr;
  input [2:0]S00_AXI_awprot;
  output [0:0]S00_AXI_awready;
  input [0:0]S00_AXI_awvalid;
  input [0:0]S00_AXI_bready;
  output [1:0]S00_AXI_bresp;
  output [0:0]S00_AXI_bvalid;
  output [31:0]S00_AXI_rdata;
  input [0:0]S00_AXI_rready;
  output [1:0]S00_AXI_rresp;
  output [0:0]S00_AXI_rvalid;
  input [31:0]S00_AXI_wdata;
  output [0:0]S00_AXI_wready;
  input [3:0]S00_AXI_wstrb;
  input [0:0]S00_AXI_wvalid;
endmodule
