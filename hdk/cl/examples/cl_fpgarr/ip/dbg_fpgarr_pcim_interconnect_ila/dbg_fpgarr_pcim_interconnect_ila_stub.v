// Copyright 1986-2020 Xilinx, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------
// Tool Version: Vivado v.2020.2 (lin64) Build 3064766 Wed Nov 18 09:12:47 MST 2020
// Date        : Mon Apr 25 03:02:20 2022
// Host        : cilantro running 64-bit Ubuntu 20.04.4 LTS
// Command     : write_verilog -force -mode synth_stub
//               /mnt/storage/gefeizuo/FPGA/FPGARR/aws-fpga/hdk/cl/examples/cl_fpgarr/ip/dbg_fpgarr_pcim_interconnect_ila/dbg_fpgarr_pcim_interconnect_ila_stub.v
// Design      : dbg_fpgarr_pcim_interconnect_ila
// Purpose     : Stub declaration of top-level module interface
// Device      : xcvu9p-flgb2104-2-i
// --------------------------------------------------------------------------------

// This empty module with port declaration file causes synthesis tools to infer a black box for IP.
// The synthesis directives are for Synopsys Synplify support to prevent IO buffer insertion.
// Please paste the declaration into a Verilog source file or add the file as an additional source.
(* X_CORE_INFO = "ila,Vivado 2020.2" *)
module dbg_fpgarr_pcim_interconnect_ila(clk, probe0, probe1, probe2, probe3, probe4, probe5, 
  probe6, probe7, probe8, probe9, probe10, probe11, probe12, probe13, probe14, probe15, probe16, probe17, 
  probe18, probe19, probe20, probe21, probe22, probe23)
/* synthesis syn_black_box black_box_pad_pin="clk,probe0[31:0],probe1[31:0],probe2[31:0],probe3[31:0],probe4[0:0],probe5[159:0],probe6[31:0],probe7[31:0],probe8[31:0],probe9[31:0],probe10[0:0],probe11[159:0],probe12[31:0],probe13[31:0],probe14[31:0],probe15[31:0],probe16[0:0],probe17[159:0],probe18[31:0],probe19[31:0],probe20[31:0],probe21[31:0],probe22[0:0],probe23[159:0]" */;
  input clk;
  input [31:0]probe0;
  input [31:0]probe1;
  input [31:0]probe2;
  input [31:0]probe3;
  input [0:0]probe4;
  input [159:0]probe5;
  input [31:0]probe6;
  input [31:0]probe7;
  input [31:0]probe8;
  input [31:0]probe9;
  input [0:0]probe10;
  input [159:0]probe11;
  input [31:0]probe12;
  input [31:0]probe13;
  input [31:0]probe14;
  input [31:0]probe15;
  input [0:0]probe16;
  input [159:0]probe17;
  input [31:0]probe18;
  input [31:0]probe19;
  input [31:0]probe20;
  input [31:0]probe21;
  input [0:0]probe22;
  input [159:0]probe23;
endmodule
