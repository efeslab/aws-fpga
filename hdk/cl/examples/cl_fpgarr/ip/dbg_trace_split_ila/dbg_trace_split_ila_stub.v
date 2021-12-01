// Copyright 1986-2020 Xilinx, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------
// Tool Version: Vivado v.2020.2 (lin64) Build 3064766 Wed Nov 18 09:12:47 MST 2020
// Date        : Fri Dec  3 00:54:55 2021
// Host        : cilantro running 64-bit Ubuntu 20.04.3 LTS
// Command     : write_verilog -force -mode synth_stub
//               /mnt/storage/gefeizuo/FPGA/FPGARR/aws-fpga/hdk/cl/examples/cl_fpgarr/ip/dbg_trace_split_ila/dbg_trace_split_ila_stub.v
// Design      : dbg_trace_split_ila
// Purpose     : Stub declaration of top-level module interface
// Device      : xcvu9p-flgb2104-2-i
// --------------------------------------------------------------------------------

// This empty module with port declaration file causes synthesis tools to infer a black box for IP.
// The synthesis directives are for Synopsys Synplify support to prevent IO buffer insertion.
// Please paste the declaration into a Verilog source file or add the file as an additional source.
(* X_CORE_INFO = "ila,Vivado 2020.2" *)
module dbg_trace_split_ila(clk, probe0, probe1, probe2, probe3, probe4, probe5, 
  probe6, probe7, probe8, probe9, probe10, probe11, probe12)
/* synthesis syn_black_box black_box_pad_pin="clk,probe0[0:0],probe1[0:0],probe2[0:0],probe3[0:0],probe4[0:0],probe5[54:0],probe6[0:0],probe7[5:0],probe8[0:0],probe9[7:0],probe10[0:0],probe11[0:0],probe12[63:0]" */;
  input clk;
  input [0:0]probe0;
  input [0:0]probe1;
  input [0:0]probe2;
  input [0:0]probe3;
  input [0:0]probe4;
  input [54:0]probe5;
  input [0:0]probe6;
  input [5:0]probe7;
  input [0:0]probe8;
  input [7:0]probe9;
  input [0:0]probe10;
  input [0:0]probe11;
  input [63:0]probe12;
endmodule
