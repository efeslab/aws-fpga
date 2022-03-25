// Copyright 1986-2020 Xilinx, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------
// Tool Version: Vivado v.2020.2 (lin64) Build 3064766 Wed Nov 18 09:12:47 MST 2020
// Date        : Thu Mar 24 18:44:03 2022
// Host        : cilantro running 64-bit Ubuntu 20.04.3 LTS
// Command     : write_verilog -force -mode synth_stub
//               /home/jcma/aws-fpga/hdk/cl/examples/cl_axis_fifo_buggy/design/ip/ila_losscheck/ila_losscheck_stub.v
// Design      : ila_losscheck
// Purpose     : Stub declaration of top-level module interface
// Device      : xc7vx485tffg1157-1
// --------------------------------------------------------------------------------

// This empty module with port declaration file causes synthesis tools to infer a black box for IP.
// The synthesis directives are for Synopsys Synplify support to prevent IO buffer insertion.
// Please paste the declaration into a Verilog source file or add the file as an additional source.
(* X_CORE_INFO = "ila,Vivado 2020.2" *)
module ila_losscheck(clk, probe0, probe1)
/* synthesis syn_black_box black_box_pad_pin="clk,probe0[71:0],probe1[0:0]" */;
  input clk;
  input [71:0]probe0;
  input [0:0]probe1;
endmodule
