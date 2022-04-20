// This file contains modules that mux record/replay related buses
// based on the csr configuration

// rr_axi_XXX_sel are simple combinational axi bus selectors.
// It will only connect one of the two source to the one target
// For source=>target signals (e.g. mstr.awvalid)
// sel 0=>inA, 1=>inB
// For source<=target (e.g. mstr.awready)
// inA = sel? DEFAULT : out
// inB = sel? out : DEFAULT
// NOTE that the DEFAULT is:
//   0 for valid signals, to be silent if not selected
//   1 for ready signals, to drop everything if not selected
//
// rr_axi_mstr_sel selects from two AXI master
`define SRC2TGT_SEL(sel, A, B, O, obj) \
  assign O.obj = sel? B.obj : A.obj
`define TGT2SRC_SEL(sel, A, B, O, obj, DFT) \
  assign A.obj = sel? DFT : O.obj; \
  assign B.obj = sel? O.obj : DFT
module aws_axi_mstr_sel (
  input logic sel,
  axi_bus_t.master inAS,
  axi_bus_t.master inBS,
  axi_bus_t.slave outM
);
// AW Channel
`SRC2TGT_SEL(sel, inAS, inBS, outM, awvalid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, awid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, awaddr);
`SRC2TGT_SEL(sel, inAS, inBS, outM, awlen);
`SRC2TGT_SEL(sel, inAS, inBS, outM, awsize);
`TGT2SRC_SEL(sel, inAS, inBS, outM, awready, 1);
// W  Channel
`SRC2TGT_SEL(sel, inAS, inBS, outM, wvalid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, wid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, wdata);
`SRC2TGT_SEL(sel, inAS, inBS, outM, wstrb);
`SRC2TGT_SEL(sel, inAS, inBS, outM, wlast);
`TGT2SRC_SEL(sel, inAS, inBS, outM, wready, 1);
// AR Channel
`SRC2TGT_SEL(sel, inAS, inBS, outM, arvalid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, arid);
`SRC2TGT_SEL(sel, inAS, inBS, outM, araddr);
`SRC2TGT_SEL(sel, inAS, inBS, outM, arlen);
`SRC2TGT_SEL(sel, inAS, inBS, outM, arsize);
`TGT2SRC_SEL(sel, inAS, inBS, outM, arready, 1);
// B  Channel
`TGT2SRC_SEL(sel, inAS, inBS, outM, bvalid, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, bid, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, bresp, 0);
`SRC2TGT_SEL(sel, inAS, inBS, outM, bready);
// R  Channel
`TGT2SRC_SEL(sel, inAS, inBS, outM, rvalid, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, rid, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, rdata, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, rresp, 0);
`TGT2SRC_SEL(sel, inAS, inBS, outM, rlast, 0);
`SRC2TGT_SEL(sel, inAS, inBS, outM, rready);
endmodule

module aws_axi_slv_sel (
  input logic sel,
  axi_bus_t.slave inAM,
  axi_bus_t.slave inBM,
  axi_bus_t.master outS
);
// AW Channel
`TGT2SRC_SEL(sel, inAM, inBM, outS, awvalid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, awid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, awaddr, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, awlen, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, awsize, 0);
`SRC2TGT_SEL(sel, inAM, inBM, outS, awready);
// W  Channel
`TGT2SRC_SEL(sel, inAM, inBM, outS, wvalid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, wid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, wdata, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, wstrb, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, wlast, 0);
`SRC2TGT_SEL(sel, inAM, inBM, outS, wready);
// AR Channel
`TGT2SRC_SEL(sel, inAM, inBM, outS, arvalid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, arid, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, araddr, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, arlen, 0);
`TGT2SRC_SEL(sel, inAM, inBM, outS, arsize, 0);
`SRC2TGT_SEL(sel, inAM, inBM, outS, arready);
// B  Channel
`SRC2TGT_SEL(sel, inAM, inBM, outS, bvalid);
`SRC2TGT_SEL(sel, inAM, inBM, outS, bid);
`SRC2TGT_SEL(sel, inAM, inBM, outS, bresp);
`TGT2SRC_SEL(sel, inAM, inBM, outS, bready, 1);
// R  Channel
`SRC2TGT_SEL(sel, inAM, inBM, outS, rvalid);
`SRC2TGT_SEL(sel, inAM, inBM, outS, rid);
`SRC2TGT_SEL(sel, inAM, inBM, outS, rdata);
`SRC2TGT_SEL(sel, inAM, inBM, outS, rresp);
`SRC2TGT_SEL(sel, inAM, inBM, outS, rlast);
`TGT2SRC_SEL(sel, inAM, inBM, outS, rready, 1);
endmodule
