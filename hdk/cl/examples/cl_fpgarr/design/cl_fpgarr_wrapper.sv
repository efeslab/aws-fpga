`include "cl_fpgarr_defs.svh"
`include "cl_fpgarr_types.svh"

`ifndef CL_NAME
`define CL_NAME unnamed_top_module
`endif
module cl_fpgarr_wrapper #(parameter NUM_DDR=4)
(
  `include "cl_ports.vh"
);
$info("cl_fpgarr_wrapper is INJECTED, it masquerades top module %s", `"`CL_NAME`");

logic clk;
assign clk = clk_main_a0;
logic rstn;
assign rstn = rst_main_n;

// connect original F1 interfaces to sv interfaces
`AXI_SLV_WIRE2BUS(pcim_bus, cl, sh, _pcim_);
`AXI_MSTR_WIRE2BUS(dma_pcis_bus, sh, cl, _dma_pcis_);
`AXIL_MSTR_WIRE2BUS(sda_bus, sda, cl, _);
`AXIL_MSTR_WIRE2BUS(ocl_bus, sh, ocl, _);
`AXIL_MSTR_WIRE2BUS(bar1_bus, sh, bar1, _);
////////////////////////////////////////////////////////////////////////////////
// LOG AXI bus
////////////////////////////////////////////////////////////////////////////////
// PCIM bus
axi_bus_t rr_pcim_bus();
`AXI_SLV_LOGGING_BUS(rr_pcim_logging_bus);
axi_slv_recorder pcim_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inM(pcim_bus),
  .outS(rr_pcim_bus),
  .axi_log(rr_pcim_logging_bus)
);
// PCIS bus
axi_bus_t rr_dma_pcis_bus();
`AXI_MSTR_LOGGING_BUS(rr_dma_pcis_logging_bus);
axi_mstr_recorder dma_pcis_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inS(dma_pcis_bus),
  .outM(rr_dma_pcis_bus),
  .axi_log(rr_dma_pcis_logging_bus)
);
////////////////////////////////////////////////////////////////////////////////
// LOG AXIL bus
////////////////////////////////////////////////////////////////////////////////
// SDA AXIL
axi_lite_bus_t rr_sda_bus();
`AXIL_MSTR_LOGGING_BUS(rr_sda_logging_bus);
axil_mstr_recorder sda_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inS(sda_bus),
  .outM(rr_sda_bus),
  .axil_log(rr_sda_logging_bus)
);
// OCL AXIL
axi_lite_bus_t rr_ocl_bus();
`AXIL_MSTR_LOGGING_BUS(rr_ocl_logging_bus);
axil_mstr_recorder ocl_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inS(ocl_bus),
  .outM(rr_ocl_bus),
  .axil_log(rr_ocl_logging_bus)
);
// BAR1 AXIL
axi_lite_bus_t rr_bar1_bus();
`AXIL_MSTR_LOGGING_BUS(rr_bar1_logging_bus);
axil_mstr_recorder bar1_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inS(bar1_bus),
  .outM(rr_bar1_bus),
  .axil_log(rr_bar1_logging_bus)
);
////////////////////////////////////////////////////////////////////////////////
// connect the original top module
////////////////////////////////////////////////////////////////////////////////
`CL_NAME #(NUM_DDR) top (
  `AXI_CONNECT_BUS2WIRE(rr_pcim_bus, cl, sh, _pcim_),
  `AXI_CONNECT_BUS2WIRE(rr_dma_pcis_bus, sh, cl, _dma_pcis_),
  `AXIL_CONNECT_BUS2WIRE(rr_sda_bus, sda, cl, _),
  `AXIL_CONNECT_BUS2WIRE(rr_ocl_bus, sh, ocl, _),
  `AXIL_CONNECT_BUS2WIRE(rr_bar1_bus, sh, bar1, _),
  .*
);

////////////////////////////////////////////////////////////////////////////////
// Pack the logging bus
////////////////////////////////////////////////////////////////////////////////
// the merging tree of rr_logging_bus_t
// TODO: that there is a benefit to postpone the merge of wide buses
//         merged bus
//              |
//          *-- p3 ----*
//         /           |
//      *-p2-*         |
//     /      \        |
//    p0      p1       |
//   /  \     / \      |
//  /    \   /   \     |
// sda  ocl bar1 pcim pcis
//////////////////////////
`LOGGING_BUS_JOIN2(p0, rr_sda_logging_bus, rr_ocl_logging_bus);
rr_logging_bus_packer2 p0_packer(
  .inA(rr_sda_logging_bus),
  .inB(rr_ocl_logging_bus),
  .out(p0)
);
`LOGGING_BUS_JOIN2(p1, rr_bar1_logging_bus, rr_pcim_logging_bus);
rr_logging_bus_packer2 p1_packer(
  .inA(rr_bar1_logging_bus),
  .inB(rr_pcim_logging_bus),
  .out(p1)
);
`LOGGING_BUS_JOIN2(p2, p0, p1);
rr_logging_bus_packer2 p2_packer(.inA(p0), .inB(p1), .out(p2));
`LOGGING_BUS_JOIN2(merged_logging_bus, p2, rr_dma_pcis_logging_bus);
rr_logging_bus_packer2 logging_packer(
  .inA(p2),
  .inB(rr_dma_pcis_logging_bus),
  .out(merged_logging_bus)
);
`LOGGING_BUS_UNPACK2PACK(merged_logging_bus, packed_logging_bus);
rr_logging_bus_unpack2pack top_packer(
  .clk(clk),
  .rstn(rstn),
  .in(merged_logging_bus),
  .out(packed_logging_bus)
);
// the merging tree of the rr_packed_logging_bus_t is automatically generated
assign packed_logging_bus.ready = 1'b1;
endmodule

`undef CL_NAME
`define CL_NAME cl_fpgarr_wrapper
