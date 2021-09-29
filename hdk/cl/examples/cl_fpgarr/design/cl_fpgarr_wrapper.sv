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

// An illustration of the this wrapper
//
//              (AXI interconnect)
//
// *-------*            *---*   rr_pcim  *-----------*   cl_pcim   *-------*
// |       |           /   S| <========= |M subord  S| <========== |M      |
// |       |  sh_pcim *     |            |  logging  |             |       |
// |      S| <========|     |            *-----------*             |       |
// |       |          *     |   logging_wb    ‖                    |       |
// | Shell |           \   S| <======+========+                    |  CL   |
// |       |            *---*        ‖                             |       |
// |       |                    *-----------*                      |       |
// |       |                    |    mstr   |                      |       |
// |      M| =================> |M logging S| ===================> |S      |
// |       |      ocl/          *-----------*        rr_xxx        |       |
// *-------*      sda/                                             *-------*
//                bar1/
//                pcis

// connect original F1 interfaces to sv interfaces
// TODO: need to try adding register slice for timing
`AXI_SLV_WIRE2BUS(sh_pcim_bus, cl, sh, _pcim_);
rr_axi_bus_t sh_pcim_bus_q();
rr_axi_register_slice PCIM_AXI_REG_SLC (
  .clk(clk), .rstn(rstn),
  .slv(sh_pcim_bus_q),
  .mstr(sh_pcim_bus)
);
`AXI_MSTR_WIRE2BUS(dma_pcis_bus, sh, cl, _dma_pcis_);
rr_axi_bus_t dma_pcis_bus_q();
rr_axi_register_slice PCIS_AXI_REG_SLC (
  .clk(clk), .rstn(rstn),
  .slv(dma_pcis_bus),
  .mstr(dma_pcis_bus_q)
);
`AXIL_MSTR_WIRE2BUS(sda_bus, sda, cl, _);
rr_axi_lite_bus_t sda_bus_q();
rr_axi_register_slice_lite SDA_AXL_REG_SLC (
  .clk(clk), .rstn(rstn),
  .slv(sda_bus),
  .mstr(sda_bus_q)
);
`AXIL_MSTR_WIRE2BUS(ocl_bus, sh, ocl, _);
rr_axi_lite_bus_t ocl_bus_q();
rr_axi_register_slice_lite OCL_AXL_REG_SLC (
  .clk(clk), .rstn(rstn),
  .slv(ocl_bus),
  .mstr(ocl_bus_q)
);
`AXIL_MSTR_WIRE2BUS(bar1_bus, sh, bar1, _);
rr_axi_lite_bus_t bar1_bus_q();
rr_axi_register_slice_lite BAR1_AXL_REG_SLC (
  .clk(clk), .rstn(rstn),
  .slv(bar1_bus),
  .mstr(bar1_bus_q)
);
// cl_pcim_bus is the pcim bus coming directly out of cl, it is supposed to be
// logged then passed through to an axi interconnect together with the logging
// traffic
rr_axi_bus_t cl_pcim_bus();

////////////////////////////////////////////////////////////////////////////////
// LOG AXI bus
////////////////////////////////////////////////////////////////////////////////
// PCIM bus
rr_axi_bus_t rr_pcim_bus();
`AXI_SLV_LOGGING_BUS(rr_pcim_logging_bus);
axi_slv_recorder pcim_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inM(rr_pcim_bus),
  .outS(cl_pcim_bus),
  .axi_log(rr_pcim_logging_bus)
);
// PCIS bus
rr_axi_bus_t rr_dma_pcis_bus();
`AXI_MSTR_LOGGING_BUS(rr_dma_pcis_logging_bus);
axi_mstr_recorder dma_pcis_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inS(dma_pcis_bus_q),
  .outM(rr_dma_pcis_bus),
  .axi_log(rr_dma_pcis_logging_bus)
);
////////////////////////////////////////////////////////////////////////////////
// LOG AXIL bus
////////////////////////////////////////////////////////////////////////////////
// SDA AXIL
rr_axi_lite_bus_t rr_sda_bus();
`AXIL_MSTR_LOGGING_BUS(rr_sda_logging_bus);
axil_mstr_recorder sda_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inS(sda_bus_q),
  .outM(rr_sda_bus),
  .axil_log(rr_sda_logging_bus)
);
// OCL AXIL
rr_axi_lite_bus_t rr_ocl_bus();
`AXIL_MSTR_LOGGING_BUS(rr_ocl_logging_bus);
axil_mstr_recorder ocl_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inS(ocl_bus_q),
  .outM(rr_ocl_bus),
  .axil_log(rr_ocl_logging_bus)
);
// BAR1 AXIL
rr_axi_lite_bus_t rr_bar1_bus();
`AXIL_MSTR_LOGGING_BUS(rr_bar1_logging_bus);
axil_mstr_recorder bar1_bus_recorder (
  .clk(clk),
  .sync_rst_n(rstn),
  .inS(bar1_bus_q),
  .outM(rr_bar1_bus),
  .axil_log(rr_bar1_logging_bus)
);
////////////////////////////////////////////////////////////////////////////////
// connect the original top module
////////////////////////////////////////////////////////////////////////////////
// the instance name CL is to match the instance name assigned to the top CL
// module by AWS building scripts
`CL_NAME #(NUM_DDR) CL (
  `AXI_CONNECT_BUS2WIRE(cl_pcim_bus, cl, sh, _pcim_),
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
// the merging tree of the rr_packed_logging_bus_t is automatically generated
`LOGGING_BUS_UNPACK2PACK(merged_logging_bus, packed_logging_bus);
rr_logging_bus_unpack2pack top_packer(
  .clk(clk),
  .rstn(rstn),
  .in(merged_logging_bus),
  .out(packed_logging_bus)
);
`PACKED_LOGGING_BUS_TO_WBBUS(packed_logging_bus, wbbus);
rr_packed2writeback_bus wb_inst(
  .clk(clk), .rstn(rstn), .in(packed_logging_bus), .out(wbbus));
assign wbbus.ready = 1'b1;
// TODO: convert rr_stream_bus_t to logging_wb_bus via mjc's module
// TODO: need an integration test
rr_axi_bus_t logging_wb_bus();

// AXI Interconnect for the logging pcim traffic and user pcim traffic
// NOTE: that all Xid field of pcim buses, either from logging or from the cl,
// have to spare 1 bit for this interconnect.
// So instead of 16-bit Xid available in sh_pcim_bus, they only have 15-bit Xid.
rr_writeback_axi_interconnect wb_interconnect (
  .clk(clk),
  .rstn(rstn),
  .logging_wb_bus(logging_wb_bus),
  .cl_pcim_bus(rr_pcim_bus),
  .sh_pcim_bus(sh_pcim_bus_q)
);
endmodule

`undef CL_NAME
`define CL_NAME cl_fpgarr_wrapper
