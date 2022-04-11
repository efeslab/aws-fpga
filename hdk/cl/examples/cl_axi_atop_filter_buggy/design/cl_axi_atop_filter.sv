// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.

module cl_axi_atop_filter_top #(parameter NUM_DDR=4) 

(
   `include "cl_ports.vh"

);

`include "cl_common_defines.vh"      // CL Defines for all examples
`include "cl_id_defines.vh"          // Defines for ID0 and ID1 (PCI ID's)
`include "cl_axi_atop_filter_defines.vh"

// TIE OFF ALL UNUSED INTERFACES
// Including all the unused interface to tie off
// This list is put in the top of the fie to remind
// developers to remve the specific interfaces
// that the CL will use

`include "unused_sh_bar1_template.inc"
`include "unused_cl_sda_template.inc"
`include "unused_ddr_a_b_d_template.inc"
`include "unused_ddr_c_template.inc"


// Define the addition pipeline stag
// needed to close timing for the various
// place where ATG (Automatic Test Generator)
// is defined
   
   localparam NUM_CFG_STGS_CL_DDR_ATG = 8;
   localparam NUM_CFG_STGS_SH_DDR_ATG = 4;
   localparam NUM_CFG_STGS_PCIE_ATG = 4;

// To reduce RTL simulation time, only 8KiB of
// each external DRAM is scrubbed in simulations

`ifdef SIM
   localparam DDR_SCRB_MAX_ADDR = 64'h1FFF;
`else   
   localparam DDR_SCRB_MAX_ADDR = 64'h3FFFFFFFF; //16GB 
`endif
   localparam DDR_SCRB_BURST_LEN_MINUS1 = 15;

`ifdef NO_CL_TST_SCRUBBER
   localparam NO_SCRB_INST = 1;
`else
   localparam NO_SCRB_INST = 0;
`endif   

assign cl_sh_id0 = `CL_SH_ID0;
assign cl_sh_id1 = `CL_SH_ID1;

//---------------------------- 
// Internal signals
//---------------------------- 
axi_bus_t pcis_bus();
axi_bus_t pcim_bus();
axi_bus_t ddr_mstr_bus();

axi_lite_bus_t sh_ocl_bus();
axi_lite_bus_t cl_axil_slv_bus();

logic clk;
(* dont_touch = "true" *) logic pipe_rst_n;
logic pre_sync_rst_n;
(* dont_touch = "true" *) logic sync_rst_n;
logic sh_cl_flr_assert_q;
//---------------------------- 
// End Internal signals
//----------------------------

// Unused 'full' signals
assign cl_sh_dma_rd_full  = 1'b0;
assign cl_sh_dma_wr_full  = 1'b0;

// Unused *burst signals
assign cl_sh_ddr_arburst[1:0] = 2'h0;
assign cl_sh_ddr_awburst[1:0] = 2'h0;


assign clk = clk_main_a0;

//reset synchronizer
lib_pipe #(.WIDTH(1), .STAGES(4)) PIPE_RST_N (.clk(clk), .rst_n(1'b1), .in_bus(rst_main_n), .out_bus(pipe_rst_n));
   
always_ff @(negedge pipe_rst_n or posedge clk)
   if (!pipe_rst_n)
   begin
      pre_sync_rst_n <= 0;
      sync_rst_n <= 0;
   end
   else
   begin
      pre_sync_rst_n <= 1;
      sync_rst_n <= pre_sync_rst_n;
   end

//FLR response 
always_ff @(negedge sync_rst_n or posedge clk)
   if (!sync_rst_n)
   begin
      sh_cl_flr_assert_q <= 0;
      cl_sh_flr_done <= 0;
   end
   else
   begin
      sh_cl_flr_assert_q <= sh_cl_flr_assert;
      cl_sh_flr_done <= sh_cl_flr_assert_q && !cl_sh_flr_done;
   end


///////////////////////////////////////////////////////////////////////
///////////////// DMA PCIS SLAVE module ///////////////////////////////
///////////////////////////////////////////////////////////////////////
//// pcis_bus wrapper
assign pcis_bus.awvalid = sh_cl_dma_pcis_awvalid;
assign pcis_bus.awaddr = sh_cl_dma_pcis_awaddr;
assign pcis_bus.awid = sh_cl_dma_pcis_awid;
assign pcis_bus.awlen = sh_cl_dma_pcis_awlen;
assign pcis_bus.awsize = sh_cl_dma_pcis_awsize;
assign cl_sh_dma_pcis_awready = pcis_bus.awready;
assign pcis_bus.wvalid = sh_cl_dma_pcis_wvalid;
assign pcis_bus.wdata = sh_cl_dma_pcis_wdata;
assign pcis_bus.wstrb = sh_cl_dma_pcis_wstrb;
assign pcis_bus.wlast = sh_cl_dma_pcis_wlast;
assign cl_sh_dma_pcis_wready = pcis_bus.wready;
assign cl_sh_dma_pcis_bvalid = pcis_bus.bvalid;
assign cl_sh_dma_pcis_bresp = pcis_bus.bresp;
assign cl_sh_dma_pcis_bid = pcis_bus.bid;
assign pcis_bus.bready = sh_cl_dma_pcis_bready;
assign pcis_bus.arvalid = sh_cl_dma_pcis_arvalid;
assign pcis_bus.araddr = sh_cl_dma_pcis_araddr;
assign pcis_bus.arid[5:0] = sh_cl_dma_pcis_arid;
assign pcis_bus.arlen = sh_cl_dma_pcis_arlen;
assign pcis_bus.arsize = sh_cl_dma_pcis_arsize;
assign cl_sh_dma_pcis_arready = pcis_bus.arready;
assign cl_sh_dma_pcis_rvalid = pcis_bus.rvalid;
assign cl_sh_dma_pcis_rid = pcis_bus.rid[5:0];
assign cl_sh_dma_pcis_rlast = pcis_bus.rlast;
assign cl_sh_dma_pcis_rresp = pcis_bus.rresp;
assign cl_sh_dma_pcis_rdata = pcis_bus.rdata;
assign pcis_bus.rready = sh_cl_dma_pcis_rready;
//// pcim_bus wrapper
assign cl_sh_pcim_awvalid = pcim_bus.awvalid;
assign cl_sh_pcim_awaddr = pcim_bus.awaddr;
assign cl_sh_pcim_awid = pcim_bus.awid;
assign cl_sh_pcim_awlen = pcim_bus.awlen;
assign cl_sh_pcim_awsize = pcim_bus.awsize;
assign pcim_bus.awready = sh_cl_pcim_awready;
assign cl_sh_pcim_wvalid = pcim_bus.wvalid;
assign cl_sh_pcim_wdata = pcim_bus.wdata;
assign cl_sh_pcim_wstrb = pcim_bus.wstrb;
assign cl_sh_pcim_wlast = pcim_bus.wlast;
assign pcim_bus.wready = sh_cl_pcim_wready;
assign pcim_bus.bvalid = sh_cl_pcim_bvalid;
assign pcim_bus.bresp = sh_cl_pcim_bresp;
assign pcim_bus.bid = sh_cl_pcim_bid;
assign cl_sh_pcim_bready = pcim_bus.bready;
assign cl_sh_pcim_arvalid = pcim_bus.arvalid;
assign cl_sh_pcim_araddr = pcim_bus.araddr;
assign cl_sh_pcim_arid[5:0] = pcim_bus.arid;
assign cl_sh_pcim_arlen = pcim_bus.arlen;
assign cl_sh_pcim_arsize = pcim_bus.arsize;
assign pcim_bus.arready = sh_cl_pcim_arready;
assign pcim_bus.rvalid = sh_cl_pcim_rvalid;
assign pcim_bus.rid = sh_cl_pcim_rid[5:0];
assign pcim_bus.rlast = sh_cl_pcim_rlast;
assign pcim_bus.rresp = sh_cl_pcim_rresp;
assign pcim_bus.rdata = sh_cl_pcim_rdata;
assign cl_sh_pcim_rready = pcim_bus.rready;

///////////////////////////////////////////////////////////////////////
///////////////// DMA PCIS SLAVE module ///////////////////////////////
///////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////
///////////////// OCL SLAVE registering ///////////////////////////////
///////////////////////////////////////////////////////////////////////

assign sh_ocl_bus.awvalid = sh_ocl_awvalid;
assign sh_ocl_bus.awaddr[31:0] = sh_ocl_awaddr;
assign ocl_sh_awready = sh_ocl_bus.awready;
assign sh_ocl_bus.wvalid = sh_ocl_wvalid;
assign sh_ocl_bus.wdata[31:0] = sh_ocl_wdata;
assign sh_ocl_bus.wstrb[3:0] = sh_ocl_wstrb;
assign ocl_sh_wready = sh_ocl_bus.wready;
assign ocl_sh_bvalid = sh_ocl_bus.bvalid;
assign ocl_sh_bresp = sh_ocl_bus.bresp;
assign sh_ocl_bus.bready = sh_ocl_bready;
assign sh_ocl_bus.arvalid = sh_ocl_arvalid;
assign sh_ocl_bus.araddr[31:0] = sh_ocl_araddr;
assign ocl_sh_arready = sh_ocl_bus.arready;
assign ocl_sh_rvalid = sh_ocl_bus.rvalid;
assign ocl_sh_rresp = sh_ocl_bus.rresp;
assign ocl_sh_rdata = sh_ocl_bus.rdata[31:0];
assign sh_ocl_bus.rready = sh_ocl_rready;

(* dont_touch = "true" *) logic ocl_slv_sync_rst_n;
lib_pipe #(.WIDTH(1), .STAGES(4)) OCL_SLV_SLC_RST_N (.clk(clk), .rst_n(1'b1), .in_bus(sync_rst_n), .out_bus(ocl_slv_sync_rst_n));
cl_ocl_slv_reg CL_OCL_SLV (
    .clk(clk),
    .sync_rst_n(ocl_slv_sync_rst_n),
    .sh_ocl_bus(sh_ocl_bus),
    .sh_ocl_bus_q(cl_axil_slv_bus)
);

///////////////////////////////////////////////////////////////////////
///////////////// OCL SLAVE module ////////////////////////////////////
///////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////
///////////////// HLS Generated Accelerator ///////////////////////////
///////////////////////////////////////////////////////////////////////
axi_atop_filter_app AXI_ATOP_FILTER_BUGGY_APP (
  .clk(clk), .rstn(sync_rst_n),
  .pcis_bus(pcis_bus),
  .sh_ocl_bus(cl_axil_slv_bus),
  .pcim_mstr_bus(pcim_bus)
);

///////////////////////////////////////////////////////////////////////
///////////////// HLS Generated Accelerator ///////////////////////////
///////////////////////////////////////////////////////////////////////

endmodule   
