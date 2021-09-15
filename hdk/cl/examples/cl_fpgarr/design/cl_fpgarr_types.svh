`ifndef CL_FPGARR_TYPES
`define CL_FPGARR_TYPES

////////////////////////////////////////////////////////////////////////////////
// structures to track all info you need to start an AXI(lite) transaction for
// each channel.
////////////////////////////////////////////////////////////////////////////////
// RR
// record inputs from axi master:
// used in pcis
typedef struct packed {
   // AW Channel: 91b
   //    awid   16b
   //    awaddr 64b
   //    awlen  8b
   //    awsize 3b
   logic [15:0] awid;
   logic [63:0] awaddr;
   logic [7:0] awlen;
   logic [2:0] awsize;
} axi_rr_AW_t;
parameter AXI_RR_AW_WIDTH = $bits(axi_rr_AW_t);
typedef struct packed {
   // W  Channel: 593b
   //    wid   16b
   //    wdata 512b
   //    wstrb 64b
   //    wlast 1b
   logic [15:0] wid;
   logic [511:0] wdata;
   logic [63:0] wstrb;
   logic wlast;
} axi_rr_W_t;
parameter AXI_RR_W_WIDTH = $bits(axi_rr_W_t);
typedef struct packed {
   // AR Channel: 91b
   //    arid   16b
   //    araddr 64b
   //    arlen  8b
   //    arsize 3b
   logic [15:0] arid;
   logic [63:0] araddr;
   logic [7:0] arlen;
   logic [2:0] arsize;
} axi_rr_AR_t;
parameter AXI_RR_AR_WIDTH = $bits(axi_rr_AR_t);

parameter AXI_RR_MSTR_WIDTH =
   AXI_RR_AW_WIDTH + AXI_RR_W_WIDTH + AXI_RR_AR_WIDTH;

// RR
// record inputs from axi slave:
// used in pcim
typedef struct packed {
   // B  Channel: 18b
   //    bid   16b
   //    bresp 2b
   logic [15:0] bid;
   logic [1:0] bresp;
} axi_rr_B_t;
parameter AXI_RR_B_WIDTH = $bits(axi_rr_B_t);
typedef struct packed {
   // R  Channel: 531b
   //    rid   16b
   //    rdata 512b
   //    rresp 2b
   //    rlast 1b
   logic [15:0] rid;
   logic [511:0] rdata;
   logic [1:0] rresp;
   logic rlast;
} axi_rr_R_t;
parameter AXI_RR_R_WIDTH = $bits(axi_rr_R_t);

parameter AXI_RR_SLV_WIDTH = AXI_RR_B_WIDTH + AXI_RR_R_WIDTH;


// RR
// record inputs from axi lite master:
// used in: sh_ocl, sh_bar1, sda_cl
typedef struct packed {
   // AW Channel: 32b
   //    awaddr 32b
   logic [31:0] awaddr;
} axil_rr_AW_t;
parameter AXIL_RR_AW_WIDTH = $bits(axil_rr_AW_t);
typedef struct packed {
   // W  Channel: 36b
   //    wdata 32b
   //    wstrb 4b
   logic [31:0] wdata;
   logic [3:0] wstrb;
} axil_rr_W_t;
parameter AXIL_RR_W_WIDTH = $bits(axil_rr_W_t);
typedef struct packed {
   // AR Channel: 32b
   //    araddr 32b
   logic [31:0] araddr;
} axil_rr_AR_t;
parameter AXIL_RR_AR_WIDTH = $bits(axil_rr_AR_t);
parameter AXIL_RR_MSTR_WIDTH =
   AXIL_RR_AW_WIDTH + AXIL_RR_W_WIDTH + AXIL_RR_AR_WIDTH;
parameter AXIL_RR_MSTR_OFFSET_WIDTH = $clog2(AXIL_RR_MSTR_WIDTH);

// RR
// record inputs from axi slave:
// used in: ???
typedef struct packed {
   // B  Channel:
   //    bresp 2b
   logic [1:0] bresp;
} axil_rr_B_t;
parameter AXIL_RR_B_WIDTH = $bits(axil_rr_B_t);
typedef struct packed {
   // R ChanneL: 34b
   //    rdata 32b
   //    rresp 2b
   logic [31:0] rdata;
   logic [1:0] rresp;
} axil_rr_R_t;
parameter AXIL_RR_R_WIDTH = $bits(axil_rr_R_t);
parameter AXIL_RR_SLV_WIDTH = AXIL_RR_B_WIDTH + AXIL_RR_R_WIDTH;

`define AXI_MSTR_LOGGING_BUS(name)\
  rr_logging_bus_t #(\
    .LOGB_CHANNEL_CNT(3),\
    .CHANNEL_WIDTHS({\
      {AXI_RR_AW_WIDTH}, {AXI_RR_W_WIDTH}, \
      {AXI_RR_AR_WIDTH}}), \
    .LOGE_CHANNEL_CNT(5)) name()
`define AXI_SLV_LOGGING_BUS(name)\
  rr_logging_bus_t #(\
    .LOGB_CHANNEL_CNT(2),\
    .CHANNEL_WIDTHS({\
      {AXI_RR_B_WIDTH}, {AXI_RR_R_WIDTH}}), \
    .LOGE_CHANNEL_CNT(5)) name()
`define AXIL_MSTR_LOGGING_BUS(name)\
  rr_logging_bus_t #(\
    .LOGB_CHANNEL_CNT(3),\
    .CHANNEL_WIDTHS({\
      {AXIL_RR_AW_WIDTH}, {AXIL_RR_W_WIDTH}, \
      {AXIL_RR_AR_WIDTH}}), \
    .LOGE_CHANNEL_CNT(5)) name()
`define AXIL_SLV_LOGGING_BUS(name)\
  rr_logging_bus_t #(\
    .LOGB_CHANNEL_CNT(2),\
    .CHANNEL_WIDTHS({\
      {AXIL_RR_B_WIDTH}, {AXIL_RR_R_WIDTH}}), \
    .LOGE_CHANNEL_CNT(5)) name()

`endif

// template
////////////////////////////////////////////////////////////////////////////////
//////////////////////////     garbage      ////////////////////////////////////
//////////////////////////   end of garbage ////////////////////////////////////
