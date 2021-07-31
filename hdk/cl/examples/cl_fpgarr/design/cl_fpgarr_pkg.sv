`ifndef CL_FPGARR_PKG
`define CL_FPGARR_PKG
   interface axi_bus_t;
      logic[15:0] awid;
      logic[63:0] awaddr;
      logic[7:0] awlen;
      logic [2:0] awsize;
      logic awvalid;
      logic awready;
   
      logic[15:0] wid;
      logic[511:0] wdata;
      logic[63:0] wstrb;
      logic wlast;
      logic wvalid;
      logic wready;
         
      logic[15:0] bid;
      logic[1:0] bresp;
      logic bvalid;
      logic bready;
         
      logic[15:0] arid;
      logic[63:0] araddr;
      logic[7:0] arlen;
      logic [2:0] arsize;
      logic arvalid;
      logic arready;
         
      logic[15:0] rid;
      logic[511:0] rdata;
      logic[1:0] rresp;
      logic rlast;
      logic rvalid;
      logic rready;

      modport to_master (input awid, awaddr, awlen, awsize, awvalid, output awready,
                      input wid, wdata, wstrb, wlast, wvalid, output wready,
                      output bid, bresp, bvalid, input bready,
                      input arid, araddr, arlen, arsize, arvalid, output arready,
                      output rid, rdata, rresp, rlast, rvalid, input rready);

      modport to_slave  (output awid, awaddr, awlen, awsize, awvalid, input awready,
                     output wid, wdata, wstrb, wlast, wvalid, input wready,
                     input bid, bresp, bvalid, output bready,
                     output arid, araddr, arlen, arsize, arvalid, input arready,
                     input rid, rdata, rresp, rlast, rvalid, output rready);
   endinterface

   interface axi_lite_bus_t:
      // Write Address
      logic [31:0] awaddr;
      logic awvalid;
      logic awready;
      // Write Data
      logic [31:0] wdata;
      logic [3:0] wstrb;
      logic wvalid;
      logic wready;
      // Write Response
      logic [1:0] bresp;
      logic bvalid;
      logic bready;
      // Read Address
      logic [31:0] araddr;
      logic arvalid;
      logic arready;
      // Read Response
      logic [31:0] rdata;
      logic [1:0] rresp;
      logic rvalid;
      logic rready;

      modport to_master (input awaddr, awvalid, output awready,
                         input wdata, wstrb, wvalid, output wready,
                         output bresp, bvalid, input bready,
                         input araddr, arvalid, output arready,
                         output rdata, rresp, rvalid, input rready);
      modport master (input awaddr, awvalid, output awready,
                         input wdata, wstrb, wvalid, output wready,
                         output bresp, bvalid, input bready,
                         input araddr, arvalid, output arready,
                         output rdata, rresp, rvalid, input rready);

      modport to_slave  (output awaddr, awvalid, input awready,
                         output wdata, wstrb, wvalid, input wready,
                         input bresp, bvalid, output bready,
                         output araddr, arvalid, input arready,
                         input rdata, rresp, rvalid, output rready);
      modport slave  (output awaddr, awvalid, input awready,
                         output wdata, wstrb, wvalid, input wready,
                         input bresp, bvalid, output bready,
                         output araddr, arvalid, input arready,
                         input rdata, rresp, rvalid, output rready);
   endinterface

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
   } axi_rr_AW;
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
   } axi_rr_W;
   typedef struct packed {
      // AR Channel: 91b
      //    arid   16b
      //    araddr 64b
      //    arlen  8b
      //    arsize 3b
      logic [15:0] arid;
      logic [63:0] araddr;
      logic [7:0] arlen;
      logic [2:0] arsize
   } axi_rr_AR;
   
   typedef struct packed {
      logic hasAW;
      logic hasW;
      logic hasAR;
   } axi_rr_mstr_hdr;

   // RR
   // record inputs from axi slave:
   // used in pcim
   typedef struct packed {
      // B  Channel: 18b
      //    bid   16b
      //    bresp 2b
      logic [15:0] bid;
      logic [1:0] bresp;
   } axi_rr_B;
   typedef struct packed {
      // R Channel: 531b
      //    rid   16b
      //    rdata 512b
      //    rresp 2b
      //    rlast 1b
      logic [15:0] rid;
      logic [511:0] rdata;
      logic [1:0] rresp;
      logic rlast;
   } axi_rr_R;

   typedef struct packed {
      logic hasB;
      logic hasR;
   } axi_rr_slv_hdr;


   // RR
   // record inputs from axi lite master:
   // used in: sh_ocl, sh_bar1, sda_cl
   typedef struct packed {
      // AW Channel: 32b
      //    awaddr 32b
      logic [31:0] awaddr;
   } axil_rr_AW;
   typedef struct packed {
      // W  Channel: 36b
      //    wdata 32b
      //    wstrb 4b
      logic [31:0] wdata;
      logic [3:0] wstrb;
   } axil_rr_W;
   typedef struct packed {
      // AR Channel: 32b
      //    araddr 32b
      logic [31:0] araddr;
   } axil_rr_AR;

   // RR
   // record inputs from axi slave:
   // used in: ???
   typedef struct packed {
      // B  Channel:
      //    bresp 2b
      logic [1:0] bresp;
   } axil_rr_B;
   typedef struct packed {
      // R ChanneL: 34b
      //    rdata 32b
      //    rresp 2b
      logic [31:0] rdata;
      logic [1:0] rresp;
   } axil_rr_R;
