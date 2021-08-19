`ifndef CL_FPGARR_PKG
`define CL_FPGARR_PKG
`include "cl_fpgarr_types.svh"
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

      modport master (input awid, awaddr, awlen, awsize, awvalid, output awready,
                      input wid, wdata, wstrb, wlast, wvalid, output wready,
                      output bid, bresp, bvalid, input bready,
                      input arid, araddr, arlen, arsize, arvalid, output arready,
                      output rid, rdata, rresp, rlast, rvalid, input rready);

      modport slave  (output awid, awaddr, awlen, awsize, awvalid, input awready,
                     output wid, wdata, wstrb, wlast, wvalid, input wready,
                     input bid, bresp, bvalid, output bready,
                     output arid, araddr, arlen, arsize, arvalid, input arready,
                     input rid, rdata, rresp, rlast, rvalid, output rready);
   endinterface

   interface axi_lite_bus_t;
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

      modport master (input awaddr, awvalid, output awready,
                         input wdata, wstrb, wvalid, output wready,
                         output bresp, bvalid, input bready,
                         input araddr, arvalid, output arready,
                         output rdata, rresp, rvalid, input rready);

      modport slave  (output awaddr, awvalid, input awready,
                         output wdata, wstrb, wvalid, input wready,
                         input bresp, bvalid, output bready,
                         output araddr, arvalid, input arready,
                         input rdata, rresp, rvalid, output rready);
   endinterface

   // axi_mstr_rec_bus_t is the bus representing unpacked recording info for
   // axi master
   // it has a two-way handshake just like axi
   interface axi_mstr_rec_bus_t;
      logic valid;
      logic ready;
      axi_rr_mstr_hdr_t hdr;
      axi_rr_AW_t AW;
      axi_rr_W_t W;
      axi_rr_AR_t AR;
      parameter int WIDTH [0:2] = '{AXI_RR_AW_WIDTH, AXI_RR_W_WIDTH, AXI_RR_B_WIDTH};
      // recording data producer
      modport P (output valid, input ready,
                 output hdr, AW, W, AR);
      // recording data consumer
      modport C (input valid, output ready,
                 input hdr, AW, W, AR);
   endinterface

   interface axi_slv_rec_bus_t;
      logic valid;
      logic ready;
      axi_rr_slv_hdr_t hdr;
      axi_rr_B_t B;
      axi_rr_R_t R;
      // recording data producer
      modport P (output valid, input ready,
                 output hdr, B, R);
      // recording data consumer
      modport C (input valid, output ready,
                 input hdr, B, R);
   endinterface

   // axi_lite_mstr_rec_bus_t is the bus representing unpacked recording info
   // for axi lite master
   // it has a two-way handshake just like axi
   interface axi_lite_mstr_rec_bus_t;
      logic valid;
      logic ready;
      axil_rr_mstr_hdr_t hdr;
      axil_rr_AW_t AW;
      axil_rr_W_t W;
      axil_rr_AR_t AR;
      // recording data producer
      modport P (output valid, input ready,
                 output hdr, AW, W, AR);
      // recording data consumer
      modport C (input valid, output ready,
                 input hdr, AW, W, AR);
   endinterface

`endif
