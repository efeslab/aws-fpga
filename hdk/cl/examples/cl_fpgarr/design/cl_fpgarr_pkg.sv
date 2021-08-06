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

   module axi_to_axil_master(
      axi_bus_t.master axi,
      axi_lite_bus_t.slave axil);
      // AW Channel
      assign axil.awaddr = axi.awaddr[31:0];
      assign axil.awvalid = axi.awvalid;
      assign axi.awready = axil.awready;
      // W  Channel
      assign axil.wdata = axi.wdata[31:0];
      assign axil.wstrb = axi.wstrb[3:0];
      assign axil.wvalid = axi.wvalid;
      assign axi.wready = axil.wready;
      // B  Channel
      assign axi.bresp = axil.bresp;
      assign axi.bvalid = axil.bvalid;
      assign axil.bready = axi.bready;
      // AR Channel
      assign axil.araddr = axi.araddr[31:0];
      assign axil.arvalid = axi.arvalid;
      assign axi.arready = axil.arready;
      // R  Channel
      assign axi.rdata[31:0] = axil.rdata;
      assign axi.rresp = axil.rresp;
      assign axi.rvalid = axil.rvalid;
      assign axil.rready = axi.rready;
   endmodule

   module reduction_and #(
      parameter IN_WIDTH,
      parameter OUT_WIDTH) (
      input logic [IN_WIDTH-1:0] in,
      output logic [OUT_WIDTH-1:0] out);
      localparam REMAIN = IN_WIDTH % OUT_WIDTH;
      integer i;
      always_comb begin
         out = {OUT_WIDTH{1'b0}};
         for (i=OUT_WIDTH; i < IN_WIDTH; i+=OUT_WIDTH) begin
            out = out & in[i-1 -: OUT_WIDTH];
         end
         if (REMAIN > 0)
            out = out & {{OUT_WIDTH-REMAIN{1'b0}}, in[IN_WIDTH-REMAIN +: REMAIN]};
      end
   endmodule
`endif
