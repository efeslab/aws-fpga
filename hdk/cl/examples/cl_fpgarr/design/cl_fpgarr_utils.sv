module axi_to_axil_master(
   rr_axi_bus_t.master axi,
   rr_axi_lite_bus_t.slave axil);
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


////////////////////////////////////////////////////////////////////////////////
// reduction_and is to establish fake depenencies to prevent synthesizer from
// optimizing out circuits under test. This was useful when I wanted to
// estimate the timing/resource usage of unfinished circuits.
////////////////////////////////////////////////////////////////////////////////
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
