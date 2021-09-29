module rr_packed2writeback_bus (
   input wire clk,
   input wire rstn,
   rr_packed_logging_bus_t.C in,
   rr_stream_bus_t.P out
);

// parameter check
generate
   if (in.LOGB_CHANNEL_CNT + in.LOGE_CHANNEL_CNT + in.FULL_WIDTH
       != out.FULL_WIDTH)
    $error("Writeback FULL_WIDTH mismatch: logb W%d, loge W%d, packed_logb_data W%d, writeback W%d\n",
      in.LOGB_CHANNEL_CNT, in.LOGE_CHANNEL_CNT, in.FULL_WIDTH, out.FULL_WIDTH);
endgenerate

// loge_valid_output is the signal outputting to the writeback_bus
// loge_valid_output[i] shows whether one (and can only be one) transaction has
// finished on channel[i] between now (some logb_valid are true) and the last
// time some logb are valid.
// if logb_valid[i] && loge_valid[i], which only happen if the transaction
// really lasts for only one cycle (ready was asserted in advance)
logic [in.LOGE_CHANNEL_CNT-1:0] loge_valid_out;

assign out.valid = in.plogb.any_valid;
assign in.ready = out.ready;
assign out.len = out.valid?
   (in.plogb.len + out.OFFSET_WIDTH'(in.LOGB_CHANNEL_CNT + in.LOGE_CHANNEL_CNT))
   : 0;
// from LSB to MSB:
// logb_valid, loge_valid, packed_logb_data
assign out.data = {in.plogb.data, loge_valid_out, in.logb_valid};

// buf loge_valid if there is no valid logb to send
always @(posedge clk)
if (!rstn)
   loge_valid_out <= 0;
else
   for (int i=0; i < in.LOGE_CHANNEL_CNT; i=i+1)
      if (out.valid && in.loge_valid[i])
         loge_valid_out[i] <= 1;
      else if (out.valid && !in.loge_valid[i])
         loge_valid_out[i] <= 0;
      else if (!out.valid && in.loge_valid[i]) begin
         loge_valid_out[i] <= 1;
         no_loge_overwrite: assert(!loge_valid_out[i]);
      end
      else // !out.valid && !in.loge_valid[i]
         loge_valid_out[i] <= loge_valid_out[i];
endmodule


////////////////////////////////////////////////////////////////////////////
// axi interconnect for sharing single shell pcim bus across the logging
// writeback module and the user pcim bus
////////////////////////////////////////////////////////////////////////////
module rr_storage_pcim_axi_interconnect (
   input wire clk,
   input wire rstn,
   rr_axi_bus_t.master logging_wb_bus,
   rr_axi_bus_t.master cl_pcim_bus,
   rr_axi_bus_t.slave sh_pcim_bus
);

rr_pcim_axi_interconnect pcim_interconnect_inst (
   .ACLK(clk),
   .ARESETN(rstn),
   /* the single output master bus connecting to the shell*/
   .M00_AXI_araddr(sh_pcim_bus.araddr),
   .M00_AXI_arburst(),
   .M00_AXI_arcache(),
   .M00_AXI_arid(sh_pcim_bus.arid),
   .M00_AXI_arlen(sh_pcim_bus.arlen),
   .M00_AXI_arlock(),
   .M00_AXI_arprot(),
   .M00_AXI_arqos(),
   .M00_AXI_arready(sh_pcim_bus.arready),
   .M00_AXI_arregion(),
   .M00_AXI_arsize(sh_pcim_bus.arsize),
   .M00_AXI_arvalid(sh_pcim_bus.arvalid),
   .M00_AXI_awaddr(sh_pcim_bus.awaddr),
   .M00_AXI_awburst(),
   .M00_AXI_awcache(),
   .M00_AXI_awid(sh_pcim_bus.awid),
   .M00_AXI_awlen(sh_pcim_bus.awlen),
   .M00_AXI_awlock(),
   .M00_AXI_awprot(),
   .M00_AXI_awqos(),
   .M00_AXI_awready(sh_pcim_bus.awready),
   .M00_AXI_awregion(),
   .M00_AXI_awsize(sh_pcim_bus.awsize),
   .M00_AXI_awvalid(sh_pcim_bus.awvalid),
   .M00_AXI_bid(sh_pcim_bus.bid),
   .M00_AXI_bready(sh_pcim_bus.bready),
   .M00_AXI_bresp(sh_pcim_bus.bresp),
   .M00_AXI_bvalid(sh_pcim_bus.bvalid),
   .M00_AXI_rdata(sh_pcim_bus.rdata),
   .M00_AXI_rid(sh_pcim_bus.rid),
   .M00_AXI_rlast(sh_pcim_bus.rlast),
   .M00_AXI_rready(sh_pcim_bus.rready),
   .M00_AXI_rresp(sh_pcim_bus.rresp),
   .M00_AXI_rvalid(sh_pcim_bus.rvalid),
   .M00_AXI_wdata(sh_pcim_bus.wdata),
   .M00_AXI_wlast(sh_pcim_bus.wlast),
   .M00_AXI_wready(sh_pcim_bus.wready),
   .M00_AXI_wstrb(sh_pcim_bus.wstrb),
   .M00_AXI_wvalid(sh_pcim_bus.wvalid),
   /* logging writeback bus (generated by rr) */
   .S00_AXI_araddr(logging_wb_bus.araddr),
   .S00_AXI_arburst(2'b1), // INCR
   .S00_AXI_arcache(4'b00),
   .S00_AXI_arid(logging_wb_bus.arid[14:0]),
   .S00_AXI_arlen(logging_wb_bus.arlen),
   .S00_AXI_arlock(1'b0),
   .S00_AXI_arprot(3'b00),
   .S00_AXI_arqos(4'b0),
   .S00_AXI_arready(logging_wb_bus.arready),
   .S00_AXI_arregion(4'b0),
   .S00_AXI_arsize(logging_wb_bus.arsize),
   .S00_AXI_arvalid(logging_wb_bus.arvalid),
   .S00_AXI_awaddr(logging_wb_bus.awaddr),
   .S00_AXI_awburst(2'b1),
   .S00_AXI_awcache(4'b00),
   .S00_AXI_awid(logging_wb_bus.awid[14:0]),
   .S00_AXI_awlen(logging_wb_bus.awlen),
   .S00_AXI_awlock(1'b0),
   .S00_AXI_awprot(3'b00),
   .S00_AXI_awqos(4'b0),
   .S00_AXI_awready(logging_wb_bus.awready),
   .S00_AXI_awregion(4'b0),
   .S00_AXI_awsize(logging_wb_bus.awsize),
   .S00_AXI_awvalid(logging_wb_bus.awvalid),
   .S00_AXI_bid(logging_wb_bus.bid[14:0]),
   .S00_AXI_bready(logging_wb_bus.bready),
   .S00_AXI_bresp(logging_wb_bus.bresp),
   .S00_AXI_bvalid(logging_wb_bus.bvalid),
   .S00_AXI_rdata(logging_wb_bus.rdata),
   .S00_AXI_rid(logging_wb_bus.rid[14:0]),
   .S00_AXI_rlast(logging_wb_bus.rlast),
   .S00_AXI_rready(logging_wb_bus.rready),
   .S00_AXI_rresp(logging_wb_bus.rresp),
   .S00_AXI_rvalid(logging_wb_bus.rvalid),
   .S00_AXI_wdata(logging_wb_bus.wdata),
   .S00_AXI_wlast(logging_wb_bus.wlast),
   .S00_AXI_wready(logging_wb_bus.wready),
   .S00_AXI_wstrb(logging_wb_bus.wstrb),
   .S00_AXI_wvalid(logging_wb_bus.wvalid),
   /* cl pcim bus (should be taken care of in rr) */
   .S01_AXI_araddr(cl_pcim_bus.araddr),
   .S01_AXI_arburst(2'b1), // INCR
   .S01_AXI_arcache(4'b00),
   .S01_AXI_arid(cl_pcim_bus.arid[14:0]),
   .S01_AXI_arlen(cl_pcim_bus.arlen),
   .S01_AXI_arlock(1'b0),
   .S01_AXI_arprot(3'b00),
   .S01_AXI_arqos(4'b0),
   .S01_AXI_arready(cl_pcim_bus.arready),
   .S01_AXI_arregion(4'b0),
   .S01_AXI_arsize(cl_pcim_bus.arsize),
   .S01_AXI_arvalid(cl_pcim_bus.arvalid),
   .S01_AXI_awaddr(cl_pcim_bus.awaddr),
   .S01_AXI_awburst(2'b1),
   .S01_AXI_awcache(4'b00),
   .S01_AXI_awid(cl_pcim_bus.awid[14:0]),
   .S01_AXI_awlen(cl_pcim_bus.awlen),
   .S01_AXI_awlock(1'b0),
   .S01_AXI_awprot(3'b00),
   .S01_AXI_awqos(4'b0),
   .S01_AXI_awready(cl_pcim_bus.awready),
   .S01_AXI_awregion(4'b0),
   .S01_AXI_awsize(cl_pcim_bus.awsize),
   .S01_AXI_awvalid(cl_pcim_bus.awvalid),
   .S01_AXI_bid(cl_pcim_bus.bid[14:0]),
   .S01_AXI_bready(cl_pcim_bus.bready),
   .S01_AXI_bresp(cl_pcim_bus.bresp),
   .S01_AXI_bvalid(cl_pcim_bus.bvalid),
   .S01_AXI_rdata(cl_pcim_bus.rdata),
   .S01_AXI_rid(cl_pcim_bus.rid[14:0]),
   .S01_AXI_rlast(cl_pcim_bus.rlast),
   .S01_AXI_rready(cl_pcim_bus.rready),
   .S01_AXI_rresp(cl_pcim_bus.rresp),
   .S01_AXI_rvalid(cl_pcim_bus.rvalid),
   .S01_AXI_wdata(cl_pcim_bus.wdata),
   .S01_AXI_wlast(cl_pcim_bus.wlast),
   .S01_AXI_wready(cl_pcim_bus.wready),
   .S01_AXI_wstrb(cl_pcim_bus.wstrb),
   .S01_AXI_wvalid(cl_pcim_bus.wvalid)
);
endmodule
