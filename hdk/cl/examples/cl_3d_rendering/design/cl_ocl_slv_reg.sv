module cl_ocl_slv_reg (
    input clk,
    input sync_rst_n,

    axi_lite_bus_t.master sh_ocl_bus,
    axi_lite_bus_t.slave sh_ocl_bus_q
);

//---------------------------------
// flop the input OCL bus
//---------------------------------
   axi_register_slice_light AXIL_OCL_REG_SLC (
    .aclk          (clk),
    .aresetn       (sync_rst_n),
    .s_axi_awaddr  (sh_ocl_bus.awaddr[31:0]),
    .s_axi_awvalid (sh_ocl_bus.awvalid),
    .s_axi_awready (sh_ocl_bus.awready),
    .s_axi_wdata   (sh_ocl_bus.wdata[31:0]),
    .s_axi_wstrb   (sh_ocl_bus.wstrb[3:0]),
    .s_axi_wvalid  (sh_ocl_bus.wvalid),
    .s_axi_wready  (sh_ocl_bus.wready),
    .s_axi_bresp   (sh_ocl_bus.bresp),
    .s_axi_bvalid  (sh_ocl_bus.bvalid),
    .s_axi_bready  (sh_ocl_bus.bready),
    .s_axi_araddr  (sh_ocl_bus.araddr[31:0]),
    .s_axi_arvalid (sh_ocl_bus.arvalid),
    .s_axi_arready (sh_ocl_bus.arready),
    .s_axi_rdata   (sh_ocl_bus.rdata[31:0]),
    .s_axi_rresp   (sh_ocl_bus.rresp),
    .s_axi_rvalid  (sh_ocl_bus.rvalid),
    .s_axi_rready  (sh_ocl_bus.rready),
 
    .m_axi_awaddr  (sh_ocl_bus_q.awaddr[31:0]), 
    .m_axi_awvalid (sh_ocl_bus_q.awvalid),
    .m_axi_awready (sh_ocl_bus_q.awready),
    .m_axi_wdata   (sh_ocl_bus_q.wdata[31:0]),  
    .m_axi_wstrb   (sh_ocl_bus_q.wstrb[3:0]),
    .m_axi_wvalid  (sh_ocl_bus_q.wvalid), 
    .m_axi_wready  (sh_ocl_bus_q.wready), 
    .m_axi_bresp   (sh_ocl_bus_q.bresp),  
    .m_axi_bvalid  (sh_ocl_bus_q.bvalid), 
    .m_axi_bready  (sh_ocl_bus_q.bready), 
    .m_axi_araddr  (sh_ocl_bus_q.araddr[31:0]), 
    .m_axi_arvalid (sh_ocl_bus_q.arvalid),
    .m_axi_arready (sh_ocl_bus_q.arready),
    .m_axi_rdata   (sh_ocl_bus_q.rdata[31:0]),  
    .m_axi_rresp   (sh_ocl_bus_q.rresp),  
    .m_axi_rvalid  (sh_ocl_bus_q.rvalid), 
    .m_axi_rready  (sh_ocl_bus_q.rready)
   );

endmodule
