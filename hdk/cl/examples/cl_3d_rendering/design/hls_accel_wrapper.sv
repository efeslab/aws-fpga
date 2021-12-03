module hls_accel_wrapper (
    input aclk,
    input aresetn,

    axi_bus_t.slave cl_axi_mstr_bus,
    axi_lite_bus_t.master cl_axil_slv_bus,
    output logic interrupt
);

    rendering rendering_inst(
        .ap_clk(aclk),
        .ap_rst_n(aresetn),
        .m_axi_gmem_AWVALID(cl_axi_mstr_bus.awvalid),
        .m_axi_gmem_AWREADY(cl_axi_mstr_bus.awready),
        .m_axi_gmem_AWADDR(cl_axi_mstr_bus.awaddr),
        .m_axi_gmem_AWID(cl_axi_mstr_bus.awid[0]),
        .m_axi_gmem_AWLEN(cl_axi_mstr_bus.awlen),
        .m_axi_gmem_AWSIZE(cl_axi_mstr_bus.awsize),
        .m_axi_gmem_AWBURST(),
        .m_axi_gmem_AWLOCK(),
        .m_axi_gmem_AWCACHE(),
        .m_axi_gmem_AWPROT(),
        .m_axi_gmem_AWQOS(),
        .m_axi_gmem_AWREGION(),
        .m_axi_gmem_AWUSER(),

        .m_axi_gmem_WVALID(cl_axi_mstr_bus.wvalid),
        .m_axi_gmem_WREADY(cl_axi_mstr_bus.wready),
        .m_axi_gmem_WDATA(cl_axi_mstr_bus.wdata),
        .m_axi_gmem_WSTRB(cl_axi_mstr_bus.wstrb),
        .m_axi_gmem_WLAST(cl_axi_mstr_bus.wlast),
        .m_axi_gmem_WID(cl_axi_mstr_bus.wid[0]),
        .m_axi_gmem_WUSER(),

        .m_axi_gmem_ARVALID(cl_axi_mstr_bus.arvalid),
        .m_axi_gmem_ARREADY(cl_axi_mstr_bus.arready),
        .m_axi_gmem_ARADDR(cl_axi_mstr_bus.araddr),
        .m_axi_gmem_ARID(cl_axi_mstr_bus.arid[0]),
        .m_axi_gmem_ARLEN(cl_axi_mstr_bus.arlen),
        .m_axi_gmem_ARSIZE(cl_axi_mstr_bus.arsize),
        .m_axi_gmem_ARBURST(),
        .m_axi_gmem_ARLOCK(),
        .m_axi_gmem_ARCACHE(),
        .m_axi_gmem_ARPROT(),
        .m_axi_gmem_ARQOS(),
        .m_axi_gmem_ARREGION(),
        .m_axi_gmem_ARUSER(),

        .m_axi_gmem_RVALID(cl_axi_mstr_bus.rvalid),
        .m_axi_gmem_RREADY(cl_axi_mstr_bus.rready),
        .m_axi_gmem_RDATA(cl_axi_mstr_bus.rdata),
        .m_axi_gmem_RLAST(cl_axi_mstr_bus.rlast),
        .m_axi_gmem_RID(cl_axi_mstr_bus.rid),
        .m_axi_gmem_RUSER(),
        .m_axi_gmem_RRESP(cl_axi_mstr_bus.rresp),

        .m_axi_gmem_BVALID(cl_axi_mstr_bus.bvalid),
        .m_axi_gmem_BREADY(cl_axi_mstr_bus.bready),
        .m_axi_gmem_BRESP(cl_axi_mstr_bus.bresp),
        .m_axi_gmem_BID(cl_axi_mstr_bus.bid[0]),
        .m_axi_gmem_BUSER(),

        .s_axi_control_AWVALID(cl_axil_slv_bus.awvalid),
        .s_axi_control_AWREADY(cl_axil_slv_bus.awready),
        .s_axi_control_AWADDR(cl_axil_slv_bus.awaddr[5:0]),
        .s_axi_control_WVALID(cl_axil_slv_bus.wvalid),
        .s_axi_control_WREADY(cl_axil_slv_bus.wready),
        .s_axi_control_WDATA(cl_axil_slv_bus.wdata),
        .s_axi_control_WSTRB(cl_axil_slv_bus.wstrb),
        .s_axi_control_ARVALID(cl_axil_slv_bus.arvalid),
        .s_axi_control_ARREADY(cl_axil_slv_bus.arready),
        .s_axi_control_ARADDR(cl_axil_slv_bus.araddr[5:0]),
        .s_axi_control_RVALID(cl_axil_slv_bus.rvalid),
        .s_axi_control_RREADY(cl_axil_slv_bus.rready),
        .s_axi_control_RDATA(cl_axil_slv_bus.rdata),
        .s_axi_control_RRESP(cl_axil_slv_bus.rresp),
        .s_axi_control_BVALID(cl_axil_slv_bus.bvalid),
        .s_axi_control_BREADY(cl_axil_slv_bus.bready),
        .s_axi_control_BRESP(cl_axil_slv_bus.bresp),
        .interrupt(interrupt)
    );

    assign cl_axi_mstr_bus.awid[15:1] = 15'h0;
    assign cl_axi_mstr_bus.arid[15:1] = 15'h0;
    assign cl_axi_mstr_bus.wid[15:1] = 15'h0;

endmodule

