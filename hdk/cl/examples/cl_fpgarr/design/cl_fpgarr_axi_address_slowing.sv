`include "cl_fpgarr_defs.svh"
`include "cl_fpgarr_types.svh"
`include "cl_fpgarr_packing_cfg.svh"

module rr_axi_address_slowing (
    input wire clk,
    input wire rstn,
    rr_axi_bus_t.master axi_in,
    rr_axi_bus_t.slave axi_out
);

    // W
    assign axi_out.wid = axi_in.wid;
    assign axi_out.wdata = axi_in.wdata;
    assign axi_out.wstrb = axi_in.wstrb;
    assign axi_out.wlast = axi_in.wlast;
    assign axi_out.wvalid = axi_in.wvalid;
    assign axi_in.wready = axi_out.wready;

    // B
    assign axi_in.bid = axi_out.bid;
    assign axi_in.bresp = axi_out.bresp;
    assign axi_in.bvalid = axi_out.bvalid;
    assign axi_out.bready = axi_in.bready;

    // R
    assign axi_in.rid = axi_out.rid;
    assign axi_in.rdata = axi_out.rdata;
    assign axi_in.rresp = axi_out.rresp;
    assign axi_in.rlast = axi_out.rlast;
    assign axi_in.rvalid = axi_out.rvalid;
    assign axi_out.rready = axi_in.rready;

    // AW
    assign axi_out.awid = axi_in.awid;
    assign axi_out.awaddr = axi_in.awaddr;
    assign axi_out.awlen = axi_in.awlen;
    assign axi_out.awsize = axi_in.awsize;

    logic [8:0] awlen_reg, awlen, w_count_reg, w_count_next, w_count;

    assign w_count = w_count_next;
    always_comb begin
        w_count_next = w_count_reg;
        if (axi_in.wvalid && axi_in.wready)
            w_count_next = w_count_next + 1;
    end

    assign awlen = (axi_in.awvalid && axi_in.awready) ? axi_in.awlen + 1 : awlen_reg;
    always_ff @(posedge clk) begin
        if (!rstn) begin
            awlen_reg <= 0;
            w_count_reg <= 0;
        end else begin
            if (axi_in.awvalid && axi_in.awready) begin
                awlen_reg <= axi_in.awlen + 1;
            end

            if (w_count_next == awlen)
                w_count_reg <= 0;
            else
                w_count_reg <= w_count_next;
        end
    end

    logic aw_accept;
    assign axi_out.awvalid = aw_accept && axi_in.awvalid;
    assign axi_in.awready = aw_accept && axi_out.awready;
    always_ff @(posedge clk) begin
        if (!rstn) begin
            aw_accept <= 1;
        end else if (axi_in.awvalid && axi_in.awready) begin
            aw_accept <= 0;
        end else if (awlen == w_count) begin
            aw_accept <= 1;
        end
    end

    // AR
    assign axi_out.arid = axi_in.arid;
    assign axi_out.araddr = axi_in.araddr;
    assign axi_out.arlen = axi_in.arlen;
    assign axi_out.arsize = axi_in.arsize;

    logic [8:0] arlen_reg, arlen, r_count_reg, r_count_next, r_count;

    assign r_count = r_count_next;
    always_comb begin
        r_count_next = r_count_reg;
        if (axi_in.rvalid && axi_in.rready)
            r_count_next = r_count_next + 1;
    end

    assign arlen = (axi_in.arvalid && axi_in.arready) ? axi_in.arlen + 1 : arlen_reg;
    always_ff @(posedge clk) begin
        if (!rstn) begin
            arlen_reg <= 0;
            r_count_reg <= 0;
        end else begin
            if (axi_in.arvalid && axi_in.arready) begin
                arlen_reg <= axi_in.arlen + 1;
            end

            if (r_count_next == arlen)
                r_count_reg <= 0;
            else
                r_count_reg <= r_count_next;
        end
    end

    logic ar_accept;
    assign axi_out.arvalid = ar_accept && axi_in.arvalid;
    assign axi_in.arready = ar_accept && axi_out.arready;
    always_ff @(posedge clk) begin
        if (!rstn) begin
            ar_accept <= 1;
        end else if (axi_in.arvalid && axi_in.arready) begin
            ar_accept <= 0;
        end else if (arlen == r_count) begin
            ar_accept <= 1;
        end
    end


endmodule
