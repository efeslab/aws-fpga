`include "cl_fpgarr_defs.svh"

module rr_csrs (
    input wire clk,
    input wire rstn,
    rr_axi_lite_bus_t.master rr_cfg_bus,
    output storage_axi_csr_t storage_axi_csr
);

    // Address Map:
    // 0x000000 --> BUF_ADDR_HI
    // 0x000004 --> BUF_ADDR_LO
    // 0x000008 --> BUF_SIZE_HI
    // 0x00000C --> BUF_SIZE_LO
    // 0x000010 --> BUF_UPDATE
    // 0x000014 --> FORCE_FINISH

    logic [31:0] csrs [RR_CSR_CNT-1:0];

    logic al_aw_transmitted, al_a_transmitted, al_write_transmitted;
    logic al_write_transmitted_q, al_write_transmitted_qq;
    rr_csr_enum al_addr, al_addr_q;
    logic [31:0] al_data, csr_reg;
    logic [31:0] al_strb_ext;
    logic al_aw_handled, al_w_handled;
    logic al_b_working;

    assign al_aw_transmitted = rr_cfg_bus.awready & rr_cfg_bus.awvalid;
    assign al_w_transmitted = rr_cfg_bus.wready & rr_cfg_bus.wvalid;
    assign al_write_transmitted = (al_aw_transmitted | al_aw_handled) & (al_w_transmitted | al_w_handled);

    // These two channels should not accepting new packets when either of the followings:
    // 1) the circuit is working on a previous write, which means the channel is handled but the other channel
    //    is not, i.e., al_*_handled is 1 (because this bit will be cleared when both channels are handled)
    // 2) the write response is not accepted by the master
    assign rr_cfg_bus.awready = ~al_aw_handled & ~al_b_working;
    assign rr_cfg_bus.wready = ~al_w_handled & ~al_b_working;

    // Write address and write data
    always_ff @(posedge clk) begin
        if (~rstn) begin
            al_aw_handled <= 0;
            al_w_handled <= 0;
            al_addr <= 0;
            al_data <= 0;
        end else begin
            if (al_aw_transmitted & al_w_transmitted) begin
                al_aw_handled <= 0;
            end else if (al_aw_transmitted & ~al_w_transmitted & ~al_w_handled) begin
                al_aw_handled <= 1;
            end else if (al_aw_handled & al_w_transmitted) begin
                al_aw_handled <= 0;
            end

            if (al_aw_transmitted & al_w_transmitted) begin
                al_w_handled <= 0;
            end else if (al_w_transmitted & ~al_aw_transmitted & ~al_aw_handled) begin
                al_w_handled <= 1;
            end else if (al_w_handled & al_aw_transmitted) begin
                al_w_handled <= 0;
            end

            if (al_aw_transmitted) begin
                // the 32-bit addresses address 32-bit, or 4-byte registers
                // Since we use aligned addresses for csr, the lower 2 bit of
                // the address will always be 0 thus not part of the csr index.
                al_addr <= rr_cfg_bus.awaddr[2 +: RR_CSR_WIDTH];
            end
            if (al_w_transmitted) begin
                al_data <= rr_cfg_bus.wdata;
                for (int i = 0; i < 8; i++) begin
                    al_strb_ext[i] <= rr_cfg_bus.wstrb[0];
                    al_strb_ext[8+i] <= rr_cfg_bus.wstrb[1];
                    al_strb_ext[16+i] <= rr_cfg_bus.wstrb[2];
                    al_strb_ext[24+i] <= rr_cfg_bus.wstrb[3];
                end
            end
        end
    end

    // Write register update
    always_ff @(posedge clk) begin
        if (~rstn) begin
            al_addr_q <= 0;
            al_write_transmitted_q <= 0;
            al_write_transmitted_qq <= 0;
            for (int i = 0; i < 16; i++) begin
                csrs[i] <= 0;
            end
        end else begin
            al_addr_q <= al_addr;
            al_write_transmitted_q <= al_write_transmitted;
            al_write_transmitted_qq <= al_write_transmitted_q;
            if (al_write_transmitted_q) begin
                csr_reg <= (al_strb_ext & al_data) | (~al_strb_ext & csrs[al_addr]);
            end
            if (al_write_transmitted_qq) begin
                csrs[al_addr_q] <= csr_reg;
            end
        end
    end

    // Write response
    logic al_b_transmitted;
    assign al_b_transmitted = rr_cfg_bus.bvalid & rr_cfg_bus.bready;
    assign al_b_working = rr_cfg_bus.bvalid & ~rr_cfg_bus.bready;
    always_ff @(posedge clk)  begin
        if (~rstn) begin
            rr_cfg_bus.bvalid <= 0;
            rr_cfg_bus.bresp <= 0;
        end else begin
            if (al_write_transmitted) begin
                rr_cfg_bus.bvalid <= 1;
            end else if (al_b_transmitted) begin
                rr_cfg_bus.bvalid <= 0;
            end
        end
    end

    // Read control
    logic [3:0] al_araddr;
    logic al_ar_transmitted, al_r_transmitted, al_r_working;

    // Only accepting read data when the previous read response is accepted by master
    assign rr_cfg_bus.arready = ~al_r_working;

    assign al_ar_transmitted = rr_cfg_bus.arvalid & rr_cfg_bus.arready;
    assign al_r_working = rr_cfg_bus.rvalid & ~rr_cfg_bus.rready;
    assign al_r_transmitted = rr_cfg_bus.rvalid & rr_cfg_bus.rready;
    assign al_araddr = rr_cfg_bus.araddr[5:2];

    always_ff @(posedge clk) begin
        if (~rstn) begin
            rr_cfg_bus.rvalid <= 0;
            rr_cfg_bus.rdata <= 0;
            rr_cfg_bus.rresp <= 0;
        end else begin
            if (al_ar_transmitted) begin
                rr_cfg_bus.rdata <= csrs[al_araddr];
                rr_cfg_bus.rvalid <= 1;
            end else if (al_r_transmitted) begin
                rr_cfg_bus.rvalid <= 0;
            end
        end
    end

    assign storage_axi_csr = '{
        write_buf_addr: {csrs[BUF_ADDR_HI], csrs[BUF_ADDR_LO]},
        write_buf_size: {csrs[BUF_SIZE_HI], csrs[BUF_SIZE_LO]},
        write_buf_update: al_write_transmitted_q && (al_addr == BUF_UPDATE),
        record_force_finish: al_write_transmitted_q && (al_addr == FORCE_FINISH)
    };

`ifdef WRITEBACK_DEBUG
    always_ff @(posedge clk) begin
        if (al_aw_transmitted) begin
            $display("[cfg]: axilite write addr 0x%x", rr_cfg_bus.awaddr);
        end
        if (al_w_transmitted)
            $display("[cfg]: axilite write data 0x%x", rr_cfg_bus.wdata);
    end
`endif

endmodule
