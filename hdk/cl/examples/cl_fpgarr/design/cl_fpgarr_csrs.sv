`include "cl_fpgarr_defs.svh"

module rr_csrs #(
    parameter REG_STAGES=1) (
    input wire clk,
    input wire rstn,
    rr_axi_lite_bus_t.master rr_cfg_bus,
    output storage_axi_write_csr_t storage_axi_write_csr,
    output rr_mode_csr_t rr_mode_csr,
    input storage_axi_read_csr_t storage_axi_read_csr,
    input rr_state_csr_t rr_state_csr
);

    // parameter check
    if ($bits(rr_state_csr_t) > 32)
        $error("rr_state_csr_t no longer fits inside one CSR");

    logic [31:0] csrs [RR_CSR_CNT-1:0];

    logic al_aw_transmitted, al_a_transmitted, al_write_transmitted;
    logic al_write_transmitted_q, al_write_transmitted_qq;
    logic [RR_CSR_ADDR_WIDTH-1:0] al_addr, al_addr_q;
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
                al_addr <= rr_cfg_bus.awaddr[2 +: RR_CSR_ADDR_WIDTH];
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

    storage_axi_read_csr_t storage_axi_read_csr_i;
    lib_pipe #(
        .WIDTH($bits(storage_axi_read_csr_t)),
        .STAGES(REG_STAGES))
    pipe_storage_axi_read_csr(
        .clk(clk),
        .rst_n(rstn),
        .in_bus(storage_axi_read_csr),
        .out_bus(storage_axi_read_csr_i)
    );

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

            // RECORD_BITS_HI and RECORD_BITS_LO should not be written.
            // They are the statistics from the tracestorage module.
            csrs[RECORD_BITS_HI] <= storage_axi_read_csr_i.record_bits[32 +: 32];
            csrs[RECORD_BITS_LO] <= storage_axi_read_csr_i.record_bits[0 +: 32];
            csrs[VALIDATE_BITS_HI] <= storage_axi_read_csr_i.validate_bits[32 +: 32];
            csrs[VALIDATE_BITS_LO] <= storage_axi_read_csr_i.validate_bits[0 +: 32];
            csrs[RT_REPLAY_BITS_HI] <= storage_axi_read_csr_i.rt_replay_bits[32 +: 32];
            csrs[RT_REPLAY_BITS_LO] <= storage_axi_read_csr_i.rt_replay_bits[0 +: 32];
            csrs[RR_STATE] <= {{(64-$bits(rr_state_csr)){1'b0}}, rr_state_csr};
            csrs[RR_CSR_VERSION] <= RR_CSR_VERSION_INT;
            csrs[RR_TRACE_FIFO_ASSERT] <= storage_axi_read_csr_i.trace_fifo_assert[0 +: 32];
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
    logic [RR_CSR_ADDR_WIDTH-1:0] al_araddr;
    logic al_ar_transmitted, al_r_transmitted, al_r_working;

    // Only accepting read data when the previous read response is accepted by master
    assign rr_cfg_bus.arready = ~al_r_working;

    assign al_ar_transmitted = rr_cfg_bus.arvalid & rr_cfg_bus.arready;
    assign al_r_working = rr_cfg_bus.rvalid & ~rr_cfg_bus.rready;
    assign al_r_transmitted = rr_cfg_bus.rvalid & rr_cfg_bus.rready;
    assign al_araddr = rr_cfg_bus.araddr[2 +: RR_CSR_ADDR_WIDTH];

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

    storage_axi_write_csr_t storage_axi_write_csr_o;
    assign storage_axi_write_csr_o = '{
        buf_addr: {csrs[BUF_ADDR_HI], csrs[BUF_ADDR_LO]},
        buf_size: {csrs[BUF_SIZE_HI], csrs[BUF_SIZE_LO]},
        write_buf_update: al_write_transmitted_q && (al_addr == RECORD_BUF_UPDATE),
        read_buf_update: al_write_transmitted_q && (al_addr == REPLAY_BUF_UPDATE),
        record_force_finish: al_write_transmitted_q && (al_addr == RECORD_FORCE_FINISH),
        // replay_start: al_write_transmitted_q && (al_addr == REPLAY_START)
        replay_bits: {csrs[REPLAY_BITS_HI], csrs[REPLAY_BITS_LO]},
        validate_buf_update: al_write_transmitted_q && (al_addr == VALIDATE_BUF_UPDATE)
    };
    lib_pipe #(
        .WIDTH($bits(storage_axi_write_csr_t)),
        .STAGES(REG_STAGES))
    pipe_storage_axi_write_csr(
        .clk(clk),
        .rst_n(rstn),
        .in_bus(storage_axi_write_csr_o),
        .out_bus(storage_axi_write_csr)
    );

    rr_mode_csr_t rr_mode_csr_o;
    assign rr_mode_csr_o = '{
        recordEn: csrs[RR_MODE][0],
        replayEn: csrs[RR_MODE][1],
        outputValidateEn: csrs[RR_MODE][2]
    };
    lib_pipe #(
        .WIDTH($bits(rr_mode_csr_t)),
        .STAGES(REG_STAGES))
    pipe_rr_mode_csr(
        .clk(clk),
        .rst_n(rstn),
        .in_bus(rr_mode_csr_o),
        .out_bus(rr_mode_csr)
    );

`ifdef WRITEBACK_DEBUG
    always_ff @(posedge clk) begin
        if (al_aw_transmitted) begin
            $display("[rr_cfg]: axilite write addr 0x%x", rr_cfg_bus.awaddr);
        end
        if (al_w_transmitted)
            $display("[rr_cfg]: axilite write data 0x%x", rr_cfg_bus.wdata);
    end
`endif

endmodule
