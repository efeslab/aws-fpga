`include "cl_fpgarr_defs.svh"
`include "cl_fpgarr_types.svh"
`include "cl_fpgarr_packing_cfg.svh"

module rr_int_to_pcim #(
    parameter NUM_INT=16,
    parameter AXI_ADDR_WIDTH=64,
    parameter AXI_WIDTH=512
)(
    input logic clk,
    input logic rstn,
    input logic [AXI_ADDR_WIDTH-1:0] offset,
    input logic offset_update,
    input logic [NUM_INT-1:0] int_req,
    output logic [NUM_INT-1:0] int_ack,
    rr_axi_bus_t.slave pcim
);
    enum {INT_IDLE, INT_WRITE, INT_WAIT_B} state;

    logic [NUM_INT-1:0] int_hold, int_clear, int_ack_ready;
    logic [AXI_ADDR_WIDTH-1:0] int_buf_addr;
    logic wb_ready;
    logic [AXI_ADDR_WIDTH-1:0] wb_addr;
    logic [AXI_WIDTH-1:0] wb_data;
    logic axi_aw_transmitted, axi_w_transmitted, axi_write_transmitted;
    logic axi_aw_working, axi_w_working, axi_write_working;
    logic axi_b_transmitted;

    always_ff @(posedge clk) begin
        if (~rstn) begin
            int_buf_addr <= 0;
        end else begin
            if (offset_update) begin
                int_buf_addr <= offset;
            end
        end
    end

    always_ff @(posedge clk) begin
        if (~rstn) begin
            state <= INT_IDLE;
        end else begin
            case (state)
            INT_IDLE: if (int_hold != 0) state <= INT_WRITE;
            INT_WRITE: if (axi_write_transmitted) state <= INT_WAIT_B;
            INT_WAIT_B: if (axi_b_transmitted) state <= INT_IDLE;
            endcase
        end
    end

    assign axi_aw_transmitted = pcim.awready & pcim.awvalid;
    assign axi_w_transmitted = pcim.wready & pcim.wvalid;
    assign axi_b_transmitted = pcim.bready & pcim.bvalid;
    assign axi_aw_working = pcim.awvalid & ~pcim.awready;
    assign axi_w_working = pcim.wvalid & ~pcim.wready;
    assign axi_write_working = axi_aw_working | axi_w_working;

    // Transaction control
    logic axi_aw_handled, axi_w_handled;
    always_ff @(posedge clk) begin
        if (~rstn) begin
            axi_aw_handled <= 0;
            axi_w_handled <= 0;
        end else begin
            if (axi_aw_transmitted & axi_w_transmitted) begin
                axi_aw_handled <= 0;
            end else if (axi_aw_transmitted & ~axi_w_transmitted & ~axi_w_handled) begin
                axi_aw_handled <= 1;
            end else if (axi_aw_handled & axi_w_transmitted) begin
                axi_aw_handled <= 0;
            end

            if (axi_aw_transmitted & axi_w_transmitted) begin
                axi_w_handled <= 0;
            end else if (axi_w_transmitted & ~axi_aw_transmitted & ~axi_aw_handled) begin
                axi_w_handled <= 1;
            end else if (axi_w_handled & axi_aw_transmitted) begin
                axi_w_handled <= 0;
            end
        end
    end

    assign axi_write_transmitted = (axi_aw_transmitted | axi_aw_handled) & (axi_w_transmitted | axi_w_handled);
    assign write_buf_write_en = axi_write_transmitted;

    always_ff @(posedge clk) begin
        if (~rstn) begin
            wb_ready <= 0;
            wb_addr <= 0;
            wb_data <= 1;
            int_hold <= 0;
            int_ack_ready <= 0;
            int_clear <= 0;
        end else begin
            int_hold <= (int_hold & ~int_clear) | int_req;

            case(state)
                INT_IDLE: begin
                    wb_ready <= 0;
                    wb_addr <= 0;
                    if (int_hold == 0 && int_ack_ready != 0) begin
                        int_ack <= int_ack_ready;
                        int_ack_ready <= 0;
                    end
                    int_clear <= 0;
                end
                INT_WRITE: begin
                    if (~wb_ready) begin
                        for (int i = 0; i < NUM_INT; i++) begin
                            if (NUM_INT'(1 << i) & int_hold) begin
                                int_clear <= NUM_INT'(1 << i);
                                int_ack_ready <= int_ack_ready | NUM_INT'(1 << i);
                                wb_ready <= 1;
                                wb_addr <= int_buf_addr + i * AXI_WIDTH/8;
                                break;
                            end
                        end
                    end
                end
                default: begin
                    wb_ready <= 0;
                    int_clear <= 0;
                end
            endcase
        end
    end

    // Valid control
    always_ff @(posedge clk) begin
        if (~rstn) begin
            pcim.awvalid <= 0;
            pcim.wvalid <= 0;
        end else begin
            if (axi_aw_working) begin
                pcim.awvalid <= 1;
            end else if (axi_w_working) begin
                pcim.awvalid <= 0;
            end else begin
                pcim.awvalid <= (wb_ready && (state == INT_WRITE));
            end

            if (axi_w_working) begin
                pcim.wvalid <= 1;
            end else if (axi_aw_working) begin
                pcim.wvalid <= 0;
            end else begin
                pcim.wvalid <= (wb_ready && (state == INT_WRITE));
            end
        end
    end

    logic [15:0] tid;
    assign tid = 0;

    // AW extras
    assign pcim.awid = tid;
    assign pcim.awlen = 0;
    assign pcim.awsize = 3'b110; // 3'b110 means 64 bytes
    assign pcim.wid = tid;
    assign pcim.wstrb = -1;
    assign pcim.wlast = 1;
    assign pcim.bready = 1;
    assign pcim.arvalid = 0;
    assign pcim.rready = 1;
    assign pcim.awaddr = wb_addr;
    assign pcim.wdata = wb_data;

endmodule
