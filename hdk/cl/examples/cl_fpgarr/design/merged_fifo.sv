module merged_fifo #(
    parameter WIDTH, 
    parameter ALMFULL_THRESHOLD) (
    input clk,
    input rst,
    input logic [WIDTH-1:0] din,
    input logic wr_en,
    output [WIDTH-1:0] dout,
    input logic rd_en,
    output logic full,
    output logic almfull,
    output logic empty
);

    localparam PER_FIFO_WIDTH = 128;
    localparam NFIFOS = (WIDTH - 1) / PER_FIFO_WIDTH + 1;
    localparam FIFO_TOTAL_BITS = PER_FIFO_WIDTH * NFIFOS;

    logic [FIFO_TOTAL_BITS-1:0] din_wrap, dout_wrap;
    logic [PER_FIFO_WIDTH-1:0] fifo_din [NFIFOS-1:0];
    logic [PER_FIFO_WIDTH-1:0] fifo_dout [NFIFOS-1:0];
    logic fifo_full [NFIFOS-1:0];
    logic fifo_empty [NFIFOS-1:0];
    logic [$clog2(PER_FIFO_WIDTH):0] fifo_data_count [NFIFOS-1:0];

    assign din_wrap = FIFO_TOTAL_BITS'(din);
    
    always_comb begin
        for (int k = 0; k < NFIFOS; k++) begin
            fifo_din[k] = din_wrap[k*PER_FIFO_WIDTH+:PER_FIFO_WIDTH];
        end
    end

    genvar i;
    generate
        for (i = 0; i < NFIFOS; i++) begin
            fifo_128x128 fifo_inst(
                .clk(clk),
                .srst(rst),
                .din(fifo_din[i]),
                .wr_en(wr_en),
                .rd_en(rd_en),
                .dout(fifo_dout[i]),
                .full(fifo_full[i]),
                .empty(fifo_empty[i]),
                .data_count(fifo_data_count[i]),
                .wr_rst_busy(),
                .rd_rst_busy()
            );
        end
    endgenerate

    always_comb begin
        for (int k = 0; k < NFIFOS; k++) begin
            dout_wrap[k*PER_FIFO_WIDTH+:PER_FIFO_WIDTH] = fifo_dout[k];
        end
    end

    assign dout = WIDTH'(dout_wrap);
    assign full = fifo_full[0];
    assign almfull = fifo_data_count[0] >= ALMFULL_THRESHOLD;
    assign empty = fifo_empty[0];

endmodule


