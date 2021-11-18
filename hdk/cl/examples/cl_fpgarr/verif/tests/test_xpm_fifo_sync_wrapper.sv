module test_xpm_fifo_sync_wrapper;
$error("This test is still buggy, I do not understand why, see https://support.xilinx.com/s/question/0D52E00006mCacG/problem-simulating-xpmfifosync?language=en_US&t=1637207950606 for more info");
// TEST configuration
localparam int WIDTH = 16;
localparam int DEPTH = 32;
localparam int ALMFUL_THRESHOLD = 25;
// end of TEST configuration
localparam period = 4ns;
localparam halfperiod = 2ns;

logic clk;
logic rst;
logic [WIDTH-1:0] din;
logic wr_en;
logic [WIDTH-1:0] dout;
logic rd_en;
logic dout_valid;
logic full, almful, empty;

xpm_fifo_sync_wrapper #(
    .WIDTH(WIDTH), .DEPTH(DEPTH), .ALMFUL_THRESHOLD(ALMFUL_THRESHOLD)
) xpm_fifo_sync_inst (
    .clk(clk),
    .rst(rst),
    .din(din),
    .wr_en(wr_en),
    .dout(dout),
    .rd_en(rd_en),
    .dout_valid(dout_valid),
    .full(full),
    .almful(almful),
    .empty(empty)
);
initial begin
    clk = 1;
    forever begin
    #halfperiod clk = ~clk;
    end
end

initial begin
    rst = 1;
    wr_en = 0;
    rd_en = 0;
    #(period * 10);
    rst = 0;
    #(period * 3);

    for (int i=0; i < DEPTH + 2; i++) begin
        wr_en = !full;
        #period;
    end
    wr_en = 0;
    for (int i=0; i < 10; i++) begin
        wr_en = !full;
        rd_en = !empty;
        #period;
    end
    wr_en = 0;
    rd_en = 0;
    for (int i=0; i < DEPTH + 2; i++) begin
        rd_en = !empty;
        #period;
    end
    #(period * 10);
    $finish;
end
always_ff @(posedge clk)
    if (rst)
        din <= 0;
    else
        din <= din + wr_en;
endmodule
