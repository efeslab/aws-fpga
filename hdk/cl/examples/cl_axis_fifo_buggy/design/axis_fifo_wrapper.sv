module axis_fifo_wrapper #(
    parameter ADDR_WIDTH = 10,
    parameter DATA_WIDTH = 32,
    parameter USER_WIDTH = 1,
    parameter KEEP_WIDTH = (DATA_WIDTH/8)
)
(
    input logic clk,
    input logic rst,

    /*
     * AXI input
     */
    input  logic [DATA_WIDTH-1:0]  s_axis_tdata,
    input  logic [KEEP_WIDTH-1:0]  s_axis_tkeep,
    input  logic                   s_axis_tvalid,
    output logic                   s_axis_tready,
    input  logic                   s_axis_tlast,
    input  logic [USER_WIDTH-1:0]  s_axis_tuser,

    /*
     * AXI output
     */
    output logic [DATA_WIDTH-1:0]  m_axis_tdata,
    output logic [KEEP_WIDTH-1:0]  m_axis_tkeep,
    output logic                   m_axis_tvalid,
    input  logic                   m_axis_tready,
    output logic                   m_axis_tlast,
    output logic [USER_WIDTH-1:0]  m_axis_tuser,

    /*
     * Status
     */
    output logic                   status_overflow,
    output logic                   status_bad_frame,
    output logic                   status_good_frame,
    output logic                   status_empty
);

    axis_fifo #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .LAST_ENABLE(1),
        .ID_ENABLE(0),
        .DEST_ENABLE(0),
        .USER_ENABLE(1),
        .USER_WIDTH(USER_WIDTH),
        .FRAME_FIFO(1),
        .DROP_BAD_FRAME(0),
        .DROP_WHEN_FULL(0)
    ) axis_fifo_inst (
        .clk(clk),
        .rst(rst),
        .s_axis_tdata(s_axis_tdata),
        .s_axis_tkeep(s_axis_tkeep),
        .s_axis_tvalid(s_axis_tvalid),
        .s_axis_tready(s_axis_tready),
        .s_axis_tlast(s_axis_tlast),
        .s_axis_tuser(s_axis_tuser),
        .m_axis_tdata(m_axis_tdata),
        .m_axis_tvalid(m_axis_tvalid),
        .m_axis_tkeep(m_axis_tkeep),
        .m_axis_tready(m_axis_tready),
        .m_axis_tlast(m_axis_tlast),
        .m_axis_tuser(m_axis_tuser),
        .status_overflow(status_overflow),
        .status_bad_frame(status_bad_frame),
        .status_good_frame(status_good_frame),
        .status_empty(status_empty)
    );

endmodule
