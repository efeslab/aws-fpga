// ==============================================================
// Vitis HLS - High-Level Synthesis from C, C++ and OpenCL v2020.2 (64-bit)
// Copyright 1986-2020 Xilinx, Inc. All Rights Reserved.
// ==============================================================
`timescale 1ns/1ps
module mobilenet_control_s_axi
#(parameter
    C_S_AXI_ADDR_WIDTH = 7,
    C_S_AXI_DATA_WIDTH = 32
)(
    input  wire                          ACLK,
    input  wire                          ARESET,
    input  wire                          ACLK_EN,
    input  wire [C_S_AXI_ADDR_WIDTH-1:0] AWADDR,
    input  wire                          AWVALID,
    output wire                          AWREADY,
    input  wire [C_S_AXI_DATA_WIDTH-1:0] WDATA,
    input  wire [C_S_AXI_DATA_WIDTH/8-1:0] WSTRB,
    input  wire                          WVALID,
    output wire                          WREADY,
    output wire [1:0]                    BRESP,
    output wire                          BVALID,
    input  wire                          BREADY,
    input  wire [C_S_AXI_ADDR_WIDTH-1:0] ARADDR,
    input  wire                          ARVALID,
    output wire                          ARREADY,
    output wire [C_S_AXI_DATA_WIDTH-1:0] RDATA,
    output wire [1:0]                    RRESP,
    output wire                          RVALID,
    input  wire                          RREADY,
    output wire                          interrupt,
    output wire [63:0]                   image_in_raw_pad,
    output wire [63:0]                   conv_weight_1x1_all,
    output wire [63:0]                   conv_weight_3x3_all,
    output wire [63:0]                   bias_all,
    output wire [63:0]                   DDR_pool3_out_PL,
    output wire [63:0]                   DDR_pool6_out_PL,
    output wire [63:0]                   DDR_buf,
    output wire [63:0]                   predict_box,
    output wire                          ap_start,
    input  wire                          ap_done,
    input  wire                          ap_ready,
    output wire                          ap_continue,
    input  wire                          ap_idle
);
//------------------------Address Info-------------------
// 0x00 : Control signals
//        bit 0  - ap_start (Read/Write/COH)
//        bit 1  - ap_done (Read)
//        bit 2  - ap_idle (Read)
//        bit 3  - ap_ready (Read)
//        bit 4  - ap_continue (Read/Write/SC)
//        bit 7  - auto_restart (Read/Write)
//        others - reserved
// 0x04 : Global Interrupt Enable Register
//        bit 0  - Global Interrupt Enable (Read/Write)
//        others - reserved
// 0x08 : IP Interrupt Enable Register (Read/Write)
//        bit 0  - enable ap_done interrupt (Read/Write)
//        bit 1  - enable ap_ready interrupt (Read/Write)
//        others - reserved
// 0x0c : IP Interrupt Status Register (Read/TOW)
//        bit 0  - ap_done (COR/TOW)
//        bit 1  - ap_ready (COR/TOW)
//        others - reserved
// 0x10 : Data signal of image_in_raw_pad
//        bit 31~0 - image_in_raw_pad[31:0] (Read/Write)
// 0x14 : Data signal of image_in_raw_pad
//        bit 31~0 - image_in_raw_pad[63:32] (Read/Write)
// 0x18 : reserved
// 0x1c : Data signal of conv_weight_1x1_all
//        bit 31~0 - conv_weight_1x1_all[31:0] (Read/Write)
// 0x20 : Data signal of conv_weight_1x1_all
//        bit 31~0 - conv_weight_1x1_all[63:32] (Read/Write)
// 0x24 : reserved
// 0x28 : Data signal of conv_weight_3x3_all
//        bit 31~0 - conv_weight_3x3_all[31:0] (Read/Write)
// 0x2c : Data signal of conv_weight_3x3_all
//        bit 31~0 - conv_weight_3x3_all[63:32] (Read/Write)
// 0x30 : reserved
// 0x34 : Data signal of bias_all
//        bit 31~0 - bias_all[31:0] (Read/Write)
// 0x38 : Data signal of bias_all
//        bit 31~0 - bias_all[63:32] (Read/Write)
// 0x3c : reserved
// 0x40 : Data signal of DDR_pool3_out_PL
//        bit 31~0 - DDR_pool3_out_PL[31:0] (Read/Write)
// 0x44 : Data signal of DDR_pool3_out_PL
//        bit 31~0 - DDR_pool3_out_PL[63:32] (Read/Write)
// 0x48 : reserved
// 0x4c : Data signal of DDR_pool6_out_PL
//        bit 31~0 - DDR_pool6_out_PL[31:0] (Read/Write)
// 0x50 : Data signal of DDR_pool6_out_PL
//        bit 31~0 - DDR_pool6_out_PL[63:32] (Read/Write)
// 0x54 : reserved
// 0x58 : Data signal of DDR_buf
//        bit 31~0 - DDR_buf[31:0] (Read/Write)
// 0x5c : Data signal of DDR_buf
//        bit 31~0 - DDR_buf[63:32] (Read/Write)
// 0x60 : reserved
// 0x64 : Data signal of predict_box
//        bit 31~0 - predict_box[31:0] (Read/Write)
// 0x68 : Data signal of predict_box
//        bit 31~0 - predict_box[63:32] (Read/Write)
// 0x6c : reserved
// (SC = Self Clear, COR = Clear on Read, TOW = Toggle on Write, COH = Clear on Handshake)

//------------------------Parameter----------------------
localparam
    ADDR_AP_CTRL                    = 7'h00,
    ADDR_GIE                        = 7'h04,
    ADDR_IER                        = 7'h08,
    ADDR_ISR                        = 7'h0c,
    ADDR_IMAGE_IN_RAW_PAD_DATA_0    = 7'h10,
    ADDR_IMAGE_IN_RAW_PAD_DATA_1    = 7'h14,
    ADDR_IMAGE_IN_RAW_PAD_CTRL      = 7'h18,
    ADDR_CONV_WEIGHT_1X1_ALL_DATA_0 = 7'h1c,
    ADDR_CONV_WEIGHT_1X1_ALL_DATA_1 = 7'h20,
    ADDR_CONV_WEIGHT_1X1_ALL_CTRL   = 7'h24,
    ADDR_CONV_WEIGHT_3X3_ALL_DATA_0 = 7'h28,
    ADDR_CONV_WEIGHT_3X3_ALL_DATA_1 = 7'h2c,
    ADDR_CONV_WEIGHT_3X3_ALL_CTRL   = 7'h30,
    ADDR_BIAS_ALL_DATA_0            = 7'h34,
    ADDR_BIAS_ALL_DATA_1            = 7'h38,
    ADDR_BIAS_ALL_CTRL              = 7'h3c,
    ADDR_DDR_POOL3_OUT_PL_DATA_0    = 7'h40,
    ADDR_DDR_POOL3_OUT_PL_DATA_1    = 7'h44,
    ADDR_DDR_POOL3_OUT_PL_CTRL      = 7'h48,
    ADDR_DDR_POOL6_OUT_PL_DATA_0    = 7'h4c,
    ADDR_DDR_POOL6_OUT_PL_DATA_1    = 7'h50,
    ADDR_DDR_POOL6_OUT_PL_CTRL      = 7'h54,
    ADDR_DDR_BUF_DATA_0             = 7'h58,
    ADDR_DDR_BUF_DATA_1             = 7'h5c,
    ADDR_DDR_BUF_CTRL               = 7'h60,
    ADDR_PREDICT_BOX_DATA_0         = 7'h64,
    ADDR_PREDICT_BOX_DATA_1         = 7'h68,
    ADDR_PREDICT_BOX_CTRL           = 7'h6c,
    WRIDLE                          = 2'd0,
    WRDATA                          = 2'd1,
    WRRESP                          = 2'd2,
    WRRESET                         = 2'd3,
    RDIDLE                          = 2'd0,
    RDDATA                          = 2'd1,
    RDRESET                         = 2'd2,
    ADDR_BITS                = 7;

//------------------------Local signal-------------------
    reg  [1:0]                    wstate = WRRESET;
    reg  [1:0]                    wnext;
    reg  [ADDR_BITS-1:0]          waddr;
    wire [C_S_AXI_DATA_WIDTH-1:0] wmask;
    wire                          aw_hs;
    wire                          w_hs;
    reg  [1:0]                    rstate = RDRESET;
    reg  [1:0]                    rnext;
    reg  [C_S_AXI_DATA_WIDTH-1:0] rdata;
    wire                          ar_hs;
    wire [ADDR_BITS-1:0]          raddr;
    // internal registers
    reg                           int_ap_idle;
    reg                           int_ap_continue;
    reg                           int_ap_ready;
    wire                          int_ap_done;
    reg                           int_ap_start = 1'b0;
    reg                           int_auto_restart = 1'b0;
    reg                           int_gie = 1'b0;
    reg  [1:0]                    int_ier = 2'b0;
    reg  [1:0]                    int_isr = 2'b0;
    reg  [63:0]                   int_image_in_raw_pad = 'b0;
    reg  [63:0]                   int_conv_weight_1x1_all = 'b0;
    reg  [63:0]                   int_conv_weight_3x3_all = 'b0;
    reg  [63:0]                   int_bias_all = 'b0;
    reg  [63:0]                   int_DDR_pool3_out_PL = 'b0;
    reg  [63:0]                   int_DDR_pool6_out_PL = 'b0;
    reg  [63:0]                   int_DDR_buf = 'b0;
    reg  [63:0]                   int_predict_box = 'b0;

//------------------------Instantiation------------------


//------------------------AXI write fsm------------------
assign AWREADY = (wstate == WRIDLE);
assign WREADY  = (wstate == WRDATA);
assign BRESP   = 2'b00;  // OKAY
assign BVALID  = (wstate == WRRESP);
assign wmask   = { {8{WSTRB[3]}}, {8{WSTRB[2]}}, {8{WSTRB[1]}}, {8{WSTRB[0]}} };
assign aw_hs   = AWVALID & AWREADY;
assign w_hs    = WVALID & WREADY;

// wstate
always @(posedge ACLK) begin
    if (ARESET)
        wstate <= WRRESET;
    else if (ACLK_EN)
        wstate <= wnext;
end

// wnext
always @(*) begin
    case (wstate)
        WRIDLE:
            if (AWVALID)
                wnext = WRDATA;
            else
                wnext = WRIDLE;
        WRDATA:
            if (WVALID)
                wnext = WRRESP;
            else
                wnext = WRDATA;
        WRRESP:
            if (BREADY)
                wnext = WRIDLE;
            else
                wnext = WRRESP;
        default:
            wnext = WRIDLE;
    endcase
end

// waddr
always @(posedge ACLK) begin
    if (ACLK_EN) begin
        if (aw_hs)
            waddr <= AWADDR[ADDR_BITS-1:0];
    end
end

//------------------------AXI read fsm-------------------
assign ARREADY = (rstate == RDIDLE);
assign RDATA   = rdata;
assign RRESP   = 2'b00;  // OKAY
assign RVALID  = (rstate == RDDATA);
assign ar_hs   = ARVALID & ARREADY;
assign raddr   = ARADDR[ADDR_BITS-1:0];

// rstate
always @(posedge ACLK) begin
    if (ARESET)
        rstate <= RDRESET;
    else if (ACLK_EN)
        rstate <= rnext;
end

// rnext
always @(*) begin
    case (rstate)
        RDIDLE:
            if (ARVALID)
                rnext = RDDATA;
            else
                rnext = RDIDLE;
        RDDATA:
            if (RREADY & RVALID)
                rnext = RDIDLE;
            else
                rnext = RDDATA;
        default:
            rnext = RDIDLE;
    endcase
end

// rdata
always @(posedge ACLK) begin
    if (ACLK_EN) begin
        if (ar_hs) begin
            rdata <= 'b0;
            case (raddr)
                ADDR_AP_CTRL: begin
                    rdata[0] <= int_ap_start;
                    rdata[1] <= int_ap_done;
                    rdata[2] <= int_ap_idle;
                    rdata[3] <= int_ap_ready;
                    rdata[4] <= int_ap_continue;
                    rdata[7] <= int_auto_restart;
                end
                ADDR_GIE: begin
                    rdata <= int_gie;
                end
                ADDR_IER: begin
                    rdata <= int_ier;
                end
                ADDR_ISR: begin
                    rdata <= int_isr;
                end
                ADDR_IMAGE_IN_RAW_PAD_DATA_0: begin
                    rdata <= int_image_in_raw_pad[31:0];
                end
                ADDR_IMAGE_IN_RAW_PAD_DATA_1: begin
                    rdata <= int_image_in_raw_pad[63:32];
                end
                ADDR_CONV_WEIGHT_1X1_ALL_DATA_0: begin
                    rdata <= int_conv_weight_1x1_all[31:0];
                end
                ADDR_CONV_WEIGHT_1X1_ALL_DATA_1: begin
                    rdata <= int_conv_weight_1x1_all[63:32];
                end
                ADDR_CONV_WEIGHT_3X3_ALL_DATA_0: begin
                    rdata <= int_conv_weight_3x3_all[31:0];
                end
                ADDR_CONV_WEIGHT_3X3_ALL_DATA_1: begin
                    rdata <= int_conv_weight_3x3_all[63:32];
                end
                ADDR_BIAS_ALL_DATA_0: begin
                    rdata <= int_bias_all[31:0];
                end
                ADDR_BIAS_ALL_DATA_1: begin
                    rdata <= int_bias_all[63:32];
                end
                ADDR_DDR_POOL3_OUT_PL_DATA_0: begin
                    rdata <= int_DDR_pool3_out_PL[31:0];
                end
                ADDR_DDR_POOL3_OUT_PL_DATA_1: begin
                    rdata <= int_DDR_pool3_out_PL[63:32];
                end
                ADDR_DDR_POOL6_OUT_PL_DATA_0: begin
                    rdata <= int_DDR_pool6_out_PL[31:0];
                end
                ADDR_DDR_POOL6_OUT_PL_DATA_1: begin
                    rdata <= int_DDR_pool6_out_PL[63:32];
                end
                ADDR_DDR_BUF_DATA_0: begin
                    rdata <= int_DDR_buf[31:0];
                end
                ADDR_DDR_BUF_DATA_1: begin
                    rdata <= int_DDR_buf[63:32];
                end
                ADDR_PREDICT_BOX_DATA_0: begin
                    rdata <= int_predict_box[31:0];
                end
                ADDR_PREDICT_BOX_DATA_1: begin
                    rdata <= int_predict_box[63:32];
                end
            endcase
        end
    end
end


//------------------------Register logic-----------------
assign interrupt           = int_gie & (|int_isr);
assign ap_start            = int_ap_start;
assign int_ap_done         = ap_done;
assign ap_continue         = int_ap_continue;
assign image_in_raw_pad    = int_image_in_raw_pad;
assign conv_weight_1x1_all = int_conv_weight_1x1_all;
assign conv_weight_3x3_all = int_conv_weight_3x3_all;
assign bias_all            = int_bias_all;
assign DDR_pool3_out_PL    = int_DDR_pool3_out_PL;
assign DDR_pool6_out_PL    = int_DDR_pool6_out_PL;
assign DDR_buf             = int_DDR_buf;
assign predict_box         = int_predict_box;
// int_ap_start
always @(posedge ACLK) begin
    if (ARESET)
        int_ap_start <= 1'b0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_AP_CTRL && WSTRB[0] && WDATA[0])
            int_ap_start <= 1'b1;
        else if (ap_ready)
            int_ap_start <= int_auto_restart; // clear on handshake/auto restart
    end
end

// int_ap_idle
always @(posedge ACLK) begin
    if (ARESET)
        int_ap_idle <= 1'b0;
    else if (ACLK_EN) begin
            int_ap_idle <= ap_idle;
    end
end

// int_ap_ready
always @(posedge ACLK) begin
    if (ARESET)
        int_ap_ready <= 1'b0;
    else if (ACLK_EN) begin
            int_ap_ready <= ap_ready;
    end
end

// int_ap_continue
always @(posedge ACLK) begin
    if (ARESET)
        int_ap_continue <= 1'b0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_AP_CTRL && WSTRB[0] && WDATA[4])
            int_ap_continue <= 1'b1;
        else if (ap_done & ~int_ap_continue & int_auto_restart)
            int_ap_continue <= 1'b1; // auto restart
        else
            int_ap_continue <= 1'b0; // self clear
    end
end

// int_auto_restart
always @(posedge ACLK) begin
    if (ARESET)
        int_auto_restart <= 1'b0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_AP_CTRL && WSTRB[0])
            int_auto_restart <=  WDATA[7];
    end
end

// int_gie
always @(posedge ACLK) begin
    if (ARESET)
        int_gie <= 1'b0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_GIE && WSTRB[0])
            int_gie <= WDATA[0];
    end
end

// int_ier
always @(posedge ACLK) begin
    if (ARESET)
        int_ier <= 1'b0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_IER && WSTRB[0])
            int_ier <= WDATA[1:0];
    end
end

// int_isr[0]
always @(posedge ACLK) begin
    if (ARESET)
        int_isr[0] <= 1'b0;
    else if (ACLK_EN) begin
        if (int_ier[0] & ap_done)
            int_isr[0] <= 1'b1;
        else if (w_hs && waddr == ADDR_ISR && WSTRB[0])
            int_isr[0] <= int_isr[0] ^ WDATA[0]; // toggle on write
    end
end

// int_isr[1]
always @(posedge ACLK) begin
    if (ARESET)
        int_isr[1] <= 1'b0;
    else if (ACLK_EN) begin
        if (int_ier[1] & ap_ready)
            int_isr[1] <= 1'b1;
        else if (w_hs && waddr == ADDR_ISR && WSTRB[0])
            int_isr[1] <= int_isr[1] ^ WDATA[1]; // toggle on write
    end
end

// int_image_in_raw_pad[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_image_in_raw_pad[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_IMAGE_IN_RAW_PAD_DATA_0)
            int_image_in_raw_pad[31:0] <= (WDATA[31:0] & wmask) | (int_image_in_raw_pad[31:0] & ~wmask);
    end
end

// int_image_in_raw_pad[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_image_in_raw_pad[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_IMAGE_IN_RAW_PAD_DATA_1)
            int_image_in_raw_pad[63:32] <= (WDATA[31:0] & wmask) | (int_image_in_raw_pad[63:32] & ~wmask);
    end
end

// int_conv_weight_1x1_all[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_conv_weight_1x1_all[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_CONV_WEIGHT_1X1_ALL_DATA_0)
            int_conv_weight_1x1_all[31:0] <= (WDATA[31:0] & wmask) | (int_conv_weight_1x1_all[31:0] & ~wmask);
    end
end

// int_conv_weight_1x1_all[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_conv_weight_1x1_all[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_CONV_WEIGHT_1X1_ALL_DATA_1)
            int_conv_weight_1x1_all[63:32] <= (WDATA[31:0] & wmask) | (int_conv_weight_1x1_all[63:32] & ~wmask);
    end
end

// int_conv_weight_3x3_all[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_conv_weight_3x3_all[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_CONV_WEIGHT_3X3_ALL_DATA_0)
            int_conv_weight_3x3_all[31:0] <= (WDATA[31:0] & wmask) | (int_conv_weight_3x3_all[31:0] & ~wmask);
    end
end

// int_conv_weight_3x3_all[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_conv_weight_3x3_all[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_CONV_WEIGHT_3X3_ALL_DATA_1)
            int_conv_weight_3x3_all[63:32] <= (WDATA[31:0] & wmask) | (int_conv_weight_3x3_all[63:32] & ~wmask);
    end
end

// int_bias_all[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_bias_all[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_BIAS_ALL_DATA_0)
            int_bias_all[31:0] <= (WDATA[31:0] & wmask) | (int_bias_all[31:0] & ~wmask);
    end
end

// int_bias_all[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_bias_all[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_BIAS_ALL_DATA_1)
            int_bias_all[63:32] <= (WDATA[31:0] & wmask) | (int_bias_all[63:32] & ~wmask);
    end
end

// int_DDR_pool3_out_PL[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_DDR_pool3_out_PL[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_DDR_POOL3_OUT_PL_DATA_0)
            int_DDR_pool3_out_PL[31:0] <= (WDATA[31:0] & wmask) | (int_DDR_pool3_out_PL[31:0] & ~wmask);
    end
end

// int_DDR_pool3_out_PL[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_DDR_pool3_out_PL[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_DDR_POOL3_OUT_PL_DATA_1)
            int_DDR_pool3_out_PL[63:32] <= (WDATA[31:0] & wmask) | (int_DDR_pool3_out_PL[63:32] & ~wmask);
    end
end

// int_DDR_pool6_out_PL[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_DDR_pool6_out_PL[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_DDR_POOL6_OUT_PL_DATA_0)
            int_DDR_pool6_out_PL[31:0] <= (WDATA[31:0] & wmask) | (int_DDR_pool6_out_PL[31:0] & ~wmask);
    end
end

// int_DDR_pool6_out_PL[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_DDR_pool6_out_PL[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_DDR_POOL6_OUT_PL_DATA_1)
            int_DDR_pool6_out_PL[63:32] <= (WDATA[31:0] & wmask) | (int_DDR_pool6_out_PL[63:32] & ~wmask);
    end
end

// int_DDR_buf[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_DDR_buf[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_DDR_BUF_DATA_0)
            int_DDR_buf[31:0] <= (WDATA[31:0] & wmask) | (int_DDR_buf[31:0] & ~wmask);
    end
end

// int_DDR_buf[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_DDR_buf[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_DDR_BUF_DATA_1)
            int_DDR_buf[63:32] <= (WDATA[31:0] & wmask) | (int_DDR_buf[63:32] & ~wmask);
    end
end

// int_predict_box[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_predict_box[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_PREDICT_BOX_DATA_0)
            int_predict_box[31:0] <= (WDATA[31:0] & wmask) | (int_predict_box[31:0] & ~wmask);
    end
end

// int_predict_box[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_predict_box[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_PREDICT_BOX_DATA_1)
            int_predict_box[63:32] <= (WDATA[31:0] & wmask) | (int_predict_box[63:32] & ~wmask);
    end
end


//------------------------Memory logic-------------------

endmodule
