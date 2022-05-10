// ==============================================================
// Vitis HLS - High-Level Synthesis from C, C++ and OpenCL v2020.2 (64-bit)
// Copyright 1986-2020 Xilinx, Inc. All Rights Reserved.
// ==============================================================
`timescale 1ns/1ps
module nbody_control_s_axi
#(parameter
    C_S_AXI_ADDR_WIDTH = 8,
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
    output wire [63:0]                   p_x_0,
    output wire [63:0]                   p_y_0,
    output wire [63:0]                   p_z_0,
    output wire [63:0]                   a_x_0,
    output wire [63:0]                   a_y_0,
    output wire [63:0]                   a_z_0,
    output wire [63:0]                   c_0,
    output wire [63:0]                   outer_tile_start_ptr_0,
    output wire [63:0]                   outer_tile_end_ptr_0,
    output wire [63:0]                   p_x_1,
    output wire [63:0]                   p_y_1,
    output wire [63:0]                   p_z_1,
    output wire [63:0]                   a_x_1,
    output wire [63:0]                   a_y_1,
    output wire [63:0]                   a_z_1,
    output wire [63:0]                   c_1,
    output wire [63:0]                   outer_tile_start_ptr_1,
    output wire [63:0]                   outer_tile_end_ptr_1,
    output wire [63:0]                   EPS_ptr,
    output wire [63:0]                   tiling_factor_ptr,
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
// 0x10 : Data signal of p_x_0
//        bit 31~0 - p_x_0[31:0] (Read/Write)
// 0x14 : Data signal of p_x_0
//        bit 31~0 - p_x_0[63:32] (Read/Write)
// 0x18 : reserved
// 0x1c : Data signal of p_y_0
//        bit 31~0 - p_y_0[31:0] (Read/Write)
// 0x20 : Data signal of p_y_0
//        bit 31~0 - p_y_0[63:32] (Read/Write)
// 0x24 : reserved
// 0x28 : Data signal of p_z_0
//        bit 31~0 - p_z_0[31:0] (Read/Write)
// 0x2c : Data signal of p_z_0
//        bit 31~0 - p_z_0[63:32] (Read/Write)
// 0x30 : reserved
// 0x34 : Data signal of a_x_0
//        bit 31~0 - a_x_0[31:0] (Read/Write)
// 0x38 : Data signal of a_x_0
//        bit 31~0 - a_x_0[63:32] (Read/Write)
// 0x3c : reserved
// 0x40 : Data signal of a_y_0
//        bit 31~0 - a_y_0[31:0] (Read/Write)
// 0x44 : Data signal of a_y_0
//        bit 31~0 - a_y_0[63:32] (Read/Write)
// 0x48 : reserved
// 0x4c : Data signal of a_z_0
//        bit 31~0 - a_z_0[31:0] (Read/Write)
// 0x50 : Data signal of a_z_0
//        bit 31~0 - a_z_0[63:32] (Read/Write)
// 0x54 : reserved
// 0x58 : Data signal of c_0
//        bit 31~0 - c_0[31:0] (Read/Write)
// 0x5c : Data signal of c_0
//        bit 31~0 - c_0[63:32] (Read/Write)
// 0x60 : reserved
// 0x64 : Data signal of outer_tile_start_ptr_0
//        bit 31~0 - outer_tile_start_ptr_0[31:0] (Read/Write)
// 0x68 : Data signal of outer_tile_start_ptr_0
//        bit 31~0 - outer_tile_start_ptr_0[63:32] (Read/Write)
// 0x6c : reserved
// 0x70 : Data signal of outer_tile_end_ptr_0
//        bit 31~0 - outer_tile_end_ptr_0[31:0] (Read/Write)
// 0x74 : Data signal of outer_tile_end_ptr_0
//        bit 31~0 - outer_tile_end_ptr_0[63:32] (Read/Write)
// 0x78 : reserved
// 0x7c : Data signal of p_x_1
//        bit 31~0 - p_x_1[31:0] (Read/Write)
// 0x80 : Data signal of p_x_1
//        bit 31~0 - p_x_1[63:32] (Read/Write)
// 0x84 : reserved
// 0x88 : Data signal of p_y_1
//        bit 31~0 - p_y_1[31:0] (Read/Write)
// 0x8c : Data signal of p_y_1
//        bit 31~0 - p_y_1[63:32] (Read/Write)
// 0x90 : reserved
// 0x94 : Data signal of p_z_1
//        bit 31~0 - p_z_1[31:0] (Read/Write)
// 0x98 : Data signal of p_z_1
//        bit 31~0 - p_z_1[63:32] (Read/Write)
// 0x9c : reserved
// 0xa0 : Data signal of a_x_1
//        bit 31~0 - a_x_1[31:0] (Read/Write)
// 0xa4 : Data signal of a_x_1
//        bit 31~0 - a_x_1[63:32] (Read/Write)
// 0xa8 : reserved
// 0xac : Data signal of a_y_1
//        bit 31~0 - a_y_1[31:0] (Read/Write)
// 0xb0 : Data signal of a_y_1
//        bit 31~0 - a_y_1[63:32] (Read/Write)
// 0xb4 : reserved
// 0xb8 : Data signal of a_z_1
//        bit 31~0 - a_z_1[31:0] (Read/Write)
// 0xbc : Data signal of a_z_1
//        bit 31~0 - a_z_1[63:32] (Read/Write)
// 0xc0 : reserved
// 0xc4 : Data signal of c_1
//        bit 31~0 - c_1[31:0] (Read/Write)
// 0xc8 : Data signal of c_1
//        bit 31~0 - c_1[63:32] (Read/Write)
// 0xcc : reserved
// 0xd0 : Data signal of outer_tile_start_ptr_1
//        bit 31~0 - outer_tile_start_ptr_1[31:0] (Read/Write)
// 0xd4 : Data signal of outer_tile_start_ptr_1
//        bit 31~0 - outer_tile_start_ptr_1[63:32] (Read/Write)
// 0xd8 : reserved
// 0xdc : Data signal of outer_tile_end_ptr_1
//        bit 31~0 - outer_tile_end_ptr_1[31:0] (Read/Write)
// 0xe0 : Data signal of outer_tile_end_ptr_1
//        bit 31~0 - outer_tile_end_ptr_1[63:32] (Read/Write)
// 0xe4 : reserved
// 0xe8 : Data signal of EPS_ptr
//        bit 31~0 - EPS_ptr[31:0] (Read/Write)
// 0xec : Data signal of EPS_ptr
//        bit 31~0 - EPS_ptr[63:32] (Read/Write)
// 0xf0 : reserved
// 0xf4 : Data signal of tiling_factor_ptr
//        bit 31~0 - tiling_factor_ptr[31:0] (Read/Write)
// 0xf8 : Data signal of tiling_factor_ptr
//        bit 31~0 - tiling_factor_ptr[63:32] (Read/Write)
// 0xfc : reserved
// (SC = Self Clear, COR = Clear on Read, TOW = Toggle on Write, COH = Clear on Handshake)

//------------------------Parameter----------------------
localparam
    ADDR_AP_CTRL                       = 8'h00,
    ADDR_GIE                           = 8'h04,
    ADDR_IER                           = 8'h08,
    ADDR_ISR                           = 8'h0c,
    ADDR_P_X_0_DATA_0                  = 8'h10,
    ADDR_P_X_0_DATA_1                  = 8'h14,
    ADDR_P_X_0_CTRL                    = 8'h18,
    ADDR_P_Y_0_DATA_0                  = 8'h1c,
    ADDR_P_Y_0_DATA_1                  = 8'h20,
    ADDR_P_Y_0_CTRL                    = 8'h24,
    ADDR_P_Z_0_DATA_0                  = 8'h28,
    ADDR_P_Z_0_DATA_1                  = 8'h2c,
    ADDR_P_Z_0_CTRL                    = 8'h30,
    ADDR_A_X_0_DATA_0                  = 8'h34,
    ADDR_A_X_0_DATA_1                  = 8'h38,
    ADDR_A_X_0_CTRL                    = 8'h3c,
    ADDR_A_Y_0_DATA_0                  = 8'h40,
    ADDR_A_Y_0_DATA_1                  = 8'h44,
    ADDR_A_Y_0_CTRL                    = 8'h48,
    ADDR_A_Z_0_DATA_0                  = 8'h4c,
    ADDR_A_Z_0_DATA_1                  = 8'h50,
    ADDR_A_Z_0_CTRL                    = 8'h54,
    ADDR_C_0_DATA_0                    = 8'h58,
    ADDR_C_0_DATA_1                    = 8'h5c,
    ADDR_C_0_CTRL                      = 8'h60,
    ADDR_OUTER_TILE_START_PTR_0_DATA_0 = 8'h64,
    ADDR_OUTER_TILE_START_PTR_0_DATA_1 = 8'h68,
    ADDR_OUTER_TILE_START_PTR_0_CTRL   = 8'h6c,
    ADDR_OUTER_TILE_END_PTR_0_DATA_0   = 8'h70,
    ADDR_OUTER_TILE_END_PTR_0_DATA_1   = 8'h74,
    ADDR_OUTER_TILE_END_PTR_0_CTRL     = 8'h78,
    ADDR_P_X_1_DATA_0                  = 8'h7c,
    ADDR_P_X_1_DATA_1                  = 8'h80,
    ADDR_P_X_1_CTRL                    = 8'h84,
    ADDR_P_Y_1_DATA_0                  = 8'h88,
    ADDR_P_Y_1_DATA_1                  = 8'h8c,
    ADDR_P_Y_1_CTRL                    = 8'h90,
    ADDR_P_Z_1_DATA_0                  = 8'h94,
    ADDR_P_Z_1_DATA_1                  = 8'h98,
    ADDR_P_Z_1_CTRL                    = 8'h9c,
    ADDR_A_X_1_DATA_0                  = 8'ha0,
    ADDR_A_X_1_DATA_1                  = 8'ha4,
    ADDR_A_X_1_CTRL                    = 8'ha8,
    ADDR_A_Y_1_DATA_0                  = 8'hac,
    ADDR_A_Y_1_DATA_1                  = 8'hb0,
    ADDR_A_Y_1_CTRL                    = 8'hb4,
    ADDR_A_Z_1_DATA_0                  = 8'hb8,
    ADDR_A_Z_1_DATA_1                  = 8'hbc,
    ADDR_A_Z_1_CTRL                    = 8'hc0,
    ADDR_C_1_DATA_0                    = 8'hc4,
    ADDR_C_1_DATA_1                    = 8'hc8,
    ADDR_C_1_CTRL                      = 8'hcc,
    ADDR_OUTER_TILE_START_PTR_1_DATA_0 = 8'hd0,
    ADDR_OUTER_TILE_START_PTR_1_DATA_1 = 8'hd4,
    ADDR_OUTER_TILE_START_PTR_1_CTRL   = 8'hd8,
    ADDR_OUTER_TILE_END_PTR_1_DATA_0   = 8'hdc,
    ADDR_OUTER_TILE_END_PTR_1_DATA_1   = 8'he0,
    ADDR_OUTER_TILE_END_PTR_1_CTRL     = 8'he4,
    ADDR_EPS_PTR_DATA_0                = 8'he8,
    ADDR_EPS_PTR_DATA_1                = 8'hec,
    ADDR_EPS_PTR_CTRL                  = 8'hf0,
    ADDR_TILING_FACTOR_PTR_DATA_0      = 8'hf4,
    ADDR_TILING_FACTOR_PTR_DATA_1      = 8'hf8,
    ADDR_TILING_FACTOR_PTR_CTRL        = 8'hfc,
    WRIDLE                             = 2'd0,
    WRDATA                             = 2'd1,
    WRRESP                             = 2'd2,
    WRRESET                            = 2'd3,
    RDIDLE                             = 2'd0,
    RDDATA                             = 2'd1,
    RDRESET                            = 2'd2,
    ADDR_BITS                = 8;

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
    reg  [63:0]                   int_p_x_0 = 'b0;
    reg  [63:0]                   int_p_y_0 = 'b0;
    reg  [63:0]                   int_p_z_0 = 'b0;
    reg  [63:0]                   int_a_x_0 = 'b0;
    reg  [63:0]                   int_a_y_0 = 'b0;
    reg  [63:0]                   int_a_z_0 = 'b0;
    reg  [63:0]                   int_c_0 = 'b0;
    reg  [63:0]                   int_outer_tile_start_ptr_0 = 'b0;
    reg  [63:0]                   int_outer_tile_end_ptr_0 = 'b0;
    reg  [63:0]                   int_p_x_1 = 'b0;
    reg  [63:0]                   int_p_y_1 = 'b0;
    reg  [63:0]                   int_p_z_1 = 'b0;
    reg  [63:0]                   int_a_x_1 = 'b0;
    reg  [63:0]                   int_a_y_1 = 'b0;
    reg  [63:0]                   int_a_z_1 = 'b0;
    reg  [63:0]                   int_c_1 = 'b0;
    reg  [63:0]                   int_outer_tile_start_ptr_1 = 'b0;
    reg  [63:0]                   int_outer_tile_end_ptr_1 = 'b0;
    reg  [63:0]                   int_EPS_ptr = 'b0;
    reg  [63:0]                   int_tiling_factor_ptr = 'b0;

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
                ADDR_P_X_0_DATA_0: begin
                    rdata <= int_p_x_0[31:0];
                end
                ADDR_P_X_0_DATA_1: begin
                    rdata <= int_p_x_0[63:32];
                end
                ADDR_P_Y_0_DATA_0: begin
                    rdata <= int_p_y_0[31:0];
                end
                ADDR_P_Y_0_DATA_1: begin
                    rdata <= int_p_y_0[63:32];
                end
                ADDR_P_Z_0_DATA_0: begin
                    rdata <= int_p_z_0[31:0];
                end
                ADDR_P_Z_0_DATA_1: begin
                    rdata <= int_p_z_0[63:32];
                end
                ADDR_A_X_0_DATA_0: begin
                    rdata <= int_a_x_0[31:0];
                end
                ADDR_A_X_0_DATA_1: begin
                    rdata <= int_a_x_0[63:32];
                end
                ADDR_A_Y_0_DATA_0: begin
                    rdata <= int_a_y_0[31:0];
                end
                ADDR_A_Y_0_DATA_1: begin
                    rdata <= int_a_y_0[63:32];
                end
                ADDR_A_Z_0_DATA_0: begin
                    rdata <= int_a_z_0[31:0];
                end
                ADDR_A_Z_0_DATA_1: begin
                    rdata <= int_a_z_0[63:32];
                end
                ADDR_C_0_DATA_0: begin
                    rdata <= int_c_0[31:0];
                end
                ADDR_C_0_DATA_1: begin
                    rdata <= int_c_0[63:32];
                end
                ADDR_OUTER_TILE_START_PTR_0_DATA_0: begin
                    rdata <= int_outer_tile_start_ptr_0[31:0];
                end
                ADDR_OUTER_TILE_START_PTR_0_DATA_1: begin
                    rdata <= int_outer_tile_start_ptr_0[63:32];
                end
                ADDR_OUTER_TILE_END_PTR_0_DATA_0: begin
                    rdata <= int_outer_tile_end_ptr_0[31:0];
                end
                ADDR_OUTER_TILE_END_PTR_0_DATA_1: begin
                    rdata <= int_outer_tile_end_ptr_0[63:32];
                end
                ADDR_P_X_1_DATA_0: begin
                    rdata <= int_p_x_1[31:0];
                end
                ADDR_P_X_1_DATA_1: begin
                    rdata <= int_p_x_1[63:32];
                end
                ADDR_P_Y_1_DATA_0: begin
                    rdata <= int_p_y_1[31:0];
                end
                ADDR_P_Y_1_DATA_1: begin
                    rdata <= int_p_y_1[63:32];
                end
                ADDR_P_Z_1_DATA_0: begin
                    rdata <= int_p_z_1[31:0];
                end
                ADDR_P_Z_1_DATA_1: begin
                    rdata <= int_p_z_1[63:32];
                end
                ADDR_A_X_1_DATA_0: begin
                    rdata <= int_a_x_1[31:0];
                end
                ADDR_A_X_1_DATA_1: begin
                    rdata <= int_a_x_1[63:32];
                end
                ADDR_A_Y_1_DATA_0: begin
                    rdata <= int_a_y_1[31:0];
                end
                ADDR_A_Y_1_DATA_1: begin
                    rdata <= int_a_y_1[63:32];
                end
                ADDR_A_Z_1_DATA_0: begin
                    rdata <= int_a_z_1[31:0];
                end
                ADDR_A_Z_1_DATA_1: begin
                    rdata <= int_a_z_1[63:32];
                end
                ADDR_C_1_DATA_0: begin
                    rdata <= int_c_1[31:0];
                end
                ADDR_C_1_DATA_1: begin
                    rdata <= int_c_1[63:32];
                end
                ADDR_OUTER_TILE_START_PTR_1_DATA_0: begin
                    rdata <= int_outer_tile_start_ptr_1[31:0];
                end
                ADDR_OUTER_TILE_START_PTR_1_DATA_1: begin
                    rdata <= int_outer_tile_start_ptr_1[63:32];
                end
                ADDR_OUTER_TILE_END_PTR_1_DATA_0: begin
                    rdata <= int_outer_tile_end_ptr_1[31:0];
                end
                ADDR_OUTER_TILE_END_PTR_1_DATA_1: begin
                    rdata <= int_outer_tile_end_ptr_1[63:32];
                end
                ADDR_EPS_PTR_DATA_0: begin
                    rdata <= int_EPS_ptr[31:0];
                end
                ADDR_EPS_PTR_DATA_1: begin
                    rdata <= int_EPS_ptr[63:32];
                end
                ADDR_TILING_FACTOR_PTR_DATA_0: begin
                    rdata <= int_tiling_factor_ptr[31:0];
                end
                ADDR_TILING_FACTOR_PTR_DATA_1: begin
                    rdata <= int_tiling_factor_ptr[63:32];
                end
            endcase
        end
    end
end


//------------------------Register logic-----------------
assign interrupt              = int_gie & (|int_isr);
assign ap_start               = int_ap_start;
assign int_ap_done            = ap_done;
assign ap_continue            = int_ap_continue;
assign p_x_0                  = int_p_x_0;
assign p_y_0                  = int_p_y_0;
assign p_z_0                  = int_p_z_0;
assign a_x_0                  = int_a_x_0;
assign a_y_0                  = int_a_y_0;
assign a_z_0                  = int_a_z_0;
assign c_0                    = int_c_0;
assign outer_tile_start_ptr_0 = int_outer_tile_start_ptr_0;
assign outer_tile_end_ptr_0   = int_outer_tile_end_ptr_0;
assign p_x_1                  = int_p_x_1;
assign p_y_1                  = int_p_y_1;
assign p_z_1                  = int_p_z_1;
assign a_x_1                  = int_a_x_1;
assign a_y_1                  = int_a_y_1;
assign a_z_1                  = int_a_z_1;
assign c_1                    = int_c_1;
assign outer_tile_start_ptr_1 = int_outer_tile_start_ptr_1;
assign outer_tile_end_ptr_1   = int_outer_tile_end_ptr_1;
assign EPS_ptr                = int_EPS_ptr;
assign tiling_factor_ptr      = int_tiling_factor_ptr;
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

// int_p_x_0[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_p_x_0[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_P_X_0_DATA_0)
            int_p_x_0[31:0] <= (WDATA[31:0] & wmask) | (int_p_x_0[31:0] & ~wmask);
    end
end

// int_p_x_0[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_p_x_0[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_P_X_0_DATA_1)
            int_p_x_0[63:32] <= (WDATA[31:0] & wmask) | (int_p_x_0[63:32] & ~wmask);
    end
end

// int_p_y_0[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_p_y_0[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_P_Y_0_DATA_0)
            int_p_y_0[31:0] <= (WDATA[31:0] & wmask) | (int_p_y_0[31:0] & ~wmask);
    end
end

// int_p_y_0[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_p_y_0[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_P_Y_0_DATA_1)
            int_p_y_0[63:32] <= (WDATA[31:0] & wmask) | (int_p_y_0[63:32] & ~wmask);
    end
end

// int_p_z_0[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_p_z_0[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_P_Z_0_DATA_0)
            int_p_z_0[31:0] <= (WDATA[31:0] & wmask) | (int_p_z_0[31:0] & ~wmask);
    end
end

// int_p_z_0[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_p_z_0[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_P_Z_0_DATA_1)
            int_p_z_0[63:32] <= (WDATA[31:0] & wmask) | (int_p_z_0[63:32] & ~wmask);
    end
end

// int_a_x_0[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_a_x_0[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_A_X_0_DATA_0)
            int_a_x_0[31:0] <= (WDATA[31:0] & wmask) | (int_a_x_0[31:0] & ~wmask);
    end
end

// int_a_x_0[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_a_x_0[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_A_X_0_DATA_1)
            int_a_x_0[63:32] <= (WDATA[31:0] & wmask) | (int_a_x_0[63:32] & ~wmask);
    end
end

// int_a_y_0[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_a_y_0[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_A_Y_0_DATA_0)
            int_a_y_0[31:0] <= (WDATA[31:0] & wmask) | (int_a_y_0[31:0] & ~wmask);
    end
end

// int_a_y_0[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_a_y_0[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_A_Y_0_DATA_1)
            int_a_y_0[63:32] <= (WDATA[31:0] & wmask) | (int_a_y_0[63:32] & ~wmask);
    end
end

// int_a_z_0[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_a_z_0[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_A_Z_0_DATA_0)
            int_a_z_0[31:0] <= (WDATA[31:0] & wmask) | (int_a_z_0[31:0] & ~wmask);
    end
end

// int_a_z_0[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_a_z_0[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_A_Z_0_DATA_1)
            int_a_z_0[63:32] <= (WDATA[31:0] & wmask) | (int_a_z_0[63:32] & ~wmask);
    end
end

// int_c_0[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_c_0[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_C_0_DATA_0)
            int_c_0[31:0] <= (WDATA[31:0] & wmask) | (int_c_0[31:0] & ~wmask);
    end
end

// int_c_0[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_c_0[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_C_0_DATA_1)
            int_c_0[63:32] <= (WDATA[31:0] & wmask) | (int_c_0[63:32] & ~wmask);
    end
end

// int_outer_tile_start_ptr_0[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_outer_tile_start_ptr_0[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_OUTER_TILE_START_PTR_0_DATA_0)
            int_outer_tile_start_ptr_0[31:0] <= (WDATA[31:0] & wmask) | (int_outer_tile_start_ptr_0[31:0] & ~wmask);
    end
end

// int_outer_tile_start_ptr_0[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_outer_tile_start_ptr_0[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_OUTER_TILE_START_PTR_0_DATA_1)
            int_outer_tile_start_ptr_0[63:32] <= (WDATA[31:0] & wmask) | (int_outer_tile_start_ptr_0[63:32] & ~wmask);
    end
end

// int_outer_tile_end_ptr_0[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_outer_tile_end_ptr_0[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_OUTER_TILE_END_PTR_0_DATA_0)
            int_outer_tile_end_ptr_0[31:0] <= (WDATA[31:0] & wmask) | (int_outer_tile_end_ptr_0[31:0] & ~wmask);
    end
end

// int_outer_tile_end_ptr_0[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_outer_tile_end_ptr_0[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_OUTER_TILE_END_PTR_0_DATA_1)
            int_outer_tile_end_ptr_0[63:32] <= (WDATA[31:0] & wmask) | (int_outer_tile_end_ptr_0[63:32] & ~wmask);
    end
end

// int_p_x_1[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_p_x_1[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_P_X_1_DATA_0)
            int_p_x_1[31:0] <= (WDATA[31:0] & wmask) | (int_p_x_1[31:0] & ~wmask);
    end
end

// int_p_x_1[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_p_x_1[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_P_X_1_DATA_1)
            int_p_x_1[63:32] <= (WDATA[31:0] & wmask) | (int_p_x_1[63:32] & ~wmask);
    end
end

// int_p_y_1[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_p_y_1[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_P_Y_1_DATA_0)
            int_p_y_1[31:0] <= (WDATA[31:0] & wmask) | (int_p_y_1[31:0] & ~wmask);
    end
end

// int_p_y_1[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_p_y_1[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_P_Y_1_DATA_1)
            int_p_y_1[63:32] <= (WDATA[31:0] & wmask) | (int_p_y_1[63:32] & ~wmask);
    end
end

// int_p_z_1[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_p_z_1[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_P_Z_1_DATA_0)
            int_p_z_1[31:0] <= (WDATA[31:0] & wmask) | (int_p_z_1[31:0] & ~wmask);
    end
end

// int_p_z_1[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_p_z_1[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_P_Z_1_DATA_1)
            int_p_z_1[63:32] <= (WDATA[31:0] & wmask) | (int_p_z_1[63:32] & ~wmask);
    end
end

// int_a_x_1[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_a_x_1[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_A_X_1_DATA_0)
            int_a_x_1[31:0] <= (WDATA[31:0] & wmask) | (int_a_x_1[31:0] & ~wmask);
    end
end

// int_a_x_1[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_a_x_1[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_A_X_1_DATA_1)
            int_a_x_1[63:32] <= (WDATA[31:0] & wmask) | (int_a_x_1[63:32] & ~wmask);
    end
end

// int_a_y_1[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_a_y_1[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_A_Y_1_DATA_0)
            int_a_y_1[31:0] <= (WDATA[31:0] & wmask) | (int_a_y_1[31:0] & ~wmask);
    end
end

// int_a_y_1[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_a_y_1[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_A_Y_1_DATA_1)
            int_a_y_1[63:32] <= (WDATA[31:0] & wmask) | (int_a_y_1[63:32] & ~wmask);
    end
end

// int_a_z_1[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_a_z_1[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_A_Z_1_DATA_0)
            int_a_z_1[31:0] <= (WDATA[31:0] & wmask) | (int_a_z_1[31:0] & ~wmask);
    end
end

// int_a_z_1[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_a_z_1[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_A_Z_1_DATA_1)
            int_a_z_1[63:32] <= (WDATA[31:0] & wmask) | (int_a_z_1[63:32] & ~wmask);
    end
end

// int_c_1[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_c_1[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_C_1_DATA_0)
            int_c_1[31:0] <= (WDATA[31:0] & wmask) | (int_c_1[31:0] & ~wmask);
    end
end

// int_c_1[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_c_1[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_C_1_DATA_1)
            int_c_1[63:32] <= (WDATA[31:0] & wmask) | (int_c_1[63:32] & ~wmask);
    end
end

// int_outer_tile_start_ptr_1[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_outer_tile_start_ptr_1[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_OUTER_TILE_START_PTR_1_DATA_0)
            int_outer_tile_start_ptr_1[31:0] <= (WDATA[31:0] & wmask) | (int_outer_tile_start_ptr_1[31:0] & ~wmask);
    end
end

// int_outer_tile_start_ptr_1[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_outer_tile_start_ptr_1[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_OUTER_TILE_START_PTR_1_DATA_1)
            int_outer_tile_start_ptr_1[63:32] <= (WDATA[31:0] & wmask) | (int_outer_tile_start_ptr_1[63:32] & ~wmask);
    end
end

// int_outer_tile_end_ptr_1[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_outer_tile_end_ptr_1[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_OUTER_TILE_END_PTR_1_DATA_0)
            int_outer_tile_end_ptr_1[31:0] <= (WDATA[31:0] & wmask) | (int_outer_tile_end_ptr_1[31:0] & ~wmask);
    end
end

// int_outer_tile_end_ptr_1[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_outer_tile_end_ptr_1[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_OUTER_TILE_END_PTR_1_DATA_1)
            int_outer_tile_end_ptr_1[63:32] <= (WDATA[31:0] & wmask) | (int_outer_tile_end_ptr_1[63:32] & ~wmask);
    end
end

// int_EPS_ptr[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_EPS_ptr[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_EPS_PTR_DATA_0)
            int_EPS_ptr[31:0] <= (WDATA[31:0] & wmask) | (int_EPS_ptr[31:0] & ~wmask);
    end
end

// int_EPS_ptr[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_EPS_ptr[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_EPS_PTR_DATA_1)
            int_EPS_ptr[63:32] <= (WDATA[31:0] & wmask) | (int_EPS_ptr[63:32] & ~wmask);
    end
end

// int_tiling_factor_ptr[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_tiling_factor_ptr[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_TILING_FACTOR_PTR_DATA_0)
            int_tiling_factor_ptr[31:0] <= (WDATA[31:0] & wmask) | (int_tiling_factor_ptr[31:0] & ~wmask);
    end
end

// int_tiling_factor_ptr[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_tiling_factor_ptr[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_TILING_FACTOR_PTR_DATA_1)
            int_tiling_factor_ptr[63:32] <= (WDATA[31:0] & wmask) | (int_tiling_factor_ptr[63:32] & ~wmask);
    end
end


//------------------------Memory logic-------------------

endmodule
