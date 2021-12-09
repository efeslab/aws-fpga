// ==============================================================
// Vitis HLS - High-Level Synthesis from C, C++ and OpenCL v2020.2 (64-bit)
// Copyright 1986-2020 Xilinx, Inc. All Rights Reserved.
// ==============================================================
`timescale 1ns/1ps
module top_control_s_axi
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
    output wire [63:0]                   wt_i,
    output wire [63:0]                   kh_i,
    output wire [63:0]                   dmem_i,
    output wire [63:0]                   dmem_o,
    output wire [15:0]                   n_inputs,
    output wire [15:0]                   n_outputs,
    output wire [15:0]                   input_words,
    output wire [15:0]                   output_words,
    output wire [2:0]                    layer_mode,
    output wire [0:0]                    dmem_mode,
    output wire [1:0]                    width_mode,
    output wire [1:0]                    norm_mode,
    output wire                          ap_start,
    input  wire                          ap_done,
    input  wire                          ap_ready,
    input  wire                          ap_idle
);
//------------------------Address Info-------------------
// 0x00 : Control signals
//        bit 0  - ap_start (Read/Write/COH)
//        bit 1  - ap_done (Read/COR)
//        bit 2  - ap_idle (Read)
//        bit 3  - ap_ready (Read)
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
// 0x10 : Data signal of wt_i
//        bit 31~0 - wt_i[31:0] (Read/Write)
// 0x14 : Data signal of wt_i
//        bit 31~0 - wt_i[63:32] (Read/Write)
// 0x18 : reserved
// 0x1c : Data signal of kh_i
//        bit 31~0 - kh_i[31:0] (Read/Write)
// 0x20 : Data signal of kh_i
//        bit 31~0 - kh_i[63:32] (Read/Write)
// 0x24 : reserved
// 0x28 : Data signal of dmem_i
//        bit 31~0 - dmem_i[31:0] (Read/Write)
// 0x2c : Data signal of dmem_i
//        bit 31~0 - dmem_i[63:32] (Read/Write)
// 0x30 : reserved
// 0x34 : Data signal of dmem_o
//        bit 31~0 - dmem_o[31:0] (Read/Write)
// 0x38 : Data signal of dmem_o
//        bit 31~0 - dmem_o[63:32] (Read/Write)
// 0x3c : reserved
// 0x40 : Data signal of n_inputs
//        bit 15~0 - n_inputs[15:0] (Read/Write)
//        others   - reserved
// 0x44 : reserved
// 0x48 : Data signal of n_outputs
//        bit 15~0 - n_outputs[15:0] (Read/Write)
//        others   - reserved
// 0x4c : reserved
// 0x50 : Data signal of input_words
//        bit 15~0 - input_words[15:0] (Read/Write)
//        others   - reserved
// 0x54 : reserved
// 0x58 : Data signal of output_words
//        bit 15~0 - output_words[15:0] (Read/Write)
//        others   - reserved
// 0x5c : reserved
// 0x60 : Data signal of layer_mode
//        bit 2~0 - layer_mode[2:0] (Read/Write)
//        others  - reserved
// 0x64 : reserved
// 0x68 : Data signal of dmem_mode
//        bit 0  - dmem_mode[0] (Read/Write)
//        others - reserved
// 0x6c : reserved
// 0x70 : Data signal of width_mode
//        bit 1~0 - width_mode[1:0] (Read/Write)
//        others  - reserved
// 0x74 : reserved
// 0x78 : Data signal of norm_mode
//        bit 1~0 - norm_mode[1:0] (Read/Write)
//        others  - reserved
// 0x7c : reserved
// (SC = Self Clear, COR = Clear on Read, TOW = Toggle on Write, COH = Clear on Handshake)

//------------------------Parameter----------------------
localparam
    ADDR_AP_CTRL             = 7'h00,
    ADDR_GIE                 = 7'h04,
    ADDR_IER                 = 7'h08,
    ADDR_ISR                 = 7'h0c,
    ADDR_WT_I_DATA_0         = 7'h10,
    ADDR_WT_I_DATA_1         = 7'h14,
    ADDR_WT_I_CTRL           = 7'h18,
    ADDR_KH_I_DATA_0         = 7'h1c,
    ADDR_KH_I_DATA_1         = 7'h20,
    ADDR_KH_I_CTRL           = 7'h24,
    ADDR_DMEM_I_DATA_0       = 7'h28,
    ADDR_DMEM_I_DATA_1       = 7'h2c,
    ADDR_DMEM_I_CTRL         = 7'h30,
    ADDR_DMEM_O_DATA_0       = 7'h34,
    ADDR_DMEM_O_DATA_1       = 7'h38,
    ADDR_DMEM_O_CTRL         = 7'h3c,
    ADDR_N_INPUTS_DATA_0     = 7'h40,
    ADDR_N_INPUTS_CTRL       = 7'h44,
    ADDR_N_OUTPUTS_DATA_0    = 7'h48,
    ADDR_N_OUTPUTS_CTRL      = 7'h4c,
    ADDR_INPUT_WORDS_DATA_0  = 7'h50,
    ADDR_INPUT_WORDS_CTRL    = 7'h54,
    ADDR_OUTPUT_WORDS_DATA_0 = 7'h58,
    ADDR_OUTPUT_WORDS_CTRL   = 7'h5c,
    ADDR_LAYER_MODE_DATA_0   = 7'h60,
    ADDR_LAYER_MODE_CTRL     = 7'h64,
    ADDR_DMEM_MODE_DATA_0    = 7'h68,
    ADDR_DMEM_MODE_CTRL      = 7'h6c,
    ADDR_WIDTH_MODE_DATA_0   = 7'h70,
    ADDR_WIDTH_MODE_CTRL     = 7'h74,
    ADDR_NORM_MODE_DATA_0    = 7'h78,
    ADDR_NORM_MODE_CTRL      = 7'h7c,
    WRIDLE                   = 2'd0,
    WRDATA                   = 2'd1,
    WRRESP                   = 2'd2,
    WRRESET                  = 2'd3,
    RDIDLE                   = 2'd0,
    RDDATA                   = 2'd1,
    RDRESET                  = 2'd2,
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
    reg                           int_ap_ready;
    reg                           int_ap_done = 1'b0;
    reg                           int_ap_start = 1'b0;
    reg                           int_auto_restart = 1'b0;
    reg                           int_gie = 1'b0;
    reg  [1:0]                    int_ier = 2'b0;
    reg  [1:0]                    int_isr = 2'b0;
    reg  [63:0]                   int_wt_i = 'b0;
    reg  [63:0]                   int_kh_i = 'b0;
    reg  [63:0]                   int_dmem_i = 'b0;
    reg  [63:0]                   int_dmem_o = 'b0;
    reg  [15:0]                   int_n_inputs = 'b0;
    reg  [15:0]                   int_n_outputs = 'b0;
    reg  [15:0]                   int_input_words = 'b0;
    reg  [15:0]                   int_output_words = 'b0;
    reg  [2:0]                    int_layer_mode = 'b0;
    reg  [0:0]                    int_dmem_mode = 'b0;
    reg  [1:0]                    int_width_mode = 'b0;
    reg  [1:0]                    int_norm_mode = 'b0;

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
                ADDR_WT_I_DATA_0: begin
                    rdata <= int_wt_i[31:0];
                end
                ADDR_WT_I_DATA_1: begin
                    rdata <= int_wt_i[63:32];
                end
                ADDR_KH_I_DATA_0: begin
                    rdata <= int_kh_i[31:0];
                end
                ADDR_KH_I_DATA_1: begin
                    rdata <= int_kh_i[63:32];
                end
                ADDR_DMEM_I_DATA_0: begin
                    rdata <= int_dmem_i[31:0];
                end
                ADDR_DMEM_I_DATA_1: begin
                    rdata <= int_dmem_i[63:32];
                end
                ADDR_DMEM_O_DATA_0: begin
                    rdata <= int_dmem_o[31:0];
                end
                ADDR_DMEM_O_DATA_1: begin
                    rdata <= int_dmem_o[63:32];
                end
                ADDR_N_INPUTS_DATA_0: begin
                    rdata <= int_n_inputs[15:0];
                end
                ADDR_N_OUTPUTS_DATA_0: begin
                    rdata <= int_n_outputs[15:0];
                end
                ADDR_INPUT_WORDS_DATA_0: begin
                    rdata <= int_input_words[15:0];
                end
                ADDR_OUTPUT_WORDS_DATA_0: begin
                    rdata <= int_output_words[15:0];
                end
                ADDR_LAYER_MODE_DATA_0: begin
                    rdata <= int_layer_mode[2:0];
                end
                ADDR_DMEM_MODE_DATA_0: begin
                    rdata <= int_dmem_mode[0:0];
                end
                ADDR_WIDTH_MODE_DATA_0: begin
                    rdata <= int_width_mode[1:0];
                end
                ADDR_NORM_MODE_DATA_0: begin
                    rdata <= int_norm_mode[1:0];
                end
            endcase
        end
    end
end


//------------------------Register logic-----------------
assign interrupt    = int_gie & (|int_isr);
assign ap_start     = int_ap_start;
assign wt_i         = int_wt_i;
assign kh_i         = int_kh_i;
assign dmem_i       = int_dmem_i;
assign dmem_o       = int_dmem_o;
assign n_inputs     = int_n_inputs;
assign n_outputs    = int_n_outputs;
assign input_words  = int_input_words;
assign output_words = int_output_words;
assign layer_mode   = int_layer_mode;
assign dmem_mode    = int_dmem_mode;
assign width_mode   = int_width_mode;
assign norm_mode    = int_norm_mode;
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

// int_ap_done
always @(posedge ACLK) begin
    if (ARESET)
        int_ap_done <= 1'b0;
    else if (ACLK_EN) begin
        if (ap_done)
            int_ap_done <= 1'b1;
        else if (ar_hs && raddr == ADDR_AP_CTRL)
            int_ap_done <= 1'b0; // clear on read
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

// int_wt_i[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_wt_i[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_WT_I_DATA_0)
            int_wt_i[31:0] <= (WDATA[31:0] & wmask) | (int_wt_i[31:0] & ~wmask);
    end
end

// int_wt_i[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_wt_i[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_WT_I_DATA_1)
            int_wt_i[63:32] <= (WDATA[31:0] & wmask) | (int_wt_i[63:32] & ~wmask);
    end
end

// int_kh_i[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_kh_i[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_KH_I_DATA_0)
            int_kh_i[31:0] <= (WDATA[31:0] & wmask) | (int_kh_i[31:0] & ~wmask);
    end
end

// int_kh_i[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_kh_i[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_KH_I_DATA_1)
            int_kh_i[63:32] <= (WDATA[31:0] & wmask) | (int_kh_i[63:32] & ~wmask);
    end
end

// int_dmem_i[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_dmem_i[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_DMEM_I_DATA_0)
            int_dmem_i[31:0] <= (WDATA[31:0] & wmask) | (int_dmem_i[31:0] & ~wmask);
    end
end

// int_dmem_i[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_dmem_i[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_DMEM_I_DATA_1)
            int_dmem_i[63:32] <= (WDATA[31:0] & wmask) | (int_dmem_i[63:32] & ~wmask);
    end
end

// int_dmem_o[31:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_dmem_o[31:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_DMEM_O_DATA_0)
            int_dmem_o[31:0] <= (WDATA[31:0] & wmask) | (int_dmem_o[31:0] & ~wmask);
    end
end

// int_dmem_o[63:32]
always @(posedge ACLK) begin
    if (ARESET)
        int_dmem_o[63:32] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_DMEM_O_DATA_1)
            int_dmem_o[63:32] <= (WDATA[31:0] & wmask) | (int_dmem_o[63:32] & ~wmask);
    end
end

// int_n_inputs[15:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_n_inputs[15:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_N_INPUTS_DATA_0)
            int_n_inputs[15:0] <= (WDATA[31:0] & wmask) | (int_n_inputs[15:0] & ~wmask);
    end
end

// int_n_outputs[15:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_n_outputs[15:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_N_OUTPUTS_DATA_0)
            int_n_outputs[15:0] <= (WDATA[31:0] & wmask) | (int_n_outputs[15:0] & ~wmask);
    end
end

// int_input_words[15:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_input_words[15:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_INPUT_WORDS_DATA_0)
            int_input_words[15:0] <= (WDATA[31:0] & wmask) | (int_input_words[15:0] & ~wmask);
    end
end

// int_output_words[15:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_output_words[15:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_OUTPUT_WORDS_DATA_0)
            int_output_words[15:0] <= (WDATA[31:0] & wmask) | (int_output_words[15:0] & ~wmask);
    end
end

// int_layer_mode[2:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_layer_mode[2:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_LAYER_MODE_DATA_0)
            int_layer_mode[2:0] <= (WDATA[31:0] & wmask) | (int_layer_mode[2:0] & ~wmask);
    end
end

// int_dmem_mode[0:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_dmem_mode[0:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_DMEM_MODE_DATA_0)
            int_dmem_mode[0:0] <= (WDATA[31:0] & wmask) | (int_dmem_mode[0:0] & ~wmask);
    end
end

// int_width_mode[1:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_width_mode[1:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_WIDTH_MODE_DATA_0)
            int_width_mode[1:0] <= (WDATA[31:0] & wmask) | (int_width_mode[1:0] & ~wmask);
    end
end

// int_norm_mode[1:0]
always @(posedge ACLK) begin
    if (ARESET)
        int_norm_mode[1:0] <= 0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_NORM_MODE_DATA_0)
            int_norm_mode[1:0] <= (WDATA[31:0] & wmask) | (int_norm_mode[1:0] & ~wmask);
    end
end


//------------------------Memory logic-------------------

endmodule
