// ==============================================================
// Vitis HLS - High-Level Synthesis from C, C++ and OpenCL v2020.2 (64-bit)
// Copyright 1986-2020 Xilinx, Inc. All Rights Reserved.
// ==============================================================
`timescale 1 ns / 1 ps
module hashing_kernel_sha256_1_W_ram (addr0, ce0, d0, we0, q0, addr1, ce1, q1, addr2, ce2, q2, addr3, ce3, q3, addr4, ce4, q4, addr5, ce5, q5, addr6, ce6, q6, addr7, ce7, q7, addr8, ce8, q8, addr9, ce9, q9, addr10, ce10, q10, addr11, ce11, q11, addr12, ce12, q12, addr13, ce13, q13, addr14, ce14, q14, addr15, ce15, q15,  clk);

parameter DWIDTH = 32;
parameter AWIDTH = 6;
parameter MEM_SIZE = 64;

input[AWIDTH-1:0] addr0;
input ce0;
input[DWIDTH-1:0] d0;
input we0;
output reg[DWIDTH-1:0] q0;
input[AWIDTH-1:0] addr1;
input ce1;
output reg[DWIDTH-1:0] q1;
input[AWIDTH-1:0] addr2;
input ce2;
output reg[DWIDTH-1:0] q2;
input[AWIDTH-1:0] addr3;
input ce3;
output reg[DWIDTH-1:0] q3;
input[AWIDTH-1:0] addr4;
input ce4;
output reg[DWIDTH-1:0] q4;
input[AWIDTH-1:0] addr5;
input ce5;
output reg[DWIDTH-1:0] q5;
input[AWIDTH-1:0] addr6;
input ce6;
output reg[DWIDTH-1:0] q6;
input[AWIDTH-1:0] addr7;
input ce7;
output reg[DWIDTH-1:0] q7;
input[AWIDTH-1:0] addr8;
input ce8;
output reg[DWIDTH-1:0] q8;
input[AWIDTH-1:0] addr9;
input ce9;
output reg[DWIDTH-1:0] q9;
input[AWIDTH-1:0] addr10;
input ce10;
output reg[DWIDTH-1:0] q10;
input[AWIDTH-1:0] addr11;
input ce11;
output reg[DWIDTH-1:0] q11;
input[AWIDTH-1:0] addr12;
input ce12;
output reg[DWIDTH-1:0] q12;
input[AWIDTH-1:0] addr13;
input ce13;
output reg[DWIDTH-1:0] q13;
input[AWIDTH-1:0] addr14;
input ce14;
output reg[DWIDTH-1:0] q14;
input[AWIDTH-1:0] addr15;
input ce15;
output reg[DWIDTH-1:0] q15;
input clk;

reg [DWIDTH-1:0] ram0[0:MEM_SIZE-1];
reg [DWIDTH-1:0] ram1[0:MEM_SIZE-1];
reg [DWIDTH-1:0] ram2[0:MEM_SIZE-1];
reg [DWIDTH-1:0] ram3[0:MEM_SIZE-1];
reg [DWIDTH-1:0] ram4[0:MEM_SIZE-1];
reg [DWIDTH-1:0] ram5[0:MEM_SIZE-1];
reg [DWIDTH-1:0] ram6[0:MEM_SIZE-1];
reg [DWIDTH-1:0] ram7[0:MEM_SIZE-1];
reg [DWIDTH-1:0] ram8[0:MEM_SIZE-1];
reg [DWIDTH-1:0] ram9[0:MEM_SIZE-1];
reg [DWIDTH-1:0] ram10[0:MEM_SIZE-1];
reg [DWIDTH-1:0] ram11[0:MEM_SIZE-1];
reg [DWIDTH-1:0] ram12[0:MEM_SIZE-1];
reg [DWIDTH-1:0] ram13[0:MEM_SIZE-1];
reg [DWIDTH-1:0] ram14[0:MEM_SIZE-1];



always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram0[addr0] <= d0; 
        q0 <= ram0[addr0];
    end
end


always @(posedge clk)  
begin 
    if (ce1) begin
        q1 <= ram0[addr1];
    end
end


always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram1[addr0] <= d0; 
    end
end

always @(posedge clk)  
begin 
    if (ce2) begin
        q2 <= ram1[addr2];
    end
end


always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram2[addr0] <= d0; 
    end
end

always @(posedge clk)  
begin 
    if (ce3) begin
        q3 <= ram2[addr3];
    end
end


always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram3[addr0] <= d0; 
    end
end

always @(posedge clk)  
begin 
    if (ce4) begin
        q4 <= ram3[addr4];
    end
end


always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram4[addr0] <= d0; 
    end
end

always @(posedge clk)  
begin 
    if (ce5) begin
        q5 <= ram4[addr5];
    end
end


always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram5[addr0] <= d0; 
    end
end

always @(posedge clk)  
begin 
    if (ce6) begin
        q6 <= ram5[addr6];
    end
end


always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram6[addr0] <= d0; 
    end
end

always @(posedge clk)  
begin 
    if (ce7) begin
        q7 <= ram6[addr7];
    end
end


always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram7[addr0] <= d0; 
    end
end

always @(posedge clk)  
begin 
    if (ce8) begin
        q8 <= ram7[addr8];
    end
end


always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram8[addr0] <= d0; 
    end
end

always @(posedge clk)  
begin 
    if (ce9) begin
        q9 <= ram8[addr9];
    end
end


always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram9[addr0] <= d0; 
    end
end

always @(posedge clk)  
begin 
    if (ce10) begin
        q10 <= ram9[addr10];
    end
end


always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram10[addr0] <= d0; 
    end
end

always @(posedge clk)  
begin 
    if (ce11) begin
        q11 <= ram10[addr11];
    end
end


always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram11[addr0] <= d0; 
    end
end

always @(posedge clk)  
begin 
    if (ce12) begin
        q12 <= ram11[addr12];
    end
end


always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram12[addr0] <= d0; 
    end
end

always @(posedge clk)  
begin 
    if (ce13) begin
        q13 <= ram12[addr13];
    end
end


always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram13[addr0] <= d0; 
    end
end

always @(posedge clk)  
begin 
    if (ce14) begin
        q14 <= ram13[addr14];
    end
end


always @(posedge clk)  
begin 
    if (ce0) begin
        if (we0) 
            ram14[addr0] <= d0; 
    end
end

always @(posedge clk)  
begin 
    if (ce15) begin
        q15 <= ram14[addr15];
    end
end


endmodule

`timescale 1 ns / 1 ps
module hashing_kernel_sha256_1_W(
    reset,
    clk,
    address0,
    ce0,
    we0,
    d0,
    q0,
    address1,
    ce1,
    q1,
    address2,
    ce2,
    q2,
    address3,
    ce3,
    q3,
    address4,
    ce4,
    q4,
    address5,
    ce5,
    q5,
    address6,
    ce6,
    q6,
    address7,
    ce7,
    q7,
    address8,
    ce8,
    q8,
    address9,
    ce9,
    q9,
    address10,
    ce10,
    q10,
    address11,
    ce11,
    q11,
    address12,
    ce12,
    q12,
    address13,
    ce13,
    q13,
    address14,
    ce14,
    q14,
    address15,
    ce15,
    q15);

parameter DataWidth = 32'd32;
parameter AddressRange = 32'd64;
parameter AddressWidth = 32'd6;
input reset;
input clk;
input[AddressWidth - 1:0] address0;
input ce0;
input we0;
input[DataWidth - 1:0] d0;
output[DataWidth - 1:0] q0;
input[AddressWidth - 1:0] address1;
input ce1;
output[DataWidth - 1:0] q1;
input[AddressWidth - 1:0] address2;
input ce2;
output[DataWidth - 1:0] q2;
input[AddressWidth - 1:0] address3;
input ce3;
output[DataWidth - 1:0] q3;
input[AddressWidth - 1:0] address4;
input ce4;
output[DataWidth - 1:0] q4;
input[AddressWidth - 1:0] address5;
input ce5;
output[DataWidth - 1:0] q5;
input[AddressWidth - 1:0] address6;
input ce6;
output[DataWidth - 1:0] q6;
input[AddressWidth - 1:0] address7;
input ce7;
output[DataWidth - 1:0] q7;
input[AddressWidth - 1:0] address8;
input ce8;
output[DataWidth - 1:0] q8;
input[AddressWidth - 1:0] address9;
input ce9;
output[DataWidth - 1:0] q9;
input[AddressWidth - 1:0] address10;
input ce10;
output[DataWidth - 1:0] q10;
input[AddressWidth - 1:0] address11;
input ce11;
output[DataWidth - 1:0] q11;
input[AddressWidth - 1:0] address12;
input ce12;
output[DataWidth - 1:0] q12;
input[AddressWidth - 1:0] address13;
input ce13;
output[DataWidth - 1:0] q13;
input[AddressWidth - 1:0] address14;
input ce14;
output[DataWidth - 1:0] q14;
input[AddressWidth - 1:0] address15;
input ce15;
output[DataWidth - 1:0] q15;



hashing_kernel_sha256_1_W_ram hashing_kernel_sha256_1_W_ram_U(
    .clk( clk ),
    .addr0( address0 ),
    .ce0( ce0 ),
    .we0( we0 ),
    .d0( d0 ),
    .q0( q0 ),
    .addr1( address1 ),
    .ce1( ce1 ),
    .q1( q1 ),
    .addr2( address2 ),
    .ce2( ce2 ),
    .q2( q2 ),
    .addr3( address3 ),
    .ce3( ce3 ),
    .q3( q3 ),
    .addr4( address4 ),
    .ce4( ce4 ),
    .q4( q4 ),
    .addr5( address5 ),
    .ce5( ce5 ),
    .q5( q5 ),
    .addr6( address6 ),
    .ce6( ce6 ),
    .q6( q6 ),
    .addr7( address7 ),
    .ce7( ce7 ),
    .q7( q7 ),
    .addr8( address8 ),
    .ce8( ce8 ),
    .q8( q8 ),
    .addr9( address9 ),
    .ce9( ce9 ),
    .q9( q9 ),
    .addr10( address10 ),
    .ce10( ce10 ),
    .q10( q10 ),
    .addr11( address11 ),
    .ce11( ce11 ),
    .q11( q11 ),
    .addr12( address12 ),
    .ce12( ce12 ),
    .q12( q12 ),
    .addr13( address13 ),
    .ce13( ce13 ),
    .q13( q13 ),
    .addr14( address14 ),
    .ce14( ce14 ),
    .q14( q14 ),
    .addr15( address15 ),
    .ce15( ce15 ),
    .q15( q15 ));

endmodule

