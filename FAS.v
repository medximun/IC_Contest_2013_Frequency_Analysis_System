module  FAS (data_valid, data, clk, rst, fir_d, fir_valid, fft_valid, done, freq,
 fft_d1, fft_d2, fft_d3, fft_d4, fft_d5, fft_d6, fft_d7, fft_d8,
 fft_d9, fft_d10, fft_d11, fft_d12, fft_d13, fft_d14, fft_d15, fft_d0, clk_div);
input clk, rst;
input data_valid;
input [15:0] data;
output fir_valid;
output fft_valid;
output signed  [15:0] fir_d;
output [31:0] fft_d1, fft_d2, fft_d3, fft_d4, fft_d5, fft_d6, fft_d7, fft_d8;
output [31:0] fft_d9, fft_d10, fft_d11, fft_d12, fft_d13, fft_d14, fft_d15, fft_d0;
output reg done;
output [3:0] freq;
wire signed[15:0] sp2_even, sp2_odd;
output clk_div;
wire signed[15:0] fir_d_q;
assign fir_d_q = fir_d[15]? fir_d+1:fir_d;
//module
parameter size = 16;
FIR U1(data_valid, data, clk, rst, fir_valid, fir_d);
s2p U2(fir_d_q, fir_valid, sp2_odd, sp2_even, clk, rst, s2p_valid);
R2MDC R2MDC(sp2_odd, sp2_even, clk, rst, fft_d1, fft_d0, fft_valid);
div2 U3(clk, rst, clk_div);
reg [10:0] cnt;
always @(posedge clk_div, posedge rst) begin
    if(rst)
        cnt<= 0;
    else if(fft_valid && cnt<=1024)
        cnt<=cnt+1;
    else
        cnt<= cnt;
end
always @(posedge clk_div) begin
    if(cnt==1024)
        done<=1;
    else
        done<= 0;
end
endmodule
module R2MDC (sp2_odd, sp2_even, clk, rst, fft_d1, fft_d0, fft_valid);
input clk, rst;
input signed[15:0] sp2_even, sp2_odd;
output signed [31:0] fft_d1, fft_d0;
wire[2:0] gray, bi_cnt;
wire signed[31:0] comp_mul1_out;
wire signed[31:0] coe1_I, coe1_R, coe2_I, coe2_R, coe3_R, coe3_I;
wire clk_div; 
output reg fft_valid;

wire signed[15:0] FIFO4_1_out, sw1o1, sw1o2, sec4Do, bf_out1, bf_out2;
wire signed [47:0] st1_R, st1_I;
wire signed [31:0] st1_I_out2, st1_I_out1;
wire signed [15:0]real_out1, image_out1, real_out2, image_out2;
wire  signed[63:0]FIFO2_1_out, sw2o1, sw2o2, FIFO2_2_out, bf2_out1, bf2_out2, st2_out2, df1_out, sw3o1, sw3o2, df2_out, bf3_out1, bf3_out2, st3_out2
,Do_3, Do_4, sw4o1, sw4o2, bf4_out1, bf4_out2, st1_R_out1, st1_R_out2;
`include "./dat/FIR_coefficient.dat"
`include "./dat/Real_Value_Ref.dat"
`include "./dat/Imag_Value_Ref.dat"
FIFO4 frist4D(sp2_even, FIFO4_1_out, clk_div, rst);
div2 U3(clk, rst, clk_div);
switch1 sw1(bi_cnt, sp2_odd, FIFO4_1_out, sw1o1, sw1o2);
FIFO4 sec4D(sw1o1, sec4Do, clk_div, rst);
bf bf1(sec4Do, sw1o2, bf_out1, bf_out2);
gray_counter g_cnt(clk_div, rst, gray, bi_cnt);
mul1_rom1_img mul1_rom1_img(gray, coe1_I);
mul1_rom1_real mul1_rom1_real(gray, coe1_R);
comp_mul_1 comp_mul_1(bf_out2, coe1_R, coe1_I, st1_R, st1_I);
assign st1_R_out1 = {{8{bf_out1[15]}}, bf_out1,8'd0, 32'd0};
assign st1_I_out1 = 0;
assign st1_R_out2 = {st1_R[39:8], st1_I[39:8]};
assign st1_I_out2 = st1_I[39:8];

FIFO2 FIFO2_1(st1_R_out2, FIFO2_1_out, clk_div, rst);
switch2 switch2(bi_cnt[1:0], st1_R_out1, FIFO2_1_out, sw2o1, sw2o2);
FIFO2 FIFO2_2(sw2o1, FIFO2_2_out, clk_div, rst);
bf2 BF2(FIFO2_2_out, sw2o2, bf2_out1, bf2_out2);
comp_mul_2 comp_mul_2(bf2_out2[63:32], bf2_out2[31:0], coe2_R, coe2_I, st2_out2);
mul1_rom2_img mul1_rom2_img(gray, coe2_I);
mul1_rom2_real mul1_rom2_real(gray, coe2_R);
DFF DFF1(clk_div, rst, st2_out2, df1_out);
switch3 switch3(bi_cnt[0], bf2_out1, df1_out, sw3o1, sw3o2);
DFF DFF2(clk_div, rst, sw3o1, df2_out);
bf2 BF3(df2_out, sw3o2, bf3_out1, bf3_out2);
mul1_rom3_img mul1_rom3_img(gray, coe3_I);
mul1_rom3_real mul1_rom3_real(gray, coe3_R);
comp_mul_2 comp_mul_3(bf3_out2[63:32], bf3_out2[31:0], coe3_R, coe3_I, st3_out2);
FIFO4_64 FIFO4_3(st3_out2, Do_3, clk_div, rst);
switch4 SW4(bi_cnt, bf3_out1, Do_3, sw4o1, sw4o2);
FIFO4_64 FIFO4_4(sw4o1, Do_4, clk_div, rst);
bf2 BF4(Do_4, sw4o2, bf4_out1, bf4_out2);
//*
assign real_out1  = bf4_out1[56]? bf4_out1[55:40]+1:bf4_out1[55:40];
assign image_out1 = bf4_out1[24]? bf4_out1[23:8]+1:bf4_out1[23:8];
assign real_out2  = bf4_out2[56]? bf4_out2[55:40]+1:bf4_out2[55:40];
assign image_out2 = bf4_out2[24]? bf4_out2[23:8]+1:bf4_out2[23:8];
assign fft_d0 = {real_out1, image_out1};
assign fft_d1 = {real_out2, image_out2};
//*/
/*
assign real_out1  = bf4_out1[55:40];
assign image_out1 = bf4_out1[23:8];
assign real_out2  = bf4_out2[55:40];
assign image_out2 = bf4_out2[23:8];

*/
reg [6:0] cnt;
always @(posedge clk, posedge rst) begin
    if(rst)
        fft_valid <= 0;
    else if(cnt == 7'h35)
        fft_valid <= 1;
    else
        fft_valid <= fft_valid;
end
//cnt
always @(posedge clk , posedge rst) begin
    if(rst)
        cnt<=0;
    else if(cnt <=63)
        cnt <= cnt + 1;
    else
        cnt <= cnt;
end
endmodule


module FIR (data_valid, data, clk, rst, fir_valid, fir_d);
parameter size = 16;
input signed  [size -1:0] data;
input data_valid, clk, rst;
output reg fir_valid;
output signed[size -1 :0]fir_d;
reg signed [size-1 :0] FIFO [0:30];
reg signed [35:0] mul_out [0:31];
integer i;
`include "./dat/FIR_coefficient.dat"
reg signed [31:0] add_out; 
//barrel shifter
assign fir_d = add_out[31:16];
always @(posedge clk , posedge rst) begin
    if(rst)begin
        for(i=0;i<=29;i=i+1)
            FIFO[i] <= 0;
    end
    
    else begin
    FIFO[0] <= data;
        for(i=0;i<30;i=i+1)
            FIFO[i+1] <= FIFO[i];
    end
end
//mul
integer j;
always @(*) 
    begin
        mul_out[0] = FIR_C00 * data;
    mul_out[1] = FIR_C01 * FIFO[0];
    mul_out[2] = FIR_C02 * FIFO[1];
    mul_out[3] = FIR_C03 * FIFO[2];
    mul_out[4] = FIR_C04 * FIFO[3];
    mul_out[5] = FIR_C05 * FIFO[4];
    mul_out[6] = FIR_C06 * FIFO[5];
    mul_out[7] = FIR_C07 * FIFO[6];
    mul_out[8] = FIR_C08 * FIFO[7];
    mul_out[9] = FIR_C09 * FIFO[8];
    mul_out[10] = FIR_C10 * FIFO[9];
    mul_out[11] = FIR_C11 * FIFO[10];
    mul_out[12] = FIR_C12 * FIFO[11];
    mul_out[13] = FIR_C13 * FIFO[12];
    mul_out[14] = FIR_C14 * FIFO[13];
    mul_out[15] = FIR_C15 * FIFO[14];
    mul_out[16] = FIR_C16 * FIFO[15];
    mul_out[17] = FIR_C17 * FIFO[16];
    mul_out[18] = FIR_C18 * FIFO[17];
    mul_out[19] = FIR_C19 * FIFO[18];
    mul_out[20] = FIR_C20 * FIFO[19];
    mul_out[21] = FIR_C21 * FIFO[20];
    mul_out[22] = FIR_C22 * FIFO[21];
    mul_out[23] = FIR_C23 * FIFO[22];
    mul_out[24] = FIR_C24 * FIFO[23];
    mul_out[25] = FIR_C25 * FIFO[24];
    mul_out[26] = FIR_C26 * FIFO[25];
    mul_out[27] = FIR_C27 * FIFO[26];
    mul_out[28] = FIR_C28 * FIFO[27];
    mul_out[29] = FIR_C29 * FIFO[28];
    mul_out[30] = FIR_C30 * FIFO[29];
    mul_out[31] = FIR_C31 * FIFO[30];
end 
//add

always @(*) begin
    if(data_valid)begin
        add_out = mul_out[0]+mul_out[1]+mul_out[2]+mul_out[3]+mul_out[4]+mul_out[5]+mul_out[6]+mul_out[7]+mul_out[8]+mul_out[9]
        +mul_out[10]+mul_out[11]+mul_out[12]+mul_out[13]+mul_out[14]+mul_out[15]+mul_out[16]+mul_out[17]+mul_out[18]+mul_out[19]
        +mul_out[20]+mul_out[21]+mul_out[22]+mul_out[23]+mul_out[24]+mul_out[25]+mul_out[26]+mul_out[27]+mul_out[28]+mul_out[29]
        +mul_out[30]+mul_out[31];
    end
    else
        add_out = 0;
end

//cnt
reg [5:0] cnt;
always @(posedge clk , posedge rst) begin
    if(rst)
        cnt<=0;
    else if(cnt <=31)
        cnt <= cnt + 1;
    else
        cnt <= cnt;
end
//fir_valid
always @(posedge clk, posedge rst) begin
    if(rst)
        fir_valid <= 0;
    else if(cnt==31)
        fir_valid <= 1;
end

//fft_valid


endmodule

module s2p (fir_d, fir_valid, sp2_odd, sp2_even, clk, rst, s2p_valid);
input [15:0]fir_d;
input clk, rst, fir_valid;
output reg [15:0] sp2_even, sp2_odd;
output reg s2p_valid;
reg div2;
reg [15:0] store;
always @(posedge clk, posedge rst) begin
    if(rst)
        {sp2_odd, sp2_even} <= 0;
    else  if(fir_valid && div2)
        {sp2_odd, sp2_even} <= {store, fir_d};
    else begin
        {sp2_odd, sp2_even} <= {sp2_odd, sp2_even};
    end
end    
always @(posedge clk, posedge rst) begin
    if(rst)begin
        div2 <= 0;
    end
    else  if(fir_valid)
        div2 <= ~div2;
end    
always @(posedge clk, posedge rst) begin
    if(rst)begin
        store <= 0;
    end
    else if(fir_valid && !div2)
        store <= fir_d;
    else
        store <= 0;
end  
always @(posedge clk, posedge rst) begin
    if(rst)begin
        s2p_valid <= 0;
    end
    else if(fir_valid)
        s2p_valid <= 1;
    else
        s2p_valid <= 0;
end  
endmodule

module FIFO4 (in, out, clk, rst);
parameter length  = 4;
input clk, rst;
input [15:0]in;
integer i;
output  [15:0] out;
reg [15:0]FIFO[0:length-1];
always @(posedge clk, posedge rst) begin
    if(rst)begin
        for(i=0;i <length;i=i+1)
            FIFO[i] <= 0;
    end
    else begin
        for(i = 0; i < length-1 ;i = i+1)begin
        FIFO[i+1] <= FIFO[i];
        end
        FIFO[0] <= in;
    end
end
assign out = FIFO[length-1];
endmodule

module FIFO2 (in, out, clk, rst);
parameter length  = 2;
input clk, rst;
input [63:0]in;
integer i;
output [63:0] out;
reg [63:0]FIFO[0:length-1];
always @(posedge clk, posedge rst) begin
    if(rst)begin
        for(i=0;i <length;i=i+1)
            FIFO[i] <= 0;
    end
    else begin
        for(i = 0; i < length-1;i = i+1)begin
        FIFO[i+1] <= FIFO[i];
        end
        FIFO[0] <= in;
    end
end
assign out = FIFO[length-1];
endmodule

module DFF (clk, rst, df_in, df_out);
input clk, rst;
input [63:0] df_in;
output reg[63:0] df_out;
    always @(posedge clk , posedge rst) begin
        if(rst)
            df_out<= 0;
        else
            df_out<= df_in;
    end
endmodule

module div2 (clk, rst, clk_div);
input clk, rst;
output reg clk_div;
always @(posedge clk , posedge rst) begin
    if(rst)
        clk_div <= 1'd0;
    else
        clk_div <= ~clk_div;
end
endmodule
module switch1 (gray, sp2_odd, FIFO2_1_out, sw1o1, sw1o2);
input [15:0] sp2_odd, FIFO2_1_out;
input [2:0] gray;
output reg [15:0] sw1o1, sw1o2;
always @(*) begin
    if(gray >3)begin //align the intput of buffer
        sw1o1= sp2_odd;
        sw1o2= FIFO2_1_out;
    end
    else begin
        sw1o1= FIFO2_1_out;
        sw1o2= sp2_odd;
    end
end
endmodule
module switch2 (gray, bf1_out, FIFO2_1_out, sw2o1, sw2o2);
input [63:0] bf1_out, FIFO2_1_out;
input [1:0] gray;
output reg [63:0] sw2o1, sw2o2;
always @(*) begin
    if(gray <2)begin //align the intput of buffer
        sw2o1= bf1_out;
        sw2o2= FIFO2_1_out;
    end
    else begin
        sw2o1= FIFO2_1_out;
        sw2o2= bf1_out;
    end
end
endmodule



module mul (a, b, mul_out);
input signed[15:0]a;
input signed[31:0] b;
output reg signed[47:0]mul_out;

always @(*) begin
    mul_out = a * b;
end
endmodule

module sub16bit (a, b, sub_out);
input signed[15:0]a, b;
output reg signed[16:0]sub_out;

always @(*) begin
    sub_out = a - b;
end
endmodule


module comp_mul_1 (a, c, d, st1_R, st1_I);
input signed[15:0]a; 
input signed[31:0]c, d;
output signed[47:0] st1_R, st1_I;

assign st1_R = a * c;
assign st1_I = a * d;
endmodule

module comp_add (a, b, c, d, real_out, image_out);
input signed[7:0]a, b, c, d;
output signed[7:0]real_out, image_out;

assign real_out = a + c;
assign image_out = b + d;
endmodule

module comp_sub (a, b, c, d, real_out, image_out);
input signed[7:0]a, b, c, d;
output signed[7:0]real_out, image_out;

assign real_out = a - c;
assign image_out = b - d;
endmodule
//bf
module bf (a, b, bf_out1, bf_out2);
input signed[15:0] a, b;
output signed[15:0]bf_out1, bf_out2;
bf_add bf_add1(a, b, bf_out1);
bf_sub bf_sub1(a, b, bf_out2);
endmodule

module bf_add (a, b, add_out);
input signed[15:0] a, b;
output signed [15:0]add_out;

assign add_out = a + b;
endmodule

module bf_sub (a, b, sub_out);
input signed[15:0] a, b;
output signed [15:0]sub_out;

assign sub_out = a - b;
endmodule
//rom
module mul1_rom1_real (address, coe1_R);
`include "./dat/Real_Value_Ref.dat"
input [2:0] address;
output reg [31:0]coe1_R;
always @(*) begin
case (address)
    3'b000: coe1_R = W2_R;
    3'b001: coe1_R = W4_R;
    3'b011: coe1_R = W6_R;
    3'b010: coe1_R = W1_R;
    3'b110: coe1_R = W3_R;
    3'b111: coe1_R = W5_R;
    3'b101: coe1_R = W7_R;
    3'b100: coe1_R = W0_R;
    default: coe1_R = 0;
endcase
end
endmodule
module mul1_rom1_img (address, coe1_I);
`include "./dat/Imag_Value_Ref.dat"
input [2:0] address;
output reg [31:0]coe1_I;
always @(*) begin
case (address)
    3'b000: coe1_I = W2_I;
    3'b001: coe1_I = W4_I;
    3'b011: coe1_I = W6_I;
    3'b010: coe1_I = W1_I;
    3'b110: coe1_I = W3_I;
    3'b111: coe1_I = W5_I;
    3'b101: coe1_I = W7_I;
    3'b100: coe1_I = W0_I;
    default: coe1_I = 0;
endcase
end
endmodule
//gray
module gray_counter(clk, rst, gray, bi_cnt);
input clk, rst;
output reg [2:0] gray, bi_cnt;
wire [2:0]gray_cnt;
reg [2:0] g2b_cnt;
//bi_cnt
always @(posedge clk, posedge rst) begin
if(rst)
    bi_cnt <= 3;
else
    bi_cnt <= bi_cnt +1; 
end
//bi2gray
assign gray_cnt = (bi_cnt>>1) ^ bi_cnt;
always @(posedge clk , posedge rst) begin
    if(rst)
        gray <= 0;
    else
        gray <= gray_cnt;
end
endmodule
//BF2
module bf_add_32 (a, b, add_out);
input signed[31:0] a, b;
output signed [31:0]add_out;

assign add_out = a + b;
endmodule

module bf_sub_32 (a, b, sub_out);
input signed[31:0] a, b;
output signed [31:0]sub_out;

assign sub_out = a - b;
endmodule

module bf2 (a, b, bf2_out1, bf2_out2);
input signed[63:0] a, b;
output signed[63:0]bf2_out1, bf2_out2;
bf_add_32 bf_add2_R(a[63:32], b[63:32], bf2_out1[63:32]);
bf_add_32 bf_add2_I(a[31:0], b[31:0], bf2_out1[31:0]);
bf_sub_32 bf_sub2_R(a[63:32], b[63:32], bf2_out2[63:32]);
bf_sub_32 bf_sub2_I(a[31:0], b[31:0], bf2_out2[31:0]);
endmodule
//COMPMUL2
module mul_32 (a, b, mul_out);
input signed[31:0] a;
input signed[31:0] b;
output reg signed[63:0]mul_out;

always @(*) begin
    mul_out = a * b;
end
endmodule

module bf_add_64 (a, b, add_out);
input signed[63:0] a, b;
output signed [63:0]add_out;

assign add_out = a + b;
endmodule

module bf_sub_64 (a, b, sub_out);
input signed[63:0] a, b;
output signed [63:0]sub_out;

assign sub_out = a - b;
endmodule

module comp_mul_2 (a, b, c, d, st2_out2);

input signed[31:0]a, b, c, d;
output signed[63:0] st2_out2;

wire signed [63:0] sub_out, add_out;

wire [63:0]mul_out1, mul_out2, mul_out3, mul_out4;

mul_32 mul1(a, c, mul_out1);
mul_32 mul2(b, d, mul_out2);
mul_32 mul3(b, c, mul_out3);
mul_32 mul4(a, d, mul_out4);
bf_sub_64 bf_sub_64(mul_out1, mul_out2, sub_out);
bf_add_64 bf_add_64(mul_out3, mul_out4, add_out);
assign st2_out2 = {sub_out[47:16], add_out[47:16]};
endmodule

//rom2
module mul1_rom2_real (address, coe2_R);
`include "./dat/Real_Value_Ref.dat"
input [2:0] address;
output reg [31:0]coe2_R;
always @(*) begin
case (address)
    3'b000: coe2_R = W6_R;
    3'b001: coe2_R = W0_R;
    3'b011: coe2_R = W4_R;
    3'b010: coe2_R = W0_R;
    3'b110: coe2_R = W4_R;
    3'b111: coe2_R = W2_R;
    3'b101: coe2_R = W6_R;
    3'b100: coe2_R = W2_R;
    default: coe2_R = 0;
endcase
end
endmodule
module mul1_rom2_img (address, coe2_I);
`include "./dat/Imag_Value_Ref.dat"
input [2:0] address;
output reg [31:0]coe2_I;
always @(*) begin
case (address)
    3'b000: coe2_I = W6_I;
    3'b001: coe2_I = W0_I;
    3'b011: coe2_I = W4_I;
    3'b010: coe2_I = W0_I;
    3'b110: coe2_I = W4_I;
    3'b111: coe2_I = W2_I;
    3'b101: coe2_I = W6_I;
    3'b100: coe2_I = W2_I;
    default: coe2_I = 0;
endcase
end
endmodule

//sw3
module switch3 (gray, bf2_out1, df1_out, sw3o1, sw3o2);
input [63:0] bf2_out1, df1_out;
input gray;
output reg [63:0] sw3o1, sw3o2;
always @(*) begin
    if(!gray)begin //align the intput of buffer
        sw3o1= bf2_out1;
        sw3o2= df1_out;
    end
    else begin
        sw3o1= df1_out;
        sw3o2= bf2_out1;
    end
end
endmodule




//rom3
module mul1_rom3_real (address, coe3_R);
`include "./dat/Real_Value_Ref.dat"
input [2:0] address;
output reg [31:0]coe3_R;
always @(*) begin
case (address)
    3'b000: coe3_R = W4_R;
    3'b001: coe3_R = W4_R;
    3'b011: coe3_R = W0_R;
    3'b010: coe3_R = W0_R;
    3'b110: coe3_R = W0_R;
    3'b111: coe3_R = W0_R;
    3'b101: coe3_R = W4_R;
    3'b100: coe3_R = W4_R;
    default: coe3_R = 0;
endcase
end
endmodule
module mul1_rom3_img (address, coe3_I);
`include "./dat/Imag_Value_Ref.dat"
input [2:0] address;
output reg [31:0]coe3_I;
always @(*) begin
case (address)
    3'b000: coe3_I = W4_I;
    3'b001: coe3_I = W4_I;
    3'b011: coe3_I = W0_I;
    3'b010: coe3_I = W0_I;
    3'b110: coe3_I = W0_I;
    3'b111: coe3_I = W0_I;
    3'b101: coe3_I = W4_I;
    3'b100: coe3_I = W4_I;
    default: coe3_I = 0;
endcase
end
endmodule

module switch4 (gray, sp2_odd, FIFO2_1_out, sw1o1, sw1o2);
input [63:0] sp2_odd, FIFO2_1_out;
input [2:0] gray;
output reg [63:0] sw1o1, sw1o2;
always @(*) begin
    if(gray >2 && gray <7)begin //align the intput of buffer
        sw1o1= sp2_odd;
        sw1o2= FIFO2_1_out;
    end
    else begin
        sw1o1= FIFO2_1_out;
        sw1o2= sp2_odd;
        
    end
end
endmodule



module FIFO4_64 (in, out, clk, rst);
parameter length  = 4;
input clk, rst;
input [63:0]in;
integer i;
output  [63:0] out;
reg [63:0]FIFO[0:length-1];
always @(posedge clk, posedge rst) begin
    if(rst)begin
        for(i=0;i <length;i=i+1)
            FIFO[i] <= 0;
    end
    else begin
        for(i = 0; i < length-1 ;i = i+1)begin
        FIFO[i+1] <= FIFO[i];
        end
        FIFO[0] <= in;
    end
end
assign out = FIFO[length-1];
endmodule