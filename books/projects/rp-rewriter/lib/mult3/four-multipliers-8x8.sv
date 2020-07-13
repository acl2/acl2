module ha (
        input logic a,
        input logic b,
        output logic s,
        output logic c);
    
    assign s = a ^ b;
    assign c = a & b;
    endmodule



module fa (
        input logic x,
        input logic y,
        input logic z,
        output logic s,
        output logic c);
    
    assign s = x ^ y ^ z;
    assign c = (x & y) | (x & z) | (y & z);
    endmodule


module MERGED_8_8
  (
   input logic [7:0]  IN1,
   input logic [7:0]  IN2,
   output logic [15:0] result);

   logic [17:0]        res1, res2, res3, res4;
   
   
   DT_SB4_LF_5_5 m1 ({0, IN1[3:0]}, {0, IN2[3:0]}, res1[9:0]);
   DT_SB4_LF_5_5 m2 ({0, IN1[3:0]},
		     {IN2[7],
		      IN2[7:4]}, res2[13:4]);
   DT_SB4_LF_5_5 m3 ({IN1[7],
		      IN1[7:4]}, {0, IN2[3:0]}, res3[13:4]);
   DT_SB4_LF_5_5 m4 ({IN1[7],
		      IN1[7:4]}, 
		     {IN2[7],
		      IN2[7:4]}, res4[17:8]); 

   assign res2[3:0] = 0;
   assign res3[3:0] = 0;
   assign res4[7:0] = 0;
   
   assign res1[17:10] = 0; // sign of res1 will always be zero.
   assign res2[17:14] = {4{res2[13]}}; //sign extend
   assign res3[17:14] = {4{res3[13]}}; //sign extend
   
   assign result = res1 + res2 + res3 + res4;
   

   endmodule


module DT_SB4_LF_5_5(
        input logic [4:0] IN1,
        input logic [4:0] IN2,
        output logic [9:0] result);
    
    
// Creating Partial Products 

    wire logic const1;
    assign const1 = 1'b1;
    
    // Signed Booth Radix-4 Partial Products Row 1
    wire logic select_e_0, select_ne_0, select_2x_0, tcomp0, select_n2x_0;
    assign select_e_0 = ((~ IN1[1]) & (IN1[0] ^ 1'b0));
    assign select_ne_0 = IN1[1] &  (IN1[0] ^ 1'b0);
    assign select_2x_0 = (~ IN1[1]) & IN1[0] & 1'b0;
    assign select_n2x_0 = IN1[1] & (~ IN1[0]) & (~ 1'b0);
    wire logic pp_0_0;
    assign pp_0_0 = (select_e_0 & IN2[0] | select_2x_0 & 1'b0 | select_n2x_0 & 1'b1 | select_ne_0 & (~ IN2[0])  );
    wire logic pp_0_1;
    assign pp_0_1 = (select_e_0 & IN2[1] | select_2x_0 & IN2[0] | select_n2x_0 & (~ IN2[0]) | select_ne_0 & (~ IN2[1])  );
    wire logic pp_0_2;
    assign pp_0_2 = (select_e_0 & IN2[2] | select_2x_0 & IN2[1] | select_n2x_0 & (~ IN2[1]) | select_ne_0 & (~ IN2[2])  );
    wire logic pp_0_3;
    assign pp_0_3 = (select_e_0 & IN2[3] | select_2x_0 & IN2[2] | select_n2x_0 & (~ IN2[2]) | select_ne_0 & (~ IN2[3])  );
    wire logic pp_0_4;
    assign pp_0_4 = (select_e_0 & IN2[4] | select_2x_0 & IN2[3] | select_n2x_0 & (~ IN2[3]) | select_ne_0 & (~ IN2[4])  );
    wire logic pp_0_5;
    assign pp_0_5 = (select_e_0 & IN2[4] | select_2x_0 & IN2[4] | select_n2x_0 & (~ IN2[4]) | select_ne_0 & (~ IN2[4])  );
    wire logic pp_0_6;
    assign pp_0_6 = ~ (select_e_0 & IN2[4] | select_2x_0 & IN2[4] | select_n2x_0 & (~ IN2[4]) | select_ne_0 & (~ IN2[4])  );
    assign tcomp0 = select_ne_0 | select_n2x_0;
    
    // Signed Booth Radix-4 Partial Products Row 2
    wire logic select_e_1, select_ne_1, select_2x_1, tcomp1, select_n2x_1;
    assign select_e_1 = ((~ IN1[3]) & (IN1[2] ^ IN1[1]));
    assign select_ne_1 = IN1[3] &  (IN1[2] ^ IN1[1]);
    assign select_2x_1 = (~ IN1[3]) & IN1[2] & IN1[1];
    assign select_n2x_1 = IN1[3] & (~ IN1[2]) & (~ IN1[1]);
    wire logic pp_1_0;
    assign pp_1_0 = (select_e_1 & IN2[0] | select_2x_1 & 1'b0 | select_n2x_1 & 1'b1 | select_ne_1 & (~ IN2[0])  );
    wire logic pp_1_1;
    assign pp_1_1 = (select_e_1 & IN2[1] | select_2x_1 & IN2[0] | select_n2x_1 & (~ IN2[0]) | select_ne_1 & (~ IN2[1])  );
    wire logic pp_1_2;
    assign pp_1_2 = (select_e_1 & IN2[2] | select_2x_1 & IN2[1] | select_n2x_1 & (~ IN2[1]) | select_ne_1 & (~ IN2[2])  );
    wire logic pp_1_3;
    assign pp_1_3 = (select_e_1 & IN2[3] | select_2x_1 & IN2[2] | select_n2x_1 & (~ IN2[2]) | select_ne_1 & (~ IN2[3])  );
    wire logic pp_1_4;
    assign pp_1_4 = (select_e_1 & IN2[4] | select_2x_1 & IN2[3] | select_n2x_1 & (~ IN2[3]) | select_ne_1 & (~ IN2[4])  );
    wire logic pp_1_5;
    assign pp_1_5 = (select_e_1 & IN2[4] | select_2x_1 & IN2[4] | select_n2x_1 & (~ IN2[4]) | select_ne_1 & (~ IN2[4])  );
    wire logic pp_1_6;
    assign pp_1_6 = ~ (select_e_1 & IN2[4] | select_2x_1 & IN2[4] | select_n2x_1 & (~ IN2[4]) | select_ne_1 & (~ IN2[4])  );
    assign tcomp1 = select_ne_1 | select_n2x_1;
    
    // Signed Booth Radix-4 Partial Products Row 3
    wire logic select_e_2, select_ne_2, select_2x_2, tcomp2, select_n2x_2;
    assign select_e_2 = ((~ IN1[4]) & (IN1[4] ^ IN1[3]));
    assign select_ne_2 = IN1[4] &  (IN1[4] ^ IN1[3]);
    assign select_2x_2 = (~ IN1[4]) & IN1[4] & IN1[3];
    assign select_n2x_2 = IN1[4] & (~ IN1[4]) & (~ IN1[3]);
    wire logic pp_2_0;
    assign pp_2_0 = (select_e_2 & IN2[0] | select_2x_2 & 1'b0 | select_n2x_2 & 1'b1 | select_ne_2 & (~ IN2[0])  );
    wire logic pp_2_1;
    assign pp_2_1 = (select_e_2 & IN2[1] | select_2x_2 & IN2[0] | select_n2x_2 & (~ IN2[0]) | select_ne_2 & (~ IN2[1])  );
    wire logic pp_2_2;
    assign pp_2_2 = (select_e_2 & IN2[2] | select_2x_2 & IN2[1] | select_n2x_2 & (~ IN2[1]) | select_ne_2 & (~ IN2[2])  );
    wire logic pp_2_3;
    assign pp_2_3 = (select_e_2 & IN2[3] | select_2x_2 & IN2[2] | select_n2x_2 & (~ IN2[2]) | select_ne_2 & (~ IN2[3])  );
    wire logic pp_2_4;
    assign pp_2_4 = (select_e_2 & IN2[4] | select_2x_2 & IN2[3] | select_n2x_2 & (~ IN2[3]) | select_ne_2 & (~ IN2[4])  );
    wire logic pp_2_5;
    assign pp_2_5 = (select_e_2 & IN2[4] | select_2x_2 & IN2[4] | select_n2x_2 & (~ IN2[4]) | select_ne_2 & (~ IN2[4])  );
    wire logic pp_2_6;
    assign pp_2_6 = ~ (select_e_2 & IN2[4] | select_2x_2 & IN2[4] | select_n2x_2 & (~ IN2[4]) | select_ne_2 & (~ IN2[4])  );
    assign tcomp2 = select_ne_2 | select_n2x_2;
    
// Creating Summation Tree 

    logic s0 ,c0;
    ha ha0 (pp_0_4, pp_1_2, s0, c0);
    logic s1 ,c1;
    ha ha1 (pp_0_5, pp_1_3, s1, c1);
    logic s2 ,c2; 
    fa fa2 (pp_0_6, pp_1_4, pp_2_2, s2, c2);
    logic s3 ,c3;
    ha ha3 (const1, pp_1_5, s3, c3);
    logic s4 ,c4;
    ha ha4 (pp_0_2, pp_1_0, s4, c4);
    logic s5 ,c5;
    ha ha5 (pp_0_3, pp_1_1, s5, c5);
    logic s6 ,c6; 
    fa fa6 (pp_2_0, tcomp2, s0, s6, c6);
    logic s7 ,c7; 
    fa fa7 (pp_2_1, c0, s1, s7, c7);
    logic s8 ,c8; 
    fa fa8 (const1, c1, s2, s8, c8);
    logic s9 ,c9; 
    fa fa9 (pp_2_3, c2, s3, s9, c9);
    logic s10 ,c10; 
    fa fa10 (pp_1_6, pp_2_4, c3, s10, c10);
    logic s11 ,c11;
    ha ha11 (const1, pp_2_5, s11, c11);
    logic [10:0] adder_result;
    LF_10 final_adder ({c10, c9, c8, c7, c6, c5, c4, tcomp1, pp_0_1, pp_0_0 }, {s11, s10, s9, s8, s7, s6, s5, s4, 1'b0, tcomp0 }, adder_result );
    assign result[9:0] = adder_result[9:0];
    endmodule



module LF_10 ( 
        input logic [9:0] IN1,
        input logic [9:0] IN2,
        output logic [10:0] OUT);
    
    wire logic [9:0] p_0;
    wire logic [9:0] g_0;
    assign g_0 = IN1 & IN2;
    assign p_0 = IN1 ^ IN2;
    
    // LF stage 1
    wire logic p_1_1;
    wire logic g_1_1;
    assign p_1_1 = p_0[1] & p_0[0];
    assign g_1_1 = (p_0[1] & g_0[0]) | g_0[1];
    wire logic p_1_3;
    wire logic g_1_3;
    assign p_1_3 = p_0[3] & p_0[2];
    assign g_1_3 = (p_0[3] & g_0[2]) | g_0[3];
    wire logic p_1_5;
    wire logic g_1_5;
    assign p_1_5 = p_0[5] & p_0[4];
    assign g_1_5 = (p_0[5] & g_0[4]) | g_0[5];
    wire logic p_1_7;
    wire logic g_1_7;
    assign p_1_7 = p_0[7] & p_0[6];
    assign g_1_7 = (p_0[7] & g_0[6]) | g_0[7];
    wire logic p_1_9;
    wire logic g_1_9;
    assign p_1_9 = p_0[9] & p_0[8];
    assign g_1_9 = (p_0[9] & g_0[8]) | g_0[9];
    
    // LF stage 2
    wire logic p_2_2;
    wire logic g_2_2;
    assign p_2_2 = p_0[2] & p_1_1;
    assign g_2_2 = (p_0[2] & g_1_1) | g_0[2];
    wire logic p_2_3;
    wire logic g_2_3;
    assign p_2_3 = p_1_3 & p_1_1;
    assign g_2_3 = (p_1_3 & g_1_1) | g_1_3;
    wire logic p_2_6;
    wire logic g_2_6;
    assign p_2_6 = p_0[6] & p_1_5;
    assign g_2_6 = (p_0[6] & g_1_5) | g_0[6];
    wire logic p_2_7;
    wire logic g_2_7;
    assign p_2_7 = p_1_7 & p_1_5;
    assign g_2_7 = (p_1_7 & g_1_5) | g_1_7;
    
    // LF stage 3
    wire logic p_3_4;
    wire logic g_3_4;
    assign p_3_4 = p_0[4] & p_2_3;
    assign g_3_4 = (p_0[4] & g_2_3) | g_0[4];
    wire logic p_3_5;
    wire logic g_3_5;
    assign p_3_5 = p_1_5 & p_2_3;
    assign g_3_5 = (p_1_5 & g_2_3) | g_1_5;
    wire logic p_3_6;
    wire logic g_3_6;
    assign p_3_6 = p_2_6 & p_2_3;
    assign g_3_6 = (p_2_6 & g_2_3) | g_2_6;
    wire logic p_3_7;
    wire logic g_3_7;
    assign p_3_7 = p_2_7 & p_2_3;
    assign g_3_7 = (p_2_7 & g_2_3) | g_2_7;
    
    // LF stage 4
    wire logic p_4_8;
    wire logic g_4_8;
    assign p_4_8 = p_0[8] & p_3_7;
    assign g_4_8 = (p_0[8] & g_3_7) | g_0[8];
    wire logic p_4_9;
    wire logic g_4_9;
    assign p_4_9 = p_1_9 & p_3_7;
    assign g_4_9 = (p_1_9 & g_3_7) | g_1_9;
    
    // LF postprocess 
    assign OUT[0] = p_0[0];
    assign OUT[1] = p_0[1] ^ g_0[0];
    assign OUT[2] = p_0[2] ^ g_1_1;
    assign OUT[3] = p_0[3] ^ g_2_2;
    assign OUT[4] = p_0[4] ^ g_2_3;
    assign OUT[5] = p_0[5] ^ g_3_4;
    assign OUT[6] = p_0[6] ^ g_3_5;
    assign OUT[7] = p_0[7] ^ g_3_6;
    assign OUT[8] = p_0[8] ^ g_3_7;
    assign OUT[9] = p_0[9] ^ g_4_8;
    assign OUT[10] = g_4_9;
endmodule

