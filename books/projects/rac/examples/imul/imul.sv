module compress32 
   (
     output logic [63:0] out0,
     output logic [63:0] out1,
     input logic [63:0] in0,
     input logic [63:0] in1,
     input logic [63:0] in2
   );

   assign out0 = in0 ^ in1 ^ in2;
   assign out1 = ( in0 & in1 | in0 &in2 | in1 & in2 ) << 1;

endmodule : compress32
   

module compress42 
   (
     output logic [63:0] out0,
     output logic [63:0] out1,
     input logic [63:0] in0,
     input logic [63:0] in1,
     input logic [63:0] in2,
     input logic [63:0] in3
   );

  logic [63:0] temp;

  assign temp = (in1 & in2 | in1 & in3 | in2 & in3) << 1;
  assign out0 = in0 ^ in1 ^ in2 ^ in3 ^ temp;
  assign out1 = ( (in0 & ~(in0 ^ in1 ^ in2 ^ in3)) | (temp & (in0 ^ in1 ^ in2 ^ in3)) ) << 1;
     
endmodule : compress42
   
module sum 
  (
    output [63:0] out,
    input  [63:0] in [16:0]
  );

  genvar i;

  logic [63:0] level1 [7:0];

  generate
  for (i=0; i < 4; i++)
    begin : lev1
      compress42 l1 (level1[2*i+0], level1[2*i+1], in[4*i], in[4*i+1], in[4*i+2], in[4*i+3]);
    end : lev1
  endgenerate

  logic [63:0] level2 [3:0];

  generate
  for (i=0; i < 2; i++)
    begin : lev2
      compress42 l2 (level2[2*i+0], level2[2*i+1], level1[4*i], level1[4*i+1], level1[4*i+2], level1[4*i+3]);
    end : lev2
  endgenerate

  logic [63:0] level3 [1:0];

  compress42 l3 (level3[0], level3[1], level2[0], level2[1], level2[2], level2[3]);

  logic [63:0] level4 [1:0];

  compress32 l4 (level4[0], level4[1], level3[0], level3[1], in[16]);

  assign out = level4[0] + level4[1];

endmodule : sum

module imul
   (
    output logic [63:0]   prod, // unsigned product
                 
    input logic [31:0]    x,    // unsigned mulitplier will be (modified) Booth encoded
    input logic [31:0]    y     // unsigned multiplicand
    );
   
   /* **************************************************************
    
    Use modified radix-4 Booth encoding of multilplier x to form 
    the table of aligned partial products whose rows sum to the
    product x*y.
    
    ************************************************************** */

   localparam   TWIDE = 32 + 2*17 + 5;

   // ==============================================================
   // Step 1: Form bd, the r4 modified Booth digits for x.
   //
   logic [34:0]   xa;
   
   logic [16:0]   bd_2x; // magnitude 2 Booth digit
   logic [16:0]   bd_1x; // magnitude 1 Booth digit
   logic [16:0]   bd_m;  // minus Booth digit
   
   // Note that bd_m[k] = x[2k+1].
   
   always_comb
      begin
         xa = {2'h0,x,1'b0}; // xa[i] = x[i-1] with pre- and post-pended zeros.
         for (int k = 0; k < 17; k++) 
            begin: gen_mbd //                                     xa[2k+2]  xa[2k+1]  xa[2k  ] |
            //                                          m_2_1      x[2k+1]     x[2k]   x[2k-1] | bd
            casex (xa[(2*k+2)-:3]) //                            -----------------------------------
               3'b100: {bd_m[k],bd_2x[k],bd_1x[k]} = 3'b1_1_0; //     1         0        0     | -2
               3'b101: {bd_m[k],bd_2x[k],bd_1x[k]} = 3'b1_0_1; //     1         0        1     | -1
               3'b110: {bd_m[k],bd_2x[k],bd_1x[k]} = 3'b1_0_1; //     1         1        0     | -1
               3'b111: {bd_m[k],bd_2x[k],bd_1x[k]} = 3'b0_0_0; //     1         1        1     | +0
               3'b000: {bd_m[k],bd_2x[k],bd_1x[k]} = 3'b0_0_0; //     0         0        0     | +0
               3'b001: {bd_m[k],bd_2x[k],bd_1x[k]} = 3'b0_0_1; //     0         0        1     |  1
               3'b010: {bd_m[k],bd_2x[k],bd_1x[k]} = 3'b0_0_1; //     0         1        0     |  1
               3'b011: {bd_m[k],bd_2x[k],bd_1x[k]} = 3'b0_1_0; //     0         1        1     |  2
            endcase // casex(xp1[(2*k+2)-:3])
         end // for (int k = 0; k <= 12; k++)
      end // always_comb begin

   // ==============================================================
   // Step 2: Form the partial products.
   //
   logic [32:0]     pp   [16:0];
   logic [32:0]     row;

   always_comb
      begin: gen_pp
         for (int k=0; k<17; k++) 
            begin
               casex ({bd_2x[k],bd_1x[k]})
                  2'b10:   row = {y,1'b0}; // 2x multiple
                  2'b01:   row = {1'b0,y}; // 1x multiple
                  default: row = '0;
               endcase // casex({bd_2x[k],bd_1x[k]})
               pp[k] = bd_m[k] ? (~row) : (row);
            end
      end // always_comb begin

   // ==============================================================
   // Step 3: Form the table whose rows sum to the final product.
   //
   // We must ensure that bd_m[16] = '0, for otherwise the 
   // following table of partial products will have a missing 
   // two's complement +1 factor associated with the last row.

   genvar gi;
   logic [63:0]  tble [16:0];
      
   logic [(TWIDE-1):0]       tmp  [16:0];
   logic                     psb  [16:0];
   logic                     sb   [16:0];
   
   logic [17:0]             bd_m1;
   
   always_comb  bd_m1 = {bd_m,1'b0};
   
   generate
      for (gi=0; gi<17; gi++)
         begin: tble_gi
            always_comb
               begin
                  psb[gi] = bd_m1[gi];
                  sb[gi]  = bd_m[gi];
                  // TWIDE =    2*(17-gi)-1        +        2 + (32+1) + 2         +      2*gi+1
                  tmp[gi] = { {(2*(17-gi)-1){1'b0}}, {1'b1,~sb[gi]}, pp[gi], {1'b0, psb[gi]}, {(2*gi+1){1'b0}} };
                  if (gi == 0)
                     tmp[gi][(32+4)+:3] = {~sb[gi],sb[gi],sb[gi]};
                  tble[gi] = tmp[gi][3+:64];
               end // always_comb begin
         end // for
   endgenerate

   // ==============================================================
   // Step 4: Compute the product by summing the rows of the table of 
   //         aligned partial products.

   sum sum (prod, tble);

endmodule // imul
