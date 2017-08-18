

module shifted_sums (output [15:0] sum,
		     input [127:0] a,
		     input [127:0] b,
		     input [3:0] shift);

  logic [15:0][7:0] aslices;
  logic [15:0][7:0] bslices;
  logic [15:0][7:0] shifted_slices;
  logic [15:0][7:0] prods;
  logic [15:0][15:0] sums;
   assign aslices = a;
   assign bslices = b;
  
   generate
     genvar i;
     for (i=0; i<16; i=i+1) begin : shift_slice
       assign shifted_slices[i] = bslices[4'(shift+i)];
       assign prods[i] = aslices[i] * shifted_slices[i];
       assign sums[i] = prods[i] + ((i==0) ? 16'b0 : sums[i-1]);
     end

   endgenerate

   assign sum = sums[15];

endmodule
