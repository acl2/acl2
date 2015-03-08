
parameter nbits=11;

module encdec (input [nbits-1:0] in,
	       output logic [nbits-1:0] out);

  wire [(1<<nbits)-1:0] dec;

  genvar i;
   for (i=0; i<(1<<nbits); i++) begin
     assign dec[i] = in == i;
   end

  integer j;

   always_comb begin
     out='x;
     for (j=0; j<(1<<nbits); j++) begin
       if (dec[j] == 1'b1) out = j;
     end
   end

endmodule // encdec

module spec (input logic [127:0] in,
	     output wire [127:0] out);

   encdec encdecinst (in, out[nbits-1:0]);

endmodule // spec
