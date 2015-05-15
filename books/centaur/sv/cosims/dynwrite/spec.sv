


module spec (input logic [127:0] in,
	     output logic [127:0] out);

  logic [3:0] a, b, c, d;

   assign {a, b, c, d} = in;

  logic [15:0] e;

   always_comb begin
     e = 16'b0;
     e[a] = 1'b1;
   end

  logic [3:0] f [15:0];

     int i, j, k;

   always_comb begin
     for (i=0; i<16; i++) begin
       f[i] = 0;
     end
     f[b] = c;
   end

  logic [3:0] g [15:0], h [15:0];

   always_comb begin
     for (j=0; j<16; j++) begin
       g[j] = 0;
       h[j] = 0;
     end
     {g[d], h[d]} = {a, b};
   end

   always_comb begin
     for (k=0; k<16; k++) begin
       out[4*k +: 3] = (k & 1) ? f[k] : (k & 2) ? g[k] : h[k] ;
     end
     out[79:64] = e;
   end

   // assign out = e;
endmodule // spec

