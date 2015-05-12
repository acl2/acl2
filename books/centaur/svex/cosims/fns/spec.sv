


function automatic [31:0] maj (logic [31:0] a, b, c);
  maj = (a & b) | (b & c) | (a & c);
endfunction // maj

function automatic [31:0] sum (logic [31:0] a, b, c);
  sum = a ^ b ^ c;
endfunction // sum

function automatic [31:0] sum4 (logic [31:0] a, b, c, d);
  sum4 = sum(d, sum(c, b, a), maj(c, b, a));
endfunction

function automatic [31:0] maj4 (logic [31:0] a, b, c, d);
  maj4 = maj(d, sum(c, b, a), maj(c, b, a));
endfunction



module spec (input logic [127:0] in,
	     output [127:0] out);

  logic [31:0] a, b, c, d;
   assign {a, b, c, d} = in;

   assign out = { sum4(a, b, c, d), maj4(a, b, c, d) };

endmodule // spec
 
