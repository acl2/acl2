
module spec (input logic [127:0] in,
	     output logic [127:0] out);


  wire [3:7] a;
  wire [7:3] b;
  wire [3:3] c;
  wire [3:0] sel;
  assign {a, b, c, sel} = in;

   // NCVerilog doesn't do well on anything that is even partially out of bounds.
  assign out = {  a[4 +: 2],
                  a[4 +: 4],
                  a[1 +: 5],
                  a[10 +: 2],
		  a[0 +: 2],
		  a[0 +: 3],
		  a[0 +: 4],
		  a[7 +: 1],
		  a[sel +: 3],
                  a[sel +: 1],

		  b[4 +: 2],
                  b[4 +: 4],
                  b[1 +: 5],
                  b[10 +: 2],
		  b[0 +: 2],
		  b[0 +: 3],
		  b[0 +: 4],
		  b[7 +: 1],
		  b[sel +: 3],
                  b[sel +: 1],

                  c[3 +: 1],
                  c[3 +: 2],

                  c[2 +: 2],
                  c[2 +: 1],
		  c[2 +: 3],
		  c[4 +: 2],
		  c[0 +: 2],
		  c[sel +: 1]
		  // VCS doesn't like this: it prints
		  //    Warning-[SIOB] Select index out of bounds
		  // but then it also gets completely wrong answers,
		  // e.g., if sel is 4'b0011 and c is 1'bx, it gets 1 somehow.
		  // c[sel +: 2]

		  };

endmodule // spec


// Test failed: input:
// 110010X1Z001110X0110011X1Z1Z1100000ZZ011ZZ0X1X101110ZX1X0ZZ01ZZ100Z1Z00ZZ000X0\
// 1000X1011Z110XX0Z110XX110ZZX10Z0Z00101001Z10XX0011

// output (spec):
// 000000000000000000000000000000000000000000000000000
//   0000000010100xx101xxxxxxxxxx101011101z1010xxxxxxxxxxxxxx110xxxxxxxxxxxxxxxxx1
//          010100xx101xxxxxxxxxx101011101z1010xxxxxxxxxxxxxx110xxxxxxxxxxxxxxxxxx

// sel = 0011
// c = x


// Test failed: input:
// 0110101Z001X001101Z0ZZ000Z10Z0ZZ0101ZX1010X010X000100Z1XZ1100Z1ZX1ZXZ0X01100XX\
// 01X11Z111011001101111Z010X10001011ZX01101101XZ0011

// output (spec):
// 0000000000000000000000000000000000000000000000000000000000
// 010110xxx01xxxxxxxxxxx0x01x01110101xxxxxxxxxxxxxx101xxzxzzxxxzxxxxxzx0
// 010110xxx01xxxxxxxxxxx0x01x01110101xxxxxxxxxxxxxx101xxzxzzxxxzxxxxxzxz

