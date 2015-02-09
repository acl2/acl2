// VL 2014 -- Verilog Toolkit, 2014 Edition
// Copyright (C) 2008-2015 Centaur Technology
//
// Contact:
//   Centaur Technology Formal Verification Group
//   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
//   http://www.centtech.com/
//
// License: (An MIT/X11-style license)
//
//   Permission is hereby granted, free of charge, to any person obtaining a
//   copy of this software and associated documentation files (the "Software"),
//   to deal in the Software without restriction, including without limitation
//   the rights to use, copy, modify, merge, publish, distribute, sublicense,
//   and/or sell copies of the Software, and to permit persons to whom the
//   Software is furnished to do so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in
//   all copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
//   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>


// basic tests of binary operator translations

// Notes.
//   - These are just same-size tests
//   - Not yet implemented: /, %, **, <<<. >>>


module binary_ops_test (

src1,
src2,

// unsigned tests

out_plus,   // src1 + src2         N-bit outputs
out_minus,  // src1 - src2
out_shl,    // src1 << src2
out_shr,    // src1 >> src2
out_mult,   // src1 * src2
out_bitand, // src1 & src2
out_xor,    // src1 ^ src2
out_xnor1,  // src1 ^~ src2
out_xnor2,  // src1 ~^ src2
out_bitor,  // src1 | src2

out_lt,     // src1 < src2         1-bit outputs
out_lte,    // src1 <= src2
out_gt,     // src1 > src2
out_gte,    // src1 >= src2
out_eq,     // src1 == src2
out_neq,    // src1 != src2
out_logand, // src1 && src2
out_logor,  // src1 || src2
out_ceq,    // src1 === src2
out_cne,    // src1 !== src2

// signed tests

sout_plus,   // src1 + src2         N-bit outputs
sout_minus,  // src1 - src2
sout_shl,    // src1 << src2
sout_shr,    // src1 >> src2
sout_mult,   // src1 * src2
sout_bitand, // src1 & src2
sout_xor,    // src1 ^ src2
sout_xnor1,  // src1 ^~ src2
sout_xnor2,  // src1 ~^ src2
sout_bitor,  // src1 | src2

sout_lt,     // src1 < src2         1-bit outputs
sout_lte,    // src1 <= src2
sout_gt,     // src1 > src2
sout_gte,    // src1 >= src2
sout_eq,     // src1 == src2
sout_neq,    // src1 != src2
sout_logand, // src1 && src2
sout_logor,  // src1 || src2
sout_ceq,    // src1 === src2
sout_cne     // src1 !== src2

);

   parameter size = 1;

   input [size-1:0] src1;
   input [size-1:0] src2;

   output [size-1:0] out_plus ;
   output [size-1:0] out_minus ;
   output [size-1:0] out_shl ;
   output [size-1:0] out_shr ;
   output [size-1:0] out_mult ;
   output [size-1:0] out_bitand ;
   output [size-1:0] out_xor ;
   output [size-1:0] out_xnor1 ;
   output [size-1:0] out_xnor2 ;
   output [size-1:0] out_bitor ;

   output out_lt ;
   output out_lte ;
   output out_gt ;
   output out_gte ;
   output out_eq ;
   output out_neq ;
   output out_logand ;
   output out_logor ;
   output out_ceq ;
   output out_cne ;

   assign out_plus = src1 + src2 ;
   assign out_minus = src1 - src2 ;
   assign out_shl = src1 << src2 ;
   assign out_shr = src1 >> src2 ;
   assign out_mult = src1 * src2 ;
   assign out_bitand = src1 & src2 ;
   assign out_xor = src1 ^ src2 ;
   assign out_xnor1 = src1 ^~ src2 ;
   assign out_xnor2 = src1 ~^ src2 ;
   assign out_bitor = src1 | src2 ;

   assign out_lt = src1 < src2 ;
   assign out_lte = src1 <= src2 ;
   assign out_gt = src1 > src2 ;
   assign out_gte = src1 >= src2 ;
   assign out_eq = src1 == src2 ;
   assign out_neq = src1 != src2 ;
   assign out_logand = src1 && src2 ;
   assign out_logor = src1 || src2 ;
   assign out_ceq = src1 === src2;
   assign out_cne = src1 !== src2;


   output [size-1:0] sout_plus ;
   output [size-1:0] sout_minus ;
   output [size-1:0] sout_shl ;
   output [size-1:0] sout_shr ;
   output [size-1:0] sout_mult ;
   output [size-1:0] sout_bitand ;
   output [size-1:0] sout_xor ;
   output [size-1:0] sout_xnor1 ;
   output [size-1:0] sout_xnor2 ;
   output [size-1:0] sout_bitor ;

   output sout_lt ;
   output sout_lte ;
   output sout_gt ;
   output sout_gte ;
   output sout_eq ;
   output sout_neq ;
   output sout_logand ;
   output sout_logor ;
   output sout_ceq ;
   output sout_cne ;

   wire signed [size-1:0] ssrc1; assign ssrc1 = src1;
   wire signed [size-1:0] ssrc2; assign ssrc2 = src2;

   assign sout_plus = ssrc1 + ssrc2 ;
   assign sout_minus = ssrc1 - ssrc2 ;
   assign sout_shl = ssrc1 << ssrc2 ;
   assign sout_shr = ssrc1 >> ssrc2 ;
   assign sout_mult = ssrc1 * ssrc2 ;
   assign sout_bitand = ssrc1 & ssrc2 ;
   assign sout_xor = ssrc1 ^ ssrc2 ;
   assign sout_xnor1 = ssrc1 ^~ ssrc2 ;
   assign sout_xnor2 = ssrc1 ~^ ssrc2 ;
   assign sout_bitor = ssrc1 | ssrc2 ;

   assign sout_lt = ssrc1 < ssrc2 ;
   assign sout_lte = ssrc1 <= ssrc2 ;
   assign sout_gt = ssrc1 > ssrc2 ;
   assign sout_gte = ssrc1 >= ssrc2 ;
   assign sout_eq = ssrc1 == ssrc2 ;
   assign sout_neq = ssrc1 != ssrc2 ;
   assign sout_logand = ssrc1 && ssrc2 ;
   assign sout_logor = ssrc1 || ssrc2 ;
   assign sout_ceq = ssrc1 === ssrc2;
   assign sout_cne = ssrc1 !== ssrc2;

endmodule


/*+VL

module make_tests () ;

   wire [100:0] w;
   wire a;

   binary_ops_test #(1) binary_test_1 (1'b0, 1'b0,

			  w[0:0], w[0:0], w[0:0], w[0:0], w[0:0],
			  w[0:0], w[0:0], w[0:0], w[0:0], w[0:0],
			  a, a, a, a, a, a, a, a, a, a,

			  w[0:0], w[0:0], w[0:0], w[0:0], w[0:0],
			  w[0:0], w[0:0], w[0:0], w[0:0], w[0:0],
			  a, a, a, a, a, a, a, a, a, a
			  );

   binary_ops_test #(2) binary_test_2 (2'b0, 2'b0,

			  w[1:0], w[1:0], w[1:0], w[1:0], w[1:0],
			  w[1:0], w[1:0], w[1:0], w[1:0], w[1:0],
			  a, a, a, a, a, a, a, a, a, a,

			  w[1:0], w[1:0], w[1:0], w[1:0], w[1:0],
			  w[1:0], w[1:0], w[1:0], w[1:0], w[1:0],
			  a, a, a, a, a, a, a, a, a, a
			  );

   binary_ops_test #(3) binary_test_3 (3'b0, 3'b0,

			  w[2:0], w[2:0], w[2:0], w[2:0], w[2:0],
			  w[2:0], w[2:0], w[2:0], w[2:0], w[2:0],
			  a, a, a, a, a, a, a, a, a, a,

			  w[2:0], w[2:0], w[2:0], w[2:0], w[2:0],
			  w[2:0], w[2:0], w[2:0], w[2:0], w[2:0],
			  a, a, a, a, a, a, a, a, a, a
			  );

   binary_ops_test #(4) binary_test_4 (4'b0, 4'b0,

			  w[3:0], w[3:0], w[3:0], w[3:0], w[3:0],
			  w[3:0], w[3:0], w[3:0], w[3:0], w[3:0],
			  a, a, a, a, a, a, a, a, a, a,

			  w[3:0], w[3:0], w[3:0], w[3:0], w[3:0],
			  w[3:0], w[3:0], w[3:0], w[3:0], w[3:0],
			  a, a, a, a, a, a, a, a, a, a
			  );

   binary_ops_test #(5) binary_test_5 (5'b0, 5'b0,

			  w[4:0], w[4:0], w[4:0], w[4:0], w[4:0],
			  w[4:0], w[4:0], w[4:0], w[4:0], w[4:0],
			  a, a, a, a, a, a, a, a, a, a,

			  w[4:0], w[4:0], w[4:0], w[4:0], w[4:0],
			  w[4:0], w[4:0], w[4:0], w[4:0], w[4:0],
			  a, a, a, a, a, a, a, a, a, a
			  );

   binary_ops_test #(6) binary_test_6 (6'b0, 6'b0,

			  w[5:0], w[5:0], w[5:0], w[5:0], w[5:0],
			  w[5:0], w[5:0], w[5:0], w[5:0], w[5:0],
			  a, a, a, a, a, a, a, a, a, a,

			  w[5:0], w[5:0], w[5:0], w[5:0], w[5:0],
			  w[5:0], w[5:0], w[5:0], w[5:0], w[5:0],
			  a, a, a, a, a, a, a, a, a, a
			  );

   binary_ops_test #(7) binary_test_7 (7'b0, 7'b0,

			  w[6:0], w[6:0], w[6:0], w[6:0], w[6:0],
			  w[6:0], w[6:0], w[6:0], w[6:0], w[6:0],
			  a, a, a, a, a, a, a, a, a, a,

			  w[6:0], w[6:0], w[6:0], w[6:0], w[6:0],
			  w[6:0], w[6:0], w[6:0], w[6:0], w[6:0],
			  a, a, a, a, a, a, a, a, a, a
			  );

   binary_ops_test #(8) binary_test_8 (8'b0, 8'b0,

			  w[7:0], w[7:0], w[7:0], w[7:0], w[7:0],
			  w[7:0], w[7:0], w[7:0], w[7:0], w[7:0],
			  a, a, a, a, a, a, a, a, a, a,

			  w[7:0], w[7:0], w[7:0], w[7:0], w[7:0],
			  w[7:0], w[7:0], w[7:0], w[7:0], w[7:0],
			  a, a, a, a, a, a, a, a, a, a
			  );

endmodule

*/
