// VL Verilog Toolkit
// Copyright (C) 2008-2014 Centaur Technology
//
// Contact:
//   Centaur Technology Formal Verification Group
//   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
//   http://www.centtech.com/
//
// This program is free software; you can redistribute it and/or modify it under
// the terms of the GNU General Public License as published by the Free Software
// Foundation; either version 2 of the License, or (at your option) any later
// version.  This program is distributed in the hope that it will be useful but
// WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
// more details.  You should have received a copy of the GNU General Public
// License along with this program; if not, write to the Free Software
// Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
//
// Original author: Jared Davis <jared@centtech.com>

// basic tests of gate translations

module gates_test (

src1,
src2,
src3,
src4,

out_not,
out_not2,
out_buf,
out_buf2,

out_and,
out_or,
out_xor,
out_nand,
out_nor,
out_xnor,

out_and3,
out_or3,
out_xor3,
out_nand3,
out_nor3,
out_xnor3,

out_and4,
out_or4,
out_xor4,
out_nand4,
out_nor4,
out_xnor4


);

   parameter size = 1;

   input [size-1:0] src1;
   input [size-1:0] src2;
   input [size-1:0] src3;
   input [size-1:0] src4;

   output out_not;
   output out_buf;
   output out_not2;
   output out_buf2;
   output out_and;
   output out_or;
   output out_xor;
   output out_nand;
   output out_nor;
   output out_xnor;
   output out_and3;
   output out_or3;
   output out_xor3;
   output out_nand3;
   output out_nor3;
   output out_xnor3;
   output out_and4;
   output out_or4;
   output out_xor4;
   output out_nand4;
   output out_nor4;
   output out_xnor4;

   not (out_not, out_not2, src1);
   buf (out_buf, out_buf2, src1);

   // Goofy, degenerate one-bit cases
   and  (out_and,  src1);
   or   (out_or,   src1);
   xor  (out_xor,  src1);
   nand (out_nand, src1);
   nor  (out_nor,  src1);
   xnor (out_xnor, src1);

  // Higher arity gates

  // Checking arities 3 and 4 is good w.r.t. xor/xnor, where parity sorts of
  // things could make misinterpretations look correct at one size but not the
  // other.

  and  (out_and3,  src1, src2, src3);
  or   (out_or3,   src1, src2, src3);
  xor  (out_xor3,  src1, src2, src3);
  nand (out_nand3, src1, src2, src3);
  nor  (out_nor3,  src1, src2, src3);
  xnor (out_xnor3, src1, src2, src3);

  and  (out_and4,  src1, src2, src3, src4);
  or   (out_or4,   src1, src2, src3, src4);
  xor  (out_xor4,  src1, src2, src3, src4);
  nand (out_nand4, src1, src2, src3, src4);
  nor  (out_nor4,  src1, src2, src3, src4);
  xnor (out_xnor4, src1, src2, src3, src4);

endmodule



/*+VL

module make_tests () ;

   wire [100:0] w;
   wire a;


   gates_test #(1) test1 (1'b0, 1'b0, 1'b0, 1'b0,
                          w[0],  w[1],  w[2],  w[3],
                          w[4],  w[5],  w[6],  w[7],  w[8],  w[9],
                          w[10], w[11], w[12], w[13], w[14], w[15],
                          w[16], w[17], w[18], w[19], w[20], w[21]);

endmodule

*/


