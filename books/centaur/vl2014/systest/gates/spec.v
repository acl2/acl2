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

// basic tests of gate translations

module gates_test (

src1,
src2,
src3,

out_not,
out_buf,

out_and,
out_or,
out_xor,
out_nand,
out_nor,
out_xnor,

out_bufif0,
out_bufif1,
out_notif0,
out_notif1,

out_nmos,
out_pmos,
out_cmos,

out_rnmos,
out_rpmos,
out_rcmos

);

   parameter size = 1;

   input [size-1:0] src1;
   input [size-1:0] src2;
   input [size-1:0] src3;

   output out_not;
   output out_buf;

   output out_and;
   output out_or;
   output out_xor;
   output out_nand;
   output out_nor;
   output out_xnor;

   output out_bufif0;
   output out_bufif1;
   output out_notif0;
   output out_notif1;

   output out_nmos;
   output out_pmos;
   output out_cmos;

   output out_rnmos;
   output out_rpmos;
   output out_rcmos;

   not (out_not, src1);
   buf (out_buf, src1);

   and  (out_and,  src1, src2);
   or   (out_or,   src1, src2);
   xor  (out_xor,  src1, src2);
   nand (out_nand, src1, src2);
   nor  (out_nor,  src1, src2);
   xnor (out_xnor, src1, src2);

   bufif1 (out_bufif1, src1, src2);
   bufif0 (out_bufif0, src1, src2);
   notif1 (out_notif1, src1, src2);
   notif0 (out_notif0, src1, src2);

   // Verilog's transistors are unidirectional anyway, but for good measure
   // lets avoid any possible interaction between their inputs and the inputs
   // of other gate instances.

   wire [size-1:0] nsrc1 = src1;
   wire [size-1:0] nsrc2 = src2;
   nmos (out_nmos, nsrc1, nsrc2);

   wire [size-1:0] psrc1 = src1;
   wire [size-1:0] psrc2 = src2;
   pmos (out_pmos, psrc1, psrc2);

   wire [size-1:0] csrc1 = src1;
   wire [size-1:0] csrc2 = src2;
   wire [size-1:0] csrc3 = src3;
   cmos (out_cmos, csrc1, csrc2, csrc3);

   wire [size-1:0] rnsrc1 = src1;
   wire [size-1:0] rnsrc2 = src2;
   rnmos (out_rnmos, rnsrc1, rnsrc2);

   wire [size-1:0] rpsrc1 = src1;
   wire [size-1:0] rpsrc2 = src2;
   rpmos (out_rpmos, rpsrc1, rpsrc2);

   wire [size-1:0] rcsrc1 = src1;
   wire [size-1:0] rcsrc2 = src2;
   wire [size-1:0] rcsrc3 = src3;
   rcmos (out_rcmos, rcsrc1, rcsrc2, rcsrc3);

endmodule



/*+VL

module make_tests () ;

   wire [100:0] w;
   wire a;

  `define outs w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8], w[9], w[10], \
     w[11], w[12], w[13], w[14], w[15], w[16], w[17]

   gates_test #(1) test1 (1'b0, 1'b0, 1'b0, `outs);

// Maybe, if we want to allow multi-bit inputs:
//
//   gates_test #(2) test2 (2'b0, 2'b0, 2'b0, `outs);
//   gates_test #(3) test3 (3'b0, 3'b0, 3'b0, `outs);
//   gates_test #(4) test4 (4'b0, 4'b0, 4'b0, `outs);

endmodule

*/


