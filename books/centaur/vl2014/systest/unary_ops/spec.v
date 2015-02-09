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

// basic tests of unary operator translation

module unary_ops_test (

in,

out_bitnot,  // ~in          N-bit outputs
out_plus,    // +in
out_minus,   // -in

out_lognot,  // !in          1-bit outputs
out_and,     // &in
out_nand,    // ~&in
out_or,      // |in
out_nor,     // ~|in
out_xor,     // ^in
out_xnor,    // ~^in
out_xnor2,   // ^~in

out_true,    // constant t
out_false,   // constant f
out_x,       // constant x
out_z       // constant z

`ifdef SYSTEM_VERILOG_MODE
,

// some tests of ==? and !=? operators against certain patterns
out_wildeq1,
out_wildeq2,
out_wildeq3,
out_wildeq4,

out_wildneq1,
out_wildneq2,
out_wildneq3,
out_wildneq4

`endif

);

   parameter size = 1;

   input [size-1:0] in;

   output [size-1:0] out_bitnot ;
   output [size-1:0] out_plus ;
   output [size-1:0] out_minus ;

   output out_lognot ;
   output out_and ;
   output out_nand ;
   output out_or ;
   output out_nor ;
   output out_xor ;
   output out_xnor ;
   output out_xnor2 ;

   output out_true ;
   output out_false ;
   output out_x ;
   output out_z ;

`ifdef SYSTEM_VERILOG_MODE

   output out_wildeq1;
   output out_wildeq2;
   output out_wildeq3;
   output out_wildeq4;

   output out_wildneq1;
   output out_wildneq2;
   output out_wildneq3;
   output out_wildneq4;

`endif

   assign out_bitnot = ~in ;
   assign out_plus = +in;
   assign out_minus = -in;

   assign out_lognot = !in ;
   assign out_and = &in ;
   assign out_nand = ~&in ;
   assign out_or = |in ;
   assign out_nor = ~|in ;
   assign out_xor = ^in ;
   assign out_xnor = ~^in ;
   assign out_xnor2 = ^~in ;

   assign out_true = 1'b1;
   assign out_false = 1'b0;
   assign out_x = 1'bx;
   assign out_z = 1'bz;

`ifdef SYSTEM_VERILOG_MODE

   assign out_wildeq1 = in ==? 4'b1010;
   assign out_wildeq2 = in ==? 4'bxx10;
   assign out_wildeq3 = in ==? 4'b0?z1;
   assign out_wildeq4 = in ==? 4'bz1x0;

   assign out_wildneq1 = in !=? 4'b1010;
   assign out_wildneq2 = in !=? 4'bxx10;
   assign out_wildneq3 = in !=? 4'b0?z1;
   assign out_wildneq4 = in !=? 4'bz1x0;

`endif

endmodule



/*+VL

module make_tests () ;

   wire [100:0] w;
   wire a;

 `ifdef SYSTEM_VERILOG_MODE
    `define OUTS a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a
 `else
    `define OUTS a, a, a, a, a, a, a, a, a, a, a, a
 `endif

   unary_ops_test #(1) unary_test_1 (1'b0, w[0:0], w[0:0], w[0:0], `OUTS);
   unary_ops_test #(2) unary_test_2 (2'b0, w[1:0], w[1:0], w[1:0], `OUTS);
   unary_ops_test #(3) unary_test_3 (3'b0, w[2:0], w[2:0], w[2:0], `OUTS);
   unary_ops_test #(4) unary_test_4 (4'b0, w[3:0], w[3:0], w[3:0], `OUTS);
   unary_ops_test #(5) unary_test_5 (5'b0, w[4:0], w[4:0], w[4:0], `OUTS);
   unary_ops_test #(6) unary_test_6 (6'b0, w[5:0], w[5:0], w[5:0], `OUTS);
   unary_ops_test #(7) unary_test_7 (7'b0, w[6:0], w[6:0], w[6:0], `OUTS);
   unary_ops_test #(8) unary_test_8 (8'b0, w[7:0], w[7:0], w[7:0], `OUTS);

endmodule

*/
