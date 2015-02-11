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


// test-conditional.v    basic tests of ?: operator translations

module conditional_ops_test (

select,
src1,
src2,

out1,
out2,
out3

);

   parameter size = 1;

   input select;
   input [size-1:0] src1;
   input [size-1:0] src2;
   output [size-1:0] out1;
   output [size-1:0] out2;
   output [size-1:0] out3;

   assign out1 = select ? src1 : src2;
   assign out2 = select ? /*@VL VL_X_SELECT */ src1 : src2;
   assign out3 = (src1 === src2) ? src1 : (select ? src1 : src2);

endmodule


/*+VL

module make_tests () ;

   wire [100:0] w;
   wire a;

   conditional_ops_test #(1) conditional_test_1 (1'b0, 1'b0, 1'b0, w[0:0], w[0:0], w[0:0]);
   conditional_ops_test #(2) conditional_test_2 (1'b0, 2'b0, 2'b0, w[1:0], w[1:0], w[1:0]);
   conditional_ops_test #(3) conditional_test_3 (1'b0, 3'b0, 3'b0, w[2:0], w[2:0], w[2:0]);
   conditional_ops_test #(4) conditional_test_4 (1'b0, 4'b0, 4'b0, w[3:0], w[3:0], w[3:0]);
   conditional_ops_test #(5) conditional_test_5 (1'b0, 5'b0, 5'b0, w[4:0], w[4:0], w[4:0]);

endmodule

*/
