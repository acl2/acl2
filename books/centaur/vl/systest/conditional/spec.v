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
