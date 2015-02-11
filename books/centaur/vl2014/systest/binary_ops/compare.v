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


// Exhaustive testing of binary operators up to some small size

module convert_z_to_x (out, in);

   parameter size = 1;

   output [size-1:0] out;
   input [size-1:0] in;

   reg [size-1:0] out;

   integer i;
   always @(in)
   begin
      for(i = 0; i < size; i = i + 1)
      begin
	 out[i] = (in[i] === 1'bz) ? 1'bx : in[i];
      end
   end

endmodule


// Nasty preprocessor garbage to introduce comparison modules for each of the
// various sizes.  See aux-compare-binary.v for details.

`define SIZE 1
`define MODNAME_SIZE \binary_ops_test$size=1
`define COMPARE_NAME compare_binary_ops_aux_1
`include "compare-aux.v"
`undef SIZE
`undef MODNAME_SIZE
`undef COMPARE_NAME

`define SIZE 2
`define MODNAME_SIZE \binary_ops_test$size=2
`define COMPARE_NAME compare_binary_ops_aux_2
`include "compare-aux.v"
`undef SIZE
`undef MODNAME_SIZE
`undef COMPARE_NAME

`define SIZE 3
`define MODNAME_SIZE \binary_ops_test$size=3
`define COMPARE_NAME compare_binary_ops_aux_3
`include "compare-aux.v"
`undef SIZE
`undef MODNAME_SIZE
`undef COMPARE_NAME

`define SIZE 4
`define MODNAME_SIZE \binary_ops_test$size=4
`define COMPARE_NAME compare_binary_ops_aux_4
`include "compare-aux.v"
`undef SIZE
`undef MODNAME_SIZE
`undef COMPARE_NAME

`define SIZE 5
`define MODNAME_SIZE \binary_ops_test$size=5
`define COMPARE_NAME compare_binary_ops_aux_5
`include "compare-aux.v"
`undef SIZE
`undef MODNAME_SIZE
`undef COMPARE_NAME

`define SIZE 6
`define MODNAME_SIZE \binary_ops_test$size=6
`define COMPARE_NAME compare_binary_ops_aux_6
`include "compare-aux.v"
`undef SIZE
`undef MODNAME_SIZE
`undef COMPARE_NAME

`define SIZE 7
`define MODNAME_SIZE \binary_ops_test$size=7
`define COMPARE_NAME compare_binary_ops_aux_7
`include "compare-aux.v"
`undef SIZE
`undef MODNAME_SIZE
`undef COMPARE_NAME

`define SIZE 8
`define MODNAME_SIZE \binary_ops_test$size=8
`define COMPARE_NAME compare_binary_ops_aux_8
`include "compare-aux.v"
`undef SIZE
`undef MODNAME_SIZE
`undef COMPARE_NAME



module compare_binary_ops () ;

   reg src_a1;
   reg [1:0] src_a2;
   reg [2:0] src_a3;
   reg [3:0] src_a4;
   reg [4:0] src_a5;
   reg [5:0] src_a6;
   reg [6:0] src_a7;
   reg [7:0] src_a8;

   reg src_b1;
   reg [1:0] src_b2;
   reg [2:0] src_b3;
   reg [3:0] src_b4;
   reg [4:0] src_b5;
   reg [5:0] src_b6;
   reg [6:0] src_b7;
   reg [7:0] src_b8;

   reg chk1;
   reg chk2;
   reg chk3;
   reg chk4;
   reg chk5;
   reg chk6;
   reg chk7;
   reg chk8;

   compare_binary_ops_aux_1 test1 ( src_a1, src_b1, chk1 );
   compare_binary_ops_aux_2 test2 ( src_a2, src_b2, chk2 );
   compare_binary_ops_aux_3 test3 ( src_a3, src_b3, chk3 );
   compare_binary_ops_aux_4 test4 ( src_a4, src_b4, chk4 );
   compare_binary_ops_aux_5 test5 ( src_a5, src_b5, chk5 );
   compare_binary_ops_aux_6 test6 ( src_a6, src_b6, chk6 );
   compare_binary_ops_aux_7 test7 ( src_a7, src_b7, chk7 );
   compare_binary_ops_aux_8 test8 ( src_a8, src_b8, chk8 );

   reg [3:0] Vals;
   integer i0, i1, i2, i3, i4, i5, i6, i7, i8;
   integer j0, j1, j2, j3, j4, j5, j6, j7, j8;

   initial
   begin

      chk1 <= 1'b0;
      chk2 <= 1'b0;
      chk3 <= 1'b0;
      chk4 <= 1'b0;
      chk5 <= 1'b0;
      chk6 <= 1'b0;
      chk7 <= 1'b0;
      chk8 <= 1'b0;

      Vals <= 4'bZX10;  // The valid Verilog values

      $display("One-bit by one-bit checks.");
      for(i0 = 0; i0 < 4; i0 = i0 + 1)
      for(j0 = 0; j0 < 4; j0 = j0 + 1)
      begin
	  src_a1 = Vals[i0];
	  src_b1 = Vals[j0];
          #100 chk1 = 1;
	  #100 chk1 = 0;
      end

      $display("Two-bit by two-bit checks.");
      for(i0 = 0; i0 < 4; i0 = i0 + 1)
      for(i1 = 0; i1 < 4; i1 = i1 + 1)
      for(j0 = 0; j0 < 4; j0 = j0 + 1)
      for(j1 = 0; j1 < 4; j1 = j1 + 1)
      begin
	 src_a2 = { Vals[i0], Vals[i1] };
	 src_b2 = { Vals[j0], Vals[j1] };
         #100 chk2 = 1;
	 #100 chk2 = 0;
      end

      $display("Three-bit by three-bit checks.");
      for(i0 = 0; i0 < 4; i0 = i0 + 1)
      for(i1 = 0; i1 < 4; i1 = i1 + 1)
      for(i2 = 0; i2 < 4; i2 = i2 + 1)
      for(j0 = 0; j0 < 4; j0 = j0 + 1)
      for(j1 = 0; j1 < 4; j1 = j1 + 1)
      for(j2 = 0; j2 < 4; j2 = j2 + 1)
      begin
	 src_a3 = { Vals[i0], Vals[i1], Vals[i2] };
	 src_b3 = { Vals[j0], Vals[j1], Vals[j2] };
         #100 chk3 = 1;
	 #100 chk3 = 0;
      end

      $display("Four-bit by four-bit checks.");
      for(i0 = 0; i0 < 4; i0 = i0 + 1)
      for(i1 = 0; i1 < 4; i1 = i1 + 1)
      for(i2 = 0; i2 < 4; i2 = i2 + 1)
      for(i3 = 0; i3 < 4; i3 = i3 + 1)
      for(j0 = 0; j0 < 4; j0 = j0 + 1)
      for(j1 = 0; j1 < 4; j1 = j1 + 1)
      for(j2 = 0; j2 < 4; j2 = j2 + 1)
      for(j3 = 0; j3 < 4; j3 = j3 + 1)
      begin
	 src_a4 = { Vals[i0], Vals[i1], Vals[i2], Vals[i3] };
	 src_b4 = { Vals[j0], Vals[j1], Vals[j2], Vals[j3] };
         #100 chk4 = 1;
	 #100 chk4 = 0;
      end

      $display("Five-bit by five-bit checks.");
      for(i0 = 0; i0 < 4; i0 = i0 + 1)
      for(i1 = 0; i1 < 4; i1 = i1 + 1)
      for(i2 = 0; i2 < 4; i2 = i2 + 1)
      for(i3 = 0; i3 < 4; i3 = i3 + 1)
      for(i4 = 0; i4 < 4; i4 = i4 + 1)
      for(j0 = 0; j0 < 4; j0 = j0 + 1)
      for(j1 = 0; j1 < 4; j1 = j1 + 1)
      for(j2 = 0; j2 < 4; j2 = j2 + 1)
      for(j3 = 0; j3 < 4; j3 = j3 + 1)
      for(j4 = 0; j4 < 4; j4 = j4 + 1)
      begin
	 src_a5 = { Vals[i0], Vals[i1], Vals[i2], Vals[i3], Vals[i4] };
	 src_b5 = { Vals[j0], Vals[j1], Vals[j2], Vals[j3], Vals[j4] };
         #100 chk5 = 1;
	 #100 chk5 = 0;
      end


// these take a long time, so i ordinarily keep them commented out

/*

      $display("Six-bit by six-bit checks.");
      for(i0 = 0; i0 < 4; i0 = i0 + 1)
      for(i1 = 0; i1 < 4; i1 = i1 + 1)
      for(i2 = 0; i2 < 4; i2 = i2 + 1)
      for(i3 = 0; i3 < 4; i3 = i3 + 1)
      for(i4 = 0; i4 < 4; i4 = i4 + 1)
      for(i5 = 0; i5 < 4; i5 = i5 + 1)
      for(j0 = 0; j0 < 4; j0 = j0 + 1)
      for(j1 = 0; j1 < 4; j1 = j1 + 1)
      for(j2 = 0; j2 < 4; j2 = j2 + 1)
      for(j3 = 0; j3 < 4; j3 = j3 + 1)
      for(j4 = 0; j4 < 4; j4 = j4 + 1)
      for(j5 = 0; j5 < 4; j5 = j5 + 1)
      begin
	 src_a6 = { Vals[i0], Vals[i1], Vals[i2], Vals[i3], Vals[i4], Vals[j5] };
	 src_b6 = { Vals[j0], Vals[j1], Vals[j2], Vals[j3], Vals[j4], Vals[j5] };
         #100 chk6 = 1;
	 #100 chk6 = 0;
      end

      $display("Seven-bit by seven-bit checks.");
      for(i0 = 0; i0 < 4; i0 = i0 + 1)
      for(i1 = 0; i1 < 4; i1 = i1 + 1)
      for(i2 = 0; i2 < 4; i2 = i2 + 1)
      for(i3 = 0; i3 < 4; i3 = i3 + 1)
      for(i4 = 0; i4 < 4; i4 = i4 + 1)
      for(i5 = 0; i5 < 4; i5 = i5 + 1)
      for(i6 = 0; i6 < 4; i6 = i6 + 1)
      for(j0 = 0; j0 < 4; j0 = j0 + 1)
      for(j1 = 0; j1 < 4; j1 = j1 + 1)
      for(j2 = 0; j2 < 4; j2 = j2 + 1)
      for(j3 = 0; j3 < 4; j3 = j3 + 1)
      for(j4 = 0; j4 < 4; j4 = j4 + 1)
      for(j5 = 0; j5 < 4; j5 = j5 + 1)
      for(j6 = 0; j6 < 4; j6 = j6 + 1)
      begin
	 src_a7 = { Vals[i0], Vals[i1], Vals[i2], Vals[i3], Vals[i4], Vals[i5], Vals[i6] };
	 src_b7 = { Vals[j0], Vals[j1], Vals[j2], Vals[j3], Vals[j4], Vals[j5], Vals[j6] };
         #100 chk7 = 1;
	 #100 chk7 = 0;
      end

// this takes a really long time.  you probably want to stop at 7.

      $display("Eight-bit by eight-bit checks.");
      for(i0 = 0; i0 < 4; i0 = i0 + 1)
      for(i1 = 0; i1 < 4; i1 = i1 + 1)
      for(i2 = 0; i2 < 4; i2 = i2 + 1)
      for(i3 = 0; i3 < 4; i3 = i3 + 1)
      for(i4 = 0; i4 < 4; i4 = i4 + 1)
      for(i5 = 0; i5 < 4; i5 = i5 + 1)
      for(i6 = 0; i6 < 4; i6 = i6 + 1)
      for(i7 = 0; i7 < 4; i7 = i7 + 1)
      for(j0 = 0; j0 < 4; j0 = j0 + 1)
      for(j1 = 0; j1 < 4; j1 = j1 + 1)
      for(j2 = 0; j2 < 4; j2 = j2 + 1)
      for(j3 = 0; j3 < 4; j3 = j3 + 1)
      for(j4 = 0; j4 < 4; j4 = j4 + 1)
      for(j5 = 0; j5 < 4; j5 = j5 + 1)
      for(j6 = 0; j6 < 4; j6 = j6 + 1)
      for(j7 = 0; j7 < 4; j7 = j7 + 1)
      begin
	 src_a8 = { Vals[i0], Vals[i1], Vals[i2], Vals[i3], Vals[i4], Vals[i5], Vals[i6], Vals[i7] };
	 src_b8 = { Vals[j0], Vals[j1], Vals[j2], Vals[j3], Vals[j4], Vals[j5], Vals[j6], Vals[j7] };
         #100 chk8 = 1;
	 #100 chk8 = 0;
      end

*/

   end

endmodule
