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
`define MODNAME_SIZE \conditional_ops_test$size=1
`define COMPARE_NAME compare_conditional_ops_aux_1
`include "compare-aux.v"
`undef SIZE
`undef MODNAME_SIZE
`undef COMPARE_NAME

`define SIZE 2
`define MODNAME_SIZE \conditional_ops_test$size=2
`define COMPARE_NAME compare_conditional_ops_aux_2
`include "compare-aux.v"
`undef SIZE
`undef MODNAME_SIZE
`undef COMPARE_NAME

`define SIZE 3
`define MODNAME_SIZE \conditional_ops_test$size=3
`define COMPARE_NAME compare_conditional_ops_aux_3
`include "compare-aux.v"
`undef SIZE
`undef MODNAME_SIZE
`undef COMPARE_NAME

`define SIZE 4
`define MODNAME_SIZE \conditional_ops_test$size=4
`define COMPARE_NAME compare_conditional_ops_aux_4
`include "compare-aux.v"
`undef SIZE
`undef MODNAME_SIZE
`undef COMPARE_NAME

`define SIZE 5
`define MODNAME_SIZE \conditional_ops_test$size=5
`define COMPARE_NAME compare_conditional_ops_aux_5
`include "compare-aux.v"
`undef SIZE
`undef MODNAME_SIZE
`undef COMPARE_NAME


module compare_binary_ops () ;

   reg sel_a1;
   reg sel_a2;
   reg sel_a3;
   reg sel_a4;
   reg sel_a5;

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

   compare_conditional_ops_aux_1 test1 ( sel_a1, src_a1, src_b1, chk1 );
//   compare_conditional_ops_aux_2 test2 ( sel_a2, src_a2, src_b2, chk2 );
//   compare_conditional_ops_aux_3 test3 ( sel_a3, src_a3, src_b3, chk3 );
//   compare_conditional_ops_aux_4 test4 ( sel_a4, src_a4, src_b4, chk4 );
//   compare_conditional_ops_aux_5 test5 ( sel_a5, src_a5, src_b5, chk5 );

   reg [3:0] Vals;
   integer k;
   integer i0, i1, i2, i3, i4, i5;
   integer j0, j1, j2, j3, j4, j5;

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
      for(k = 0; k < 4; k = k + 1)
      for(i0 = 0; i0 < 4; i0 = i0 + 1)
      for(j0 = 0; j0 < 4; j0 = j0 + 1)
      begin
          sel_a1 = Vals[k];
	  src_a1 = Vals[i0];
	  src_b1 = Vals[j0];
          #100 chk1 = 1;
	  #100 chk1 = 0;
      end

      $display("Two-bit by two-bit checks.");
      for(k = 0; k < 4; k = k + 1)
      for(i0 = 0; i0 < 4; i0 = i0 + 1)
      for(i1 = 0; i1 < 4; i1 = i1 + 1)
      for(j0 = 0; j0 < 4; j0 = j0 + 1)
      for(j1 = 0; j1 < 4; j1 = j1 + 1)
      begin
         sel_a2 = Vals[k];
	 src_a2 = { Vals[i0], Vals[i1] };
	 src_b2 = { Vals[j0], Vals[j1] };
         #100 chk2 = 1;
	 #100 chk2 = 0;
      end

      $display("Three-bit by three-bit checks.");
      for(k = 0; k < 4; k = k + 1)
      for(i0 = 0; i0 < 4; i0 = i0 + 1)
      for(i1 = 0; i1 < 4; i1 = i1 + 1)
      for(i2 = 0; i2 < 4; i2 = i2 + 1)
      for(j0 = 0; j0 < 4; j0 = j0 + 1)
      for(j1 = 0; j1 < 4; j1 = j1 + 1)
      for(j2 = 0; j2 < 4; j2 = j2 + 1)
      begin
         sel_a3 = Vals[k];
	 src_a3 = { Vals[i0], Vals[i1], Vals[i2] };
	 src_b3 = { Vals[j0], Vals[j1], Vals[j2] };
         #100 chk3 = 1;
	 #100 chk3 = 0;
      end

      $display("Four-bit by four-bit checks.");
      for(k = 0; k < 4; k = k + 1)
      for(i0 = 0; i0 < 4; i0 = i0 + 1)
      for(i1 = 0; i1 < 4; i1 = i1 + 1)
      for(i2 = 0; i2 < 4; i2 = i2 + 1)
      for(i3 = 0; i3 < 4; i3 = i3 + 1)
      for(j0 = 0; j0 < 4; j0 = j0 + 1)
      for(j1 = 0; j1 < 4; j1 = j1 + 1)
      for(j2 = 0; j2 < 4; j2 = j2 + 1)
      for(j3 = 0; j3 < 4; j3 = j3 + 1)
      begin
         sel_a4 = Vals[k];
	 src_a4 = { Vals[i0], Vals[i1], Vals[i2], Vals[i3] };
	 src_b4 = { Vals[j0], Vals[j1], Vals[j2], Vals[j3] };
         #100 chk4 = 1;
	 #100 chk4 = 0;
      end

      $display("Five-bit by five-bit checks.");
      for(k = 0; k < 4; k = k + 1)
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
         sel_a5 = Vals[k];
	 src_a5 = { Vals[i0], Vals[i1], Vals[i2], Vals[i3], Vals[i4] };
	 src_b5 = { Vals[j0], Vals[j1], Vals[j2], Vals[j3], Vals[j4] };
         #100 chk5 = 1;
	 #100 chk5 = 0;
      end

  end

endmodule
