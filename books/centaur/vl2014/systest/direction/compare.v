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

module compare_dir () ;

   reg [3:0] in1, in2;

   // spec outs
   wire [3:0] sout1, sout2;
   wire [7:0] sout3;
   wire [3:0] sout4, sout5, sout6, sout7, sout8, sout9, sout10, sout11, sout12, sout13, sout14, sout15;

   // impl outs
   wire [3:0] iout1, iout2;
   wire [7:0] iout3;
   wire [3:0] iout4, iout5, iout6, iout7, iout8, iout9, iout10, iout11, iout12, iout13, iout14, iout15;

   dir_test #(1) spec (in1, in2,
	sout1,
	sout2,
	sout3,
	sout4,
	sout5,
	sout6,
	sout7,
	sout8,
	sout9,
	sout10,
	sout11,
	sout12,
	sout13,
	sout14,
	sout15);

   \dir_test$size=1 impl(in1, in2,
	iout1,
	iout2,
	iout3,
	iout4,
	iout5,
	iout6,
	iout7,
	iout8,
	iout9,
	iout10,
	iout11,
	iout12,
	iout13,
	iout14,
	iout15);

   reg [3:0] Vals;
   integer i0, i1, i2, i3, i4, i5, i6, i7;

   initial
   begin

      Vals <= 4'bZX10;  // The valid Verilog values

      for(i0 = 0; i0 < 4; i0 = i0 + 1)
      for(i1 = 0; i1 < 4; i1 = i1 + 1)
      for(i2 = 0; i2 < 4; i2 = i2 + 1)
      for(i3 = 0; i3 < 4; i3 = i3 + 1)
      for(i4 = 0; i4 < 4; i4 = i4 + 1)
      for(i5 = 0; i5 < 4; i5 = i5 + 1)
      for(i6 = 0; i6 < 4; i6 = i6 + 1)
      for(i7 = 0; i7 < 4; i7 = i7 + 1)
      begin
	 in1 = { Vals[i0], Vals[i1], Vals[i2], Vals[i3] };
	 in2 = { Vals[i4], Vals[i5], Vals[i6], Vals[i7] };

         #100

// testing code.

`define fail "fail for %m, %b vs %b, in1 is %b, in2 is %b"
if (iout1 != sout1) $display(`fail, iout1, sout1, iout1, in1, in2);
if (iout2 != sout2) $display(`fail, iout2, sout2, iout2, in1, in2);
if (iout3 != sout3) $display(`fail, iout3, sout3, iout3, in1, in2);
if (iout4 != sout4) $display(`fail, iout4, sout4, iout4, in1, in2);
if (iout5 != sout5) $display(`fail, iout5, sout5, iout5, in1, in2);
if (iout6 != sout6) $display(`fail, iout6, sout6, iout6, in1, in2);
if (iout7 != sout7) $display(`fail, iout7, sout7, iout7, in1, in2);
if (iout8 != sout8) $display(`fail, iout8, sout8, iout8, in1, in2);
if (iout9 != sout9) $display(`fail, iout9, sout9, iout9, in1, in2);
if (iout10 != sout10) $display(`fail, iout10, sout10, iout10, in1, in2);
if (iout11 != sout11) $display(`fail, iout11, sout11, iout11, in1, in2);
if (iout12 != sout12) $display(`fail, iout12, sout12, iout12, in1, in2);
if (iout13 != sout13) $display(`fail, iout13, sout13, iout13, in1, in2);
if (iout14 != sout14) $display(`fail, iout14, sout14, iout14, in1, in2);
if (iout15 != sout15) $display(`fail, iout15, sout15, iout15, in1, in2);

if (impl.and1_0.o !== spec.and1[0].o)
   $display(`fail, impl.and1_0.o, spec.and1[0].o, impl.and1_0.o, in1, in2);

if (impl.and1_1.o !== spec.and1[1].o)
   $display(`fail, impl.and1_1.o, spec.and1[1].o, impl.and1_1.o, in1, in2);

if (impl.and2_0.o !== spec.and2[0].o)
   $display(`fail, impl.and2_0.o, spec.and2[0].o, impl.and2_0.o, in1, in2);

if (impl.and2_1.o !== spec.and2[1].o)
   $display(`fail, impl.and2_1.o, spec.and2[1].o, impl.and2_1.o, in1, in2);

if (impl.and3_1.o !== spec.and3[1].o)
   $display(`fail, impl.and3_1.o, spec.and3[1].o, impl.and3_1.o, in1, in2);

if (impl.and3_2.o !== spec.and3[2].o)
   $display(`fail, impl.and3_2.o, spec.and3[2].o, impl.and3_2.o, in1, in2);

if (impl.and4_1.o !== spec.and4[1].o)
   $display(`fail, impl.and4_1.o, spec.and4[1].o, impl.and4_1.o, in1, in2);

if (impl.and4_2.o !== spec.and4[2].o)
   $display(`fail, impl.and4_2.o, spec.and4[2].o, impl.and4_2.o, in1, in2);


      end

   end

endmodule
