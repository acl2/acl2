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

`include "blankport.v"

module compare_blankport () ;

   reg [3:0] in1, in2;

   wire [7:0] sout;
   wire [7:0] iout;

   blankport_test spec (sout, in1, in2);
   \blankport_test$size=4 impl(iout, in1, in2);

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
	 if (iout !== sout)
           $display("fail in1 %b, in2 %b, sout %b, iout %b", in1, in2, sout, iout);

      end

   end

endmodule
