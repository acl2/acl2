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

`include "blankport.v"
`include "spec.v"
`include "impl.v"


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
