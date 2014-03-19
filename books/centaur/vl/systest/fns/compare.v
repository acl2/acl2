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


// Some testing of some VL's function translations

`include "spec.v"
`include "impl.v"

module test ();

reg [3:0] in;

wire [3:0] spec_o1, spec_o2, spec_o3, spec_o4, spec_o5, spec_o6;
wire [3:0] impl_o1, impl_o2, impl_o3, impl_o4, impl_o5, impl_o6;

fns #(1)    spec (spec_o1, spec_o2, spec_o3, spec_o4, spec_o5, spec_o6, in);
\fns$size=1 impl (impl_o1, impl_o2, impl_o3, impl_o4, impl_o5, impl_o6, in);



integer i0, i1, i2, i3;
reg [3:0] V;

initial begin

    V = 4'bzx10;

    for(i0 = 0;i0 < 4;i0 = i0 + 1)
    for(i1 = 0;i1 < 4;i1 = i1 + 1)
    for(i2 = 0;i2 < 4;i2 = i2 + 1)
    for(i3 = 0;i3 < 4;i3 = i3 + 1)
    begin
       in = { V[i0], V[i1], V[i2], V[i3] };
       #10
       $display("in = %b, spec = %b, impl = %b",
       		    in,
		    {spec_o1, spec_o2, spec_o3, spec_o4, spec_o5, spec_o6},
		    {impl_o1, impl_o2, impl_o3, impl_o4, impl_o5, impl_o6});

       if (spec_o1 !== impl_o1) $display("o1 fail: in = %b, spec = %b, impl = %b", in, spec_o1, impl_o1);
       if (spec_o2 !== impl_o2) $display("o2 fail: in = %b, spec = %b, impl = %b", in, spec_o2, impl_o2);
       if (spec_o3 !== impl_o3) $display("o3 fail: in = %b, spec = %b, impl = %b", in, spec_o3, impl_o3);
       if (spec_o4 !== impl_o4) $display("o4 fail: in = %b, spec = %b, impl = %b", in, spec_o4, impl_o4);
       if (spec_o5 !== impl_o5) $display("o5 fail: in = %b, spec = %b, impl = %b", in, spec_o5, impl_o5);
       if (spec_o6 !== impl_o6) $display("o6 fail: in = %b, spec = %b, impl = %b", in, spec_o6, impl_o6);
    end
end

endmodule

