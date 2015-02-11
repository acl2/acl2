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

