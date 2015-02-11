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

module compare () ;

  reg [3:0] a;
  reg [3:0] n1;
  reg [3:0] n2;

  wire [40:0] spec_o0;
  wire [40:0] spec_o1;
  wire [40:0] spec_o2;
  wire [40:0] spec_o3;
  wire [40:0] spec_o4;
  wire [40:0] spec_o5;
  wire [40:0] spec_o6;
  wire [40:0] spec_o7;
  wire [40:0] spec_o8;
  wire [40:0] spec_o9;
  wire [40:0] spec_o10;

  wire [40:0] impl_o0;
  wire [40:0] impl_o1;
  wire [40:0] impl_o2;
  wire [40:0] impl_o3;
  wire [40:0] impl_o4;
  wire [40:0] impl_o5;
  wire [40:0] impl_o6;
  wire [40:0] impl_o7;
  wire [40:0] impl_o8;
  wire [40:0] impl_o9;
  wire [40:0] impl_o10;


  dut spec (
  .o0(spec_o0),
  .o1(spec_o1),
  .o2(spec_o2),
  .o3(spec_o3),
  .o4(spec_o4),
  .o5(spec_o5),
  .o6(spec_o6),
  .o7(spec_o7),
  .o8(spec_o8),
  .o9(spec_o9),
  .o10(spec_o10),
  .a(a),
  .n1(n1),
  .n2(n2)
  );

  \dut$size=1 impl (
  .o0(impl_o0),
  .o1(impl_o1),
  .o2(impl_o2),
  .o3(impl_o3),
  .o4(impl_o4),
  .o5(impl_o5),
  .o6(impl_o6),
  .o7(impl_o7),
  .o8(impl_o8),
  .o9(impl_o9),
  .o10(impl_o10),
  .a(a),
  .n1(n1),
  .n2(n2)
  );

  wire ok =
          (impl_o0 === spec_o0)
       && (impl_o1 === spec_o1)
       && (impl_o2 === spec_o2)
       && (impl_o3 === spec_o3)
       && (impl_o4 === spec_o4)
       && (impl_o5 === spec_o5)
       && (impl_o6 === spec_o6)
       && (impl_o7 === spec_o7)
       && (impl_o8 === spec_o8)
       && (impl_o9 === spec_o9)
       && (impl_o10 === spec_o10);


     

  integer    seed;
  integer    i;
  initial
  begin
    for(i = 0; i < 1000; i = i + 1)
    begin
      {a, n1, n2} = $random(seed);
      #10;
      if (!ok)
      begin
	$display("Failure for %b, %b, %b:", a, n1, n2);
	if (impl_o0 !== spec_o0) $display("fail o0: impl %b, spec %b", impl_o0, spec_o0);
	if (impl_o1 !== spec_o1) $display("fail o1: impl %b, spec %b", impl_o1, spec_o1);
	if (impl_o2 !== spec_o2) $display("fail o2: impl %b, spec %b", impl_o2, spec_o2);
	if (impl_o3 !== spec_o3) $display("fail o3: impl %b, spec %b", impl_o3, spec_o3);
	if (impl_o4 !== spec_o4) $display("fail o4: impl %b, spec %b", impl_o4, spec_o4);
	if (impl_o5 !== spec_o5) $display("fail o5: impl %b, spec %b", impl_o5, spec_o5);
	if (impl_o6 !== spec_o6) $display("fail o6: impl %b, spec %b", impl_o6, spec_o6);
	if (impl_o7 !== spec_o7) $display("fail o7: impl %b, spec %b", impl_o7, spec_o7);
	if (impl_o8 !== spec_o8) $display("fail o8: impl %b, spec %b", impl_o8, spec_o8);
	if (impl_o9 !== spec_o9) $display("fail o9: impl %b, spec %b", impl_o9, spec_o9);
	if (impl_o10 !== spec_o10) $display("fail o10: impl %b, spec %b", impl_o10, spec_o10);
      end
    end
  end

endmodule

