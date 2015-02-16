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

`ifndef SYSTEM_VERILOG_MODE

module dummy ();

  initial $display("This test is for SystemVerilog only, nothing to check.");

endmodule

`else

module compare () ;

  reg [7:0]  in1;
  reg [7:0]  in2;

  wire [7:0] spec_out1, spec_out2, spec_out3, spec_out4, spec_out5;

  dut spec (.in1(in1),
            .in2(in2),
            .out1(spec_out1),
            .out2(spec_out2),
            .out3(spec_out3),
            .out4(spec_out4),
            .out5(spec_out5)
  );

  wire [7:0] impl_out1, impl_out2, impl_out3, impl_out4, impl_out5;

  \dut$size=1 impl(.in1(in1),
                   .in2(in2),
                   .out1(impl_out1),
                   .out2(impl_out2),
                   .out3(impl_out3),
                   .out4(impl_out4),
                   .out5(impl_out5)
  );

  wire all_ok =     (impl_out1 === spec_out1)
                 && (impl_out2 === spec_out2)
                 && (impl_out3 === spec_out3)
                 && (impl_out4 === spec_out4)
                 && (impl_out5 === spec_out5);

  reg [3:0]  Vals;
  integer    i0, i1, i2, i3, i4, i5, i6, i7, i8;
  integer    j0, j1, j2, j3, j4, j5, j6, j7, j8;
  integer    seed;

  initial
    begin
      Vals = 4'bZX10;
      seed = 0;

      for(i0 = 0; i0 < 4; i0 = i0 + 1)
      for(i1 = 0; i1 < 4; i1 = i1 + 1)
      for(i2 = 0; i2 < 4; i2 = i2 + 1)
      for(i3 = 0; i3 < 4; i3 = i3 + 1)
      for(i4 = 0; i4 < 4; i4 = i4 + 1)
      for(i5 = 0; i5 < 4; i5 = i5 + 1)
      for(i6 = 0; i6 < 4; i6 = i6 + 1)
      for(i7 = 0; i7 < 4; i7 = i7 + 1)

      for(j0 = 0; j0 < 50; j0 = j0 + 1)
      begin
	in1 = $random(seed);
	in2 = $random(seed);
	in1[3:0] = {Vals[i0], Vals[i1], Vals[i2], Vals[i3]};
	in2[3:0] = {Vals[i4], Vals[i5], Vals[i6], Vals[i7]};
	#10;

	if (all_ok !== 1'b1)         $display("fail for in1 = %b, in2 = %b:", in1, in2);
	if (spec_out1 !== impl_out1) $display("out1 spec = %b vs. impl = %b", spec_out1, impl_out1);
	if (spec_out2 !== impl_out2) $display("out2 spec = %b vs. impl = %b", spec_out2, impl_out2);
	if (spec_out3 !== impl_out3) $display("out3 spec = %b vs. impl = %b", spec_out3, impl_out3);
	if (spec_out4 !== impl_out4) $display("out4 spec = %b vs. impl = %b", spec_out4, impl_out4);
	if (spec_out5 !== impl_out5) $display("out5 spec = %b vs. impl = %b", spec_out5, impl_out5);
	if (all_ok !== 1'b1)         $finish;

      end

   end

endmodule

`endif
