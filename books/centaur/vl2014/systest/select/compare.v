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


// exhaustive testing of bit-selects up to size 6 by 6

// takes about 5 minutes to run with Verilog-XL on fv-1.

module convert_z_to_x (out, in);

   output out;
   input in;

   assign out = (in === 1'bz) ? 1'bx : in;

endmodule



module test () ;

reg [6:0] in;
reg [6:0] sel;

select_tests #(1) spec ( in, sel,

  spec_f1_s1, spec_f1_s2, spec_f1_s3, spec_f1_s4, spec_f1_s5, spec_f1_s6,
  spec_f2_s1, spec_f2_s2, spec_f2_s3, spec_f2_s4, spec_f2_s5, spec_f2_s6,
  spec_f3_s1, spec_f3_s2, spec_f3_s3, spec_f3_s4, spec_f3_s5, spec_f3_s6,
  spec_f4_s1, spec_f4_s2, spec_f4_s3, spec_f4_s4, spec_f4_s5, spec_f4_s6,
  spec_f5_s1, spec_f5_s2, spec_f5_s3, spec_f5_s4, spec_f5_s5, spec_f5_s6,
  spec_f6_s1, spec_f6_s2, spec_f6_s3, spec_f6_s4, spec_f6_s5, spec_f6_s6,
  spec_f7_s1, spec_f7_s2, spec_f7_s3, spec_f7_s4, spec_f7_s5, spec_f7_s6);

\select_tests$foo=1 impl ( in, sel,

  impl_f1_s1, impl_f1_s2, impl_f1_s3, impl_f1_s4, impl_f1_s5, impl_f1_s6,
  impl_f2_s1, impl_f2_s2, impl_f2_s3, impl_f2_s4, impl_f2_s5, impl_f2_s6,
  impl_f3_s1, impl_f3_s2, impl_f3_s3, impl_f3_s4, impl_f3_s5, impl_f3_s6,
  impl_f4_s1, impl_f4_s2, impl_f4_s3, impl_f4_s4, impl_f4_s5, impl_f4_s6,
  impl_f5_s1, impl_f5_s2, impl_f5_s3, impl_f5_s4, impl_f5_s5, impl_f5_s6,
  impl_f6_s1, impl_f6_s2, impl_f6_s3, impl_f6_s4, impl_f6_s5, impl_f6_s6,
  impl_f7_s1, impl_f7_s2, impl_f7_s3, impl_f7_s4, impl_f7_s5, impl_f7_s6);



// The VL version converts Zs to Xs, so we need to fix up the spec.

convert_z_to_x fix_f1_s1 (spec_f1_s1_x, spec_f1_s1);
convert_z_to_x fix_f1_s2 (spec_f1_s2_x, spec_f1_s2);
convert_z_to_x fix_f1_s3 (spec_f1_s3_x, spec_f1_s3);
convert_z_to_x fix_f1_s4 (spec_f1_s4_x, spec_f1_s4);
convert_z_to_x fix_f1_s5 (spec_f1_s5_x, spec_f1_s5);
convert_z_to_x fix_f1_s6 (spec_f1_s6_x, spec_f1_s6);

convert_z_to_x fix_f2_s1 (spec_f2_s1_x, spec_f2_s1);
convert_z_to_x fix_f2_s2 (spec_f2_s2_x, spec_f2_s2);
convert_z_to_x fix_f2_s3 (spec_f2_s3_x, spec_f2_s3);
convert_z_to_x fix_f2_s4 (spec_f2_s4_x, spec_f2_s4);
convert_z_to_x fix_f2_s5 (spec_f2_s5_x, spec_f2_s5);
convert_z_to_x fix_f2_s6 (spec_f2_s6_x, spec_f2_s6);

convert_z_to_x fix_f3_s1 (spec_f3_s1_x, spec_f3_s1);
convert_z_to_x fix_f3_s2 (spec_f3_s2_x, spec_f3_s2);
convert_z_to_x fix_f3_s3 (spec_f3_s3_x, spec_f3_s3);
convert_z_to_x fix_f3_s4 (spec_f3_s4_x, spec_f3_s4);
convert_z_to_x fix_f3_s5 (spec_f3_s5_x, spec_f3_s5);
convert_z_to_x fix_f3_s6 (spec_f3_s6_x, spec_f3_s6);

convert_z_to_x fix_f4_s1 (spec_f4_s1_x, spec_f4_s1);
convert_z_to_x fix_f4_s2 (spec_f4_s2_x, spec_f4_s2);
convert_z_to_x fix_f4_s3 (spec_f4_s3_x, spec_f4_s3);
convert_z_to_x fix_f4_s4 (spec_f4_s4_x, spec_f4_s4);
convert_z_to_x fix_f4_s5 (spec_f4_s5_x, spec_f4_s5);
convert_z_to_x fix_f4_s6 (spec_f4_s6_x, spec_f4_s6);

convert_z_to_x fix_f5_s1 (spec_f5_s1_x, spec_f5_s1);
convert_z_to_x fix_f5_s2 (spec_f5_s2_x, spec_f5_s2);
convert_z_to_x fix_f5_s3 (spec_f5_s3_x, spec_f5_s3);
convert_z_to_x fix_f5_s4 (spec_f5_s4_x, spec_f5_s4);
convert_z_to_x fix_f5_s5 (spec_f5_s5_x, spec_f5_s5);
convert_z_to_x fix_f5_s6 (spec_f5_s6_x, spec_f5_s6);

convert_z_to_x fix_f6_s1 (spec_f6_s1_x, spec_f6_s1);
convert_z_to_x fix_f6_s2 (spec_f6_s2_x, spec_f6_s2);
convert_z_to_x fix_f6_s3 (spec_f6_s3_x, spec_f6_s3);
convert_z_to_x fix_f6_s4 (spec_f6_s4_x, spec_f6_s4);
convert_z_to_x fix_f6_s5 (spec_f6_s5_x, spec_f6_s5);
convert_z_to_x fix_f6_s6 (spec_f6_s6_x, spec_f6_s6);

wire okp = (
        (spec_f1_s1_x === impl_f1_s1) &&
        (spec_f1_s2_x === impl_f1_s2) &&
        (spec_f1_s3_x === impl_f1_s3) &&
        (spec_f1_s4_x === impl_f1_s4) &&
        (spec_f1_s5_x === impl_f1_s5) &&
        (spec_f1_s6_x === impl_f1_s6) &&

        (spec_f2_s1_x === impl_f2_s1) &&
        (spec_f2_s2_x === impl_f2_s2) &&
        (spec_f2_s3_x === impl_f2_s3) &&
        (spec_f2_s4_x === impl_f2_s4) &&
        (spec_f2_s5_x === impl_f2_s5) &&
        (spec_f2_s6_x === impl_f2_s6) &&

        (spec_f3_s1_x === impl_f3_s1) &&
        (spec_f3_s2_x === impl_f3_s2) &&
        (spec_f3_s3_x === impl_f3_s3) &&
        (spec_f3_s4_x === impl_f3_s4) &&
        (spec_f3_s5_x === impl_f3_s5) &&
        (spec_f3_s6_x === impl_f3_s6) &&

        (spec_f4_s1_x === impl_f4_s1) &&
        (spec_f4_s2_x === impl_f4_s2) &&
        (spec_f4_s3_x === impl_f4_s3) &&
        (spec_f4_s4_x === impl_f4_s4) &&
        (spec_f4_s5_x === impl_f4_s5) &&
        (spec_f4_s6_x === impl_f4_s6) &&

        (spec_f5_s1_x === impl_f5_s1) &&
        (spec_f5_s2_x === impl_f5_s2) &&
        (spec_f5_s3_x === impl_f5_s3) &&
        (spec_f5_s4_x === impl_f5_s4) &&
        (spec_f5_s5_x === impl_f5_s5) &&
        (spec_f5_s6_x === impl_f5_s6) &&

        (spec_f6_s1_x === impl_f6_s1) &&
        (spec_f6_s2_x === impl_f6_s2) &&
        (spec_f6_s3_x === impl_f6_s3) &&
        (spec_f6_s4_x === impl_f6_s4) &&
        (spec_f6_s5_x === impl_f6_s5) &&
        (spec_f6_s6_x === impl_f6_s6)
	);



reg [3:0] V;
integer f1, f2, f3, f4, f5, f6;
integer s1, s2, s3, s4, s5, s6;

initial
begin

  V = 4'bzx10;

  for(f1 = 0; f1 < 4; f1 = f1 + 1)
  for(f2 = 0; f2 < 4; f2 = f2 + 1)
  for(f3 = 0; f3 < 4; f3 = f3 + 1)
  for(f4 = 0; f4 < 4; f4 = f4 + 1)
  for(f5 = 0; f5 < 4; f5 = f5 + 1)
  for(f6 = 0; f6 < 4; f6 = f6 + 1)
  for(s1 = 0; s1 < 4; s1 = s1 + 1)
  for(s2 = 0; s2 < 4; s2 = s2 + 1)
  for(s3 = 0; s3 < 4; s3 = s3 + 1)
  for(s4 = 0; s4 < 4; s4 = s4 + 1)
  for(s5 = 0; s5 < 4; s5 = s5 + 1)
  for(s6 = 0; s6 < 4; s6 = s6 + 1)
  begin

    in  <= { V[f1], V[f2], V[f3], V[f4], V[f5], V[f6] };
    sel <= { V[s1], V[s2], V[s3], V[s4], V[s5], V[s6] };
    #100

//    $display("From = %b, Sel = %b, OK = %b", in, sel, okp);

    if (!okp)
    begin

      $display("compare_selects fail for from = %b, sel = %b", in, sel);

      if (spec_f1_s1_x !== impl_f1_s1) $display("spec_f1_s1_x = %b, impl_f1_s1 = %b", spec_f1_s1_x, impl_f1_s1);
      if (spec_f1_s2_x !== impl_f1_s2) $display("spec_f1_s2_x = %b, impl_f1_s2 = %b", spec_f1_s2_x, impl_f1_s2);
      if (spec_f1_s3_x !== impl_f1_s3) $display("spec_f1_s3_x = %b, impl_f1_s3 = %b", spec_f1_s3_x, impl_f1_s3);
      if (spec_f1_s4_x !== impl_f1_s4) $display("spec_f1_s4_x = %b, impl_f1_s4 = %b", spec_f1_s4_x, impl_f1_s4);
      if (spec_f1_s5_x !== impl_f1_s5) $display("spec_f1_s5_x = %b, impl_f1_s5 = %b", spec_f1_s5_x, impl_f1_s5);
      if (spec_f1_s6_x !== impl_f1_s6) $display("spec_f1_s6_x = %b, impl_f1_s6 = %b", spec_f1_s6_x, impl_f1_s6);

      if (spec_f2_s1_x !== impl_f2_s1) $display("spec_f2_s1_x = %b, impl_f2_s1 = %b", spec_f2_s1_x, impl_f2_s1);
      if (spec_f2_s2_x !== impl_f2_s2) $display("spec_f2_s2_x = %b, impl_f2_s2 = %b", spec_f2_s2_x, impl_f2_s2);
      if (spec_f2_s3_x !== impl_f2_s3) $display("spec_f2_s3_x = %b, impl_f2_s3 = %b", spec_f2_s3_x, impl_f2_s3);
      if (spec_f2_s4_x !== impl_f2_s4) $display("spec_f2_s4_x = %b, impl_f2_s4 = %b", spec_f2_s4_x, impl_f2_s4);
      if (spec_f2_s5_x !== impl_f2_s5) $display("spec_f2_s5_x = %b, impl_f2_s5 = %b", spec_f2_s5_x, impl_f2_s5);
      if (spec_f2_s6_x !== impl_f2_s6) $display("spec_f2_s6_x = %b, impl_f2_s6 = %b", spec_f2_s6_x, impl_f2_s6);

      if (spec_f3_s1_x !== impl_f3_s1) $display("spec_f3_s1_x = %b, impl_f3_s1 = %b", spec_f3_s1_x, impl_f3_s1);
      if (spec_f3_s2_x !== impl_f3_s2) $display("spec_f3_s2_x = %b, impl_f3_s2 = %b", spec_f3_s2_x, impl_f3_s2);
      if (spec_f3_s3_x !== impl_f3_s3) $display("spec_f3_s3_x = %b, impl_f3_s3 = %b", spec_f3_s3_x, impl_f3_s3);
      if (spec_f3_s4_x !== impl_f3_s4) $display("spec_f3_s4_x = %b, impl_f3_s4 = %b", spec_f3_s4_x, impl_f3_s4);
      if (spec_f3_s5_x !== impl_f3_s5) $display("spec_f3_s5_x = %b, impl_f3_s5 = %b", spec_f3_s5_x, impl_f3_s5);
      if (spec_f3_s6_x !== impl_f3_s6) $display("spec_f3_s6_x = %b, impl_f3_s6 = %b", spec_f3_s6_x, impl_f3_s6);

      if (spec_f4_s1_x !== impl_f4_s1) $display("spec_f4_s1_x = %b, impl_f4_s1 = %b", spec_f4_s1_x, impl_f4_s1);
      if (spec_f4_s2_x !== impl_f4_s2) $display("spec_f4_s2_x = %b, impl_f4_s2 = %b", spec_f4_s2_x, impl_f4_s2);
      if (spec_f4_s3_x !== impl_f4_s3) $display("spec_f4_s3_x = %b, impl_f4_s3 = %b", spec_f4_s3_x, impl_f4_s3);
      if (spec_f4_s4_x !== impl_f4_s4) $display("spec_f4_s4_x = %b, impl_f4_s4 = %b", spec_f4_s4_x, impl_f4_s4);
      if (spec_f4_s5_x !== impl_f4_s5) $display("spec_f4_s5_x = %b, impl_f4_s5 = %b", spec_f4_s5_x, impl_f4_s5);
      if (spec_f4_s6_x !== impl_f4_s6) $display("spec_f4_s6_x = %b, impl_f4_s6 = %b", spec_f4_s6_x, impl_f4_s6);

      if (spec_f5_s1_x !== impl_f5_s1) $display("spec_f5_s1_x = %b, impl_f5_s1 = %b", spec_f5_s1_x, impl_f5_s1);
      if (spec_f5_s2_x !== impl_f5_s2) $display("spec_f5_s2_x = %b, impl_f5_s2 = %b", spec_f5_s2_x, impl_f5_s2);
      if (spec_f5_s3_x !== impl_f5_s3) $display("spec_f5_s3_x = %b, impl_f5_s3 = %b", spec_f5_s3_x, impl_f5_s3);
      if (spec_f5_s4_x !== impl_f5_s4) $display("spec_f5_s4_x = %b, impl_f5_s4 = %b", spec_f5_s4_x, impl_f5_s4);
      if (spec_f5_s5_x !== impl_f5_s5) $display("spec_f5_s5_x = %b, impl_f5_s5 = %b", spec_f5_s5_x, impl_f5_s5);
      if (spec_f5_s6_x !== impl_f5_s6) $display("spec_f5_s6_x = %b, impl_f5_s6 = %b", spec_f5_s6_x, impl_f5_s6);

      if (spec_f6_s1_x !== impl_f6_s1) $display("spec_f6_s1_x = %b, impl_f6_s1 = %b", spec_f6_s1_x, impl_f6_s1);
      if (spec_f6_s2_x !== impl_f6_s2) $display("spec_f6_s2_x = %b, impl_f6_s2 = %b", spec_f6_s2_x, impl_f6_s2);
      if (spec_f6_s3_x !== impl_f6_s3) $display("spec_f6_s3_x = %b, impl_f6_s3 = %b", spec_f6_s3_x, impl_f6_s3);
      if (spec_f6_s4_x !== impl_f6_s4) $display("spec_f6_s4_x = %b, impl_f6_s4 = %b", spec_f6_s4_x, impl_f6_s4);
      if (spec_f6_s5_x !== impl_f6_s5) $display("spec_f6_s5_x = %b, impl_f6_s5 = %b", spec_f6_s5_x, impl_f6_s5);
      if (spec_f6_s6_x !== impl_f6_s6) $display("spec_f6_s6_x = %b, impl_f6_s6 = %b", spec_f6_s6_x, impl_f6_s6);

//      $finish;
    end

  end // loops

end // initial


endmodule
