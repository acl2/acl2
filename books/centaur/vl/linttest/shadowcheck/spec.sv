// VL Verilog Toolkit
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

parameter shadowed_p1 = 1;

module m0 ;

  wire 	     clk;

  // This shadowing is fine, there are no prior uses to confuse things
  wire [3:0] shadowed_p1 = 3;
  wire [3:0] fine_w1 = shadowed_p1;

  reg [3:0]  fine_r2;
  always @(posedge clk)
  begin
    fine_r2 = shadowed_p1 + fine_w1;
  end

endmodule


module m1 ;

  wire 	     clk;

  // This shadowing is not okay because there are prior uses that confuse scoping
  wire [3:0] bad_w1 = shadowed_p1;
  wire [3:0] shadowed_p1 = 3;
  wire [3:0] whatever = bad_w1;

endmodule

package pkg1 ;

  typedef logic pkg1type1_t;
  typedef logic pkg1type2_t;

endpackage

import pkg1::pkg1type1_t;

module m2 (input pkg1type1_t m2in1);

  import pkg1::*;

  pkg1type1_t m2var1;
  pkg1::pkg1type1_t m2var2;
  pkg1::pkg1type2_t m2var3;


endmodule



// BOZO we should probably have a lot more tests here (but note that the
// implicit linttest is also pretty closely related and covers some of this.):
//
//  - Shadowing in other kinds of contexts, including at least:
//      generates, block statements, for loops, generate loops, functions, tasks
//
//  - Symbols being imported from other packages, import clashes, shadowing due to tricky imports, etc
