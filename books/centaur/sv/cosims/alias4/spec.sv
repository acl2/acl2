// SV - Symbolic Vector Hardware Analysis Framework
// Copyright (C) 2014-2015 Centaur Technology
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
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>

// Note: Originally this was the spec module.  When we changed the
// cosim framework to use svex-design-compile directly rather than
// basing it on SVTVs, this stopped working because the in/out signals
// got normalized to other names.  This is basically a bug with our
// cosim framework -- instead of directly setting "in" and looking up
// "out", we should properly normalize them using the alias table
// (defsvtv takes care of this for us).  But instead of complicating
// the cosim framework to fix this, we just wrap the body of the test
// in a submodule.
module sub (input wire [127:0] in,
	    output wire [127:0] out);

  // Aliasing directly from inputs to outputs

  alias out[0] = in[0];

  alias in[1] = out[1];

  alias in[10:2] = out[10:2];

  alias out[127:11] = in[127:11];

endmodule

module spec (input wire [127:0] in,
	     output wire [127:0] out);

  logic [127:0] in1;
  logic [127:0] out1;

   sub mysub (in1, out1);
   assign in1 = in;
   assign out = out1;



endmodule // spec
