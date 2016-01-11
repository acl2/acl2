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
// Original authors: Sol Swords <sswords@centtech.com>
//                   Jared Davis <jared@centtech.com>

module spec (input logic [127:0] in,
	     output wire [127:0] out);

  genvar i;

  // Basic test of the nature of a genvar.

  // SystemVerilog-2012 is pretty clear that a generate var is supposed to
  // correspond to an integer.  We think this should mean a 32-bit signed
  // quantity.  This test just tries to make sure other implementations agree.

  wire [9:0] isize;
  wire [9:0] ival;
  wire [9:0] isigndetect;

  for(i = 0; i < 1; ++i)
  begin

    // We expect that I is 0.
    assign ival = i;

    // We expect that I is 32 bits.
    assign isize = $bits(i);

    // We expect that I is signed.  If it is indeed a signed zero, this should
    // get sign-extended to 10 bits.  But if I is unsigned, then it should get
    // zero extended instead.
    assign isigndetect = 3'sb 111 + i;
  end

  assign out = { isize, ival, isigndetect };

  // Basic test that an empty generate loop is OK.
  genvar jj;
  for(jj = 0; jj < 4; ++jj) begin end

endmodule
