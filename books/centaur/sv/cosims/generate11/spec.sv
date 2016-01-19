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
// Original authors: Jared Davis <jared@centtech.com>

module spec (input logic [127:0] in,
	     output wire [127:0] out);

  wire [3:0] aa;
  wire [3:0] bb = in;

  // SystemVerilog-2012 Section 27.4 (Pages 751-752) explain:
  //
  //    "Within the generate block of a loop generate construct, there is an
  //     implicit localparam declaration.  This is an integer parameter that has
  //     the same name and type as the loop index variable, [...].
  //
  //     Because this implicit localparam has the same name as the genvar, any
  //     reference to this name inside the loop generate block will be a
  //     reference to the localparam, not to the genvar.  As a consequence it
  //     is not possible to have two nested loop generate constructs that use
  //     the same genvar."
  //
  // The spec even goes on to give Example 1, which shows that nested loops of
  // the following form are illegal, because they use the same loop index:
  //
  //       genvar i;
  //       for(i=0; i < 5; i=i+1) begin:a
  //          for(i=0; i < 5; i=i+1) begin:b
  //            ...                            // error, using "i" as loop index
  //            ...                            // for two nested generate loops
  //          end
  //       end
  //
  // That's fine and the above example is perfectly reasonable and we have a
  // test to make sure we are prohibiting it, see failtest/gen8.v.
  //
  // HOWEVER, what if the loops are declared with inline genvar declarations
  // instead of using a genvar that is declared previously?  In this case, it
  // sure seems like the genvar is being locally declared only for that loop.
  // So wouldn't this local genvar declaration override the outer parameter
  // declaration and hence be legal?
  //
  // Well, NCVerilog seems to think so.  VCS does not.  NCVerilog also
  // tolerates cosims/generate10b, which is perhaps more to the point.  I think
  // NCVerilog's behavior makes the most sense, and it seems easier to explain
  // how to scope a generate loop if we adopt its behavior, so we'll go with
  // NCV in this case.

  generate
    for(genvar i = 0; i < 4; i = i+1)
    begin:a
      for(genvar i = 0; i < 2; i = i+1)
      begin:b
	not (aa[i], bb[i]);
      end
    end
  endgenerate

  assign out = aa;

endmodule
