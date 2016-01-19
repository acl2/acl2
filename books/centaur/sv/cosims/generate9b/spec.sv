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

  parameter version = 1;
  parameter crisis = 0;

  wire [3:0] A9, A8, A7, A6, A5, A4, A3, A2, A1, A0;
  wire [3:0] B9, B8, B7, B6, B5, B4, B3, B2, B1, B0;

  assign { B9, B8, B7, B6, B5, B4, B3, B2, B1, B0,
           A9, A8, A7, A6, A5, A4, A3, A2, A1, A0 } = in;

  // More tests of direct conditional nesting.

  if (version == 1)
     if (crisis == 0)
     begin : xxxlabel
       wire [3:0] xxx = A0;
     end
     else if (crisis == 1)
     begin : xxxlabel
       wire [3:0] xxx = A1;
     end

  if (version == 1)
     if (crisis == 0)
     begin : yyylabel
       wire [3:0] yyy = A2;
     end
     else if (crisis == 1)
     begin : yyylabel
       wire [3:0] yyy = A3;
     end
     else ; // gets associated with crisis stuff
  else
  begin : yyylabel
    wire [3:0] yyy = A4;
  end

  assign out = { yyylabel.yyy, xxxlabel.xxx };


endmodule
