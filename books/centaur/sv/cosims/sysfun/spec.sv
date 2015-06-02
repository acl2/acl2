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
// Original author: Sol Swords <sswords@centtech.com>

module spec (input logic [127:0] in,
	     output logic [127:0] out);

  logic [3:0] a;
  integer b;
  // string c;  -- doesn't work in NCV
  logic [3:0] [2:7] c;
  logic [0:3] d;
  typedef logic [3:0] [5:1] arr2;
   arr2 e;
   arr2 f [4:6];
   typedef arr2 arr3 [2:5];
   arr3 g;
   arr3 h [4:0];

   always_comb begin
     case (in[2:0])
       0 :  case (in[4:3])
	      0 : out = { $bits(a), $dimensions(a) };
	      1 : out = { $left(a), $right(a) };
	      2 : out = { $low(a), $high(a) };
	      3 : out = { $increment(a), $size(a) } ;
	    endcase // case (in[4:3])
       1 :  case (in[4:3])
	      0 : out = { $bits(b), $dimensions(b) };
	      1 : out = { $left(b), $right(b) };
	      2 : out = { $low(b), $high(b) };
	      3 : out = { $increment(b), $size(b) } ;
	    endcase // case (in[4:3])
       2 :  case (in[4:3])
	      0 : out = { $bits(c), $dimensions(c) };
	      1 : out = { $left(c), $right(c) };
	      2 : out = { $low(c), $high(c) };
	      3 : out = { $increment(c), $size(c) } ;
	    endcase // case (in[4:3])
       3 :  case (in[4:3])
	      0 : out = { $bits(d), $dimensions(d) };
	      1 : out = { $left(d), $right(d) };
	      2 : out = { $low(d), $high(d) };
	      3 : out = { $increment(d), $size(d) } ;
	    endcase // case (in[4:3])
       4 :  case (in[4:3])
	      0 : out = { $bits(e), $dimensions(e) };
	      1 : out = { $left(e), $right(e) };
	      2 : out = { $low(e), $high(e) };
	      3 : out = { $increment(e), $size(e) } ;
	    endcase // case (in[4:3])
       5 :  case (in[4:3])
	      0 : out = { $bits(f), $dimensions(f) };
	      1 : out = { $left(f), $right(f) };
	      2 : out = { $low(f), $high(f) };
	      3 : out = { $increment(f), $size(f) } ;
	    endcase // case (in[4:3])
       6 :  case (in[4:3])
	      0 : out = { $bits(g), $dimensions(g) };
	      1 : out = { $left(g), $right(g) };
	      2 : out = { $low(g), $high(g) };
	      3 : out = { $increment(g), $size(g) } ;
	    endcase // case (in[4:3])
       7 :  case (in[4:3])
	      0 : out = { $bits(h), $dimensions(h) };
	      1 : out = { $left(h), $right(h) };
	      2 : out = { $low(h), $high(h) };
	      3 : out = { $increment(h), $size(h) } ;
	    endcase // case (in[4:3])
     endcase // case (in[2:0])
   end // always_comb

endmodule // spec

