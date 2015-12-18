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



parameter foo = 5;

typedef logic [foo-1 : 0] bar_t; // logic [5:0]

// package p;

   parameter bar_t br = $clog2(foo); // logic [5:0] br = 3   (?)

  typedef bar_t [br : 0] buz_t; // logic [5:0] [3:0] 

   parameter buz_t bz = $bits(buz_t) + $bits(br); // logic [5:0] [3:0] bz = 24 + 6 = 30

// endpackage





module spec (input logic [127:0] in,
	     output wire [127:0] out);

   typedef buz_t [bz-1:0] goz_t; // logic [5:0] [3:0] [29:0]

   localparam goz_t gz = $bits(goz_t); // logic [5:0] [3:0] [29:0] gz = 6*4*30

   assign out = gz;

endmodule // spec

