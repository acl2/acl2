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

module negatory #(parameter width = 1, type DTYPE=logic)
   (output DTYPE [width-1:0] q,
    input DTYPE [width-1:0] d);

   assign q = ~d;

endmodule

typedef logic[3:0] foo_t;

typedef struct packed { foo_t [3:1] bar; logic [1:5] baz; } fuz_t;

module spec (input logic [127:0] in,
	     output wire [127:0] out);


   fuz_t [3:0] a, na;
   foo_t b, nb;
  struct packed { fuz_t a; foo_t b; } [1:0] c, nc;

   assign {c, b, a} = in;
   assign out = {nc, nb, na};

   negatory #(.width(4), .DTYPE(fuz_t)) ainst(na, a);
   negatory #(.width(1), .DTYPE(foo_t)) binst(nb, b);
   negatory #(.width(2), .DTYPE(struct packed { fuz_t a; foo_t b; })) cinst(nc, c);



endmodule
