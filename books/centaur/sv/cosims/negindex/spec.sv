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


module sub #(msb=0, lsb=0) (output [7:0] width);

  wire [msb:lsb] foo;

   assign width = $bits(foo);

endmodule

module spec (input logic [127:0] in,
	     output logic [127:0] out);
  genvar a;
   for (a = 0; a < 4; a++) begin : ablk
     genvar b;
     for (b = 0; b < 4; b++) begin : bblk
       wire [7:0] width;
       sub #(a-2, b-2) sub (width);
     end
   end

   assign out = { ablk[0].bblk[0].width,
                  ablk[0].bblk[1].width,
                  ablk[0].bblk[2].width,
                  ablk[0].bblk[3].width,
                  ablk[1].bblk[0].width,
                  ablk[1].bblk[1].width,
                  ablk[1].bblk[2].width,
                  ablk[1].bblk[3].width,
                  ablk[2].bblk[0].width,
                  ablk[2].bblk[1].width,
                  ablk[2].bblk[2].width,
                  ablk[2].bblk[3].width,
                  ablk[3].bblk[0].width,
                  ablk[3].bblk[1].width,
                  ablk[3].bblk[2].width,
                  ablk[3].bblk[3].width };

endmodule
