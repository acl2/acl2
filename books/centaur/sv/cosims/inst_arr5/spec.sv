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

module submod (input [3:0] i);

  wire [3:0] internal = i;

endmodule // submod


module spec (input logic [127:0] in,
	     output wire [127:0] out);


  logic [3:0] foo [7:0];
   assign foo[7] =  in[31:28];
   assign foo[6] =  in[27:24];
   assign foo[5] =  in[23:20];
   assign foo[4] =  in[19:16];
   assign foo[3] =  in[15:12];
   assign foo[2] =  in[11:8];
   assign foo[1] =  in[7:4];
   assign foo[0] =  in[3:0];

   submod inst [7:0] (in[31:0]);

   assign out = { inst[7].internal,
                  inst[6].internal,
                  inst[5].internal,
                  inst[4].internal,
                  inst[3].internal,
                  inst[2].internal,
                  inst[1].internal,
                  inst[0].internal };

endmodule
