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




module in1out1 (input i, output o);

   assign o = i+1;

endmodule // in1out1

module in1out2 (input i, output [1:0] o);

   assign o = i+1;

endmodule // in1out1

module in2out1 (input [1:0] i, output o);

   assign o = i+1;

endmodule // in1out1

module in2out2 (input [1:0] i, output [1:0] o);

   assign o = i+1;

endmodule // in1out1


module spec (input logic [127:0] in,
	     output wire [127:0] out);

   in1out1 inst11r [3:0] (in[0], out[3:0]);

   in1out1 inst11n [3:0] (in[3:0], out[7:4]);

   in1out2 inst12r [1:0] (in[0], out[11:8]);
   
   in1out2 inst12n [1:0] (in[1:0], out[15:12]);

   in2out1 inst21r [3:0] (in[1:0], out[19:16]);

   in2out1 inst21n [3:0] (in[7:0], out[23:20]);

   in2out2 inst22r [1:0] (in[1:0], out[27:24]);

   in2out2 inst22n [1:0] (in[3:0], out[27:24]);

endmodule
