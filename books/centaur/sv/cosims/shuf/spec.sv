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

module goofyshuffle (sel,b);
input [63:0] b;
output[63:0] sel;
assign sel[00] = b[2:0] == 0;
assign sel[01] = b[2:0] == 7;
assign sel[02] = b[2:0] == 6;
assign sel[03] = b[2:0] == 5;
assign sel[04] = b[2:0] == 4;
assign sel[05] = b[2:0] == 3;
assign sel[06] = b[2:0] == 2;
assign sel[07] = b[2:0] == 1;
assign sel[08] = b[10:8] == 1;
assign sel[09] = b[10:8] == 0;
assign sel[10] = b[10:8] == 7;
assign sel[11] = b[10:8] == 6;
assign sel[12] = b[10:8] == 5;
assign sel[13] = b[10:8] == 4;
assign sel[14] = b[10:8] == 3;
assign sel[15] = b[10:8] == 2;
assign sel[16] = b[18:16] == 2;
assign sel[17] = b[18:16] == 1;
assign sel[18] = b[18:16] == 0;
assign sel[19] = b[18:16] == 7;
assign sel[20] = b[18:16] == 6;
assign sel[21] = b[18:16] == 5;
assign sel[22] = b[18:16] == 4;
assign sel[23] = b[18:16] == 3;
assign sel[24] = b[26:24] == 3;
assign sel[25] = b[26:24] == 2;
assign sel[26] = b[26:24] == 1;
assign sel[27] = b[26:24] == 0;
assign sel[28] = b[26:24] == 7;
assign sel[29] = b[26:24] == 6;
assign sel[30] = b[26:24] == 5;
assign sel[31] = b[26:24] == 4;
assign sel[32] = b[34:32] == 4;
assign sel[33] = b[34:32] == 3;
assign sel[34] = b[34:32] == 2;
assign sel[35] = b[34:32] == 1;
assign sel[36] = b[34:32] == 0;
assign sel[37] = b[34:32] == 7;
assign sel[38] = b[34:32] == 6;
assign sel[39] = b[34:32] == 5;
assign sel[40] = b[42:40] == 5;
assign sel[41] = b[42:40] == 4;
assign sel[42] = b[42:40] == 3;
assign sel[43] = b[42:40] == 2;
assign sel[44] = b[42:40] == 1;
assign sel[45] = b[42:40] == 0;
assign sel[46] = b[42:40] == 7;
assign sel[47] = b[42:40] == 6;
assign sel[48] = b[50:48] == 6;
assign sel[49] = b[50:48] == 5;
assign sel[50] = b[50:48] == 4;
assign sel[51] = b[50:48] == 3;
assign sel[52] = b[50:48] == 2;
assign sel[53] = b[50:48] == 1;
assign sel[54] = b[50:48] == 0;
assign sel[55] = b[50:48] == 7;
assign sel[56] = b[58:56] == 7;
assign sel[57] = b[58:56] == 6;
assign sel[58] = b[58:56] == 5;
assign sel[59] = b[58:56] == 4;
assign sel[60] = b[58:56] == 3;
assign sel[61] = b[58:56] == 2;
assign sel[62] = b[58:56] == 1;
assign sel[63] = b[58:56] == 0;
endmodule


module spec (input logic [127:0] in,
	     output logic [127:0] out);

  assign out [127:64] = 0;

  goofyshuffle sub (out[63:0], in[63:0]);

endmodule
