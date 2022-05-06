// SV - Symbolic Vector Hardware Analysis Framework
//
// Copyright (C) 2022 Intel Corporation
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
// Original author: Sol Swords <sol.swords@intel.com>

package mypkg;
   localparam WIDTH = 4;
   typedef logic [WIDTH-1:0] mytype;
   function automatic mytype myfun (logic [WIDTH-1:0] in);
      myfun = in+1;
   endfunction
endpackage // mypkg

module sub
  import mypkg::*;
   (input mytype in,
    input [WIDTH-1:-0] in2,
    output 	       mytype out);

   assign out = myfun(in) + myfun(in2);

endmodule // sub

module spec (input logic [127:0] in,
	     output wire [127:0] out);

   genvar 			 i;

   for (i=0; i*8<127; i++) begin: blk
      sub mysub (in[i*8+:4], in[i*8+4+:4], out[i*4+:4]);
   end
endmodule
   
