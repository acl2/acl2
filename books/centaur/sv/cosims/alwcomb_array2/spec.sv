// SV - Symbolic Vector Hardware Analysis Framework
// Copyright (C) 2022 Intel Corp.
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
// Original authors: Sol Swords <sol.swords@intel.com>


module spec (input logic [127:0] in,
	     output logic [127:0] out);


   logic [3:0] 			  arr [3:0];


   generate
      genvar 			  i, j;
      for (i=0; i<4; i++) begin: array_i
	 always_comb begin
	    if (i==0)
	      arr[0] = in[4*i+3 : 4*i];
	    else
  	      arr[i] = arr[i-1] + in[4*i+3 : 4*i];
	 end
      end
      for (j=0; j<4; j++) begin: array_j
	 always_comb begin
	    out[4*j+3 : 4*j] = arr[j];
	 end
      end
   endgenerate

   assign out[127:16] = '0;
   
   
   // always_comb begin
   //    int j;
   //    for (j=0; j<4; j++) begin
   // 	 out[4*j+3 : 4*j] = arr[j];
   //    end
   // end
   
endmodule

