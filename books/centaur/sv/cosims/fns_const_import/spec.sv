// SV - Symbolic Vector Hardware Analysis Framework
// Copyright (C) 2023 Intel Corporation
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

package my_core_pkg;
   
function logic [7:0] n_times_core ( logic [7:0] mult, int n );
   logic [7:0] acc;

   acc = 0;
   for (int i=0; i<n; i++) begin
      acc = acc + mult;
   end

   return acc;
endfunction
      
endpackage

package my_pkg;
   import my_core_pkg::*;
   
   function logic [7:0] n_times ( logic [7:0] mult, int n );
      return n_times_core(mult, n);
   endfunction // n_times
endpackage // my_pkg
   
module compute_n_times
  import my_pkg::*;
 #( parameter nn=8 )
   (input logic [7:0] in,
    output logic [15:0] out);

   localparam logic [7:0] base = n_times(8'b1, nn);
   
   assign out[7:0] = n_times(in, nn);
   assign out[15:8] = base;
endmodule
   


module spec (input logic [127:0] in,
	     output wire [127:0] out);

   compute_n_times #(1)  cntinst0 (in[7:0],   out[15:0]);
   compute_n_times #(2)  cntinst1 (in[15:8],  out[31:16]);
   compute_n_times #(4)  cntinst2 (in[23:16], out[47:32]);
   compute_n_times       cntinst3 (in[31:24], out[63:48]);   
   compute_n_times #(9)  cntinst4 (in[39:32], out[79:64]);
   compute_n_times #(10) cntinst5 (in[47:40], out[95:80]);   
   compute_n_times #(12) cntinst6 (in[55:48], out[111:96]);      
   compute_n_times #(16) cntinst7 (in[63:56], out[127:112]);
   
endmodule

