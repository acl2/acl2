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

virtual class myfns
  #(parameter WIDTH = 8,
    parameter WIDTHMINUSONE = WIDTH-1);

   static function logic [WIDTHMINUSONE:0] pluswidthminusone (logic [WIDTHMINUSONE:0] in);
      pluswidthminusone = in+WIDTHMINUSONE;
   endfunction : pluswidthminusone
endclass // myfns




module spec (input logic [127:0] in,
	     output logic [127:0] out);

   assign out[7:0]    = myfns::pluswidthminusone(in[7:0]);
   assign out[15:8]   = '0;   
   assign out[31:16]  = myfns#(16)::pluswidthminusone(in[31:16]);
   assign out[63:32]  = '0;
   assign out[95:64]  = myfns#(.WIDTH(32))::pluswidthminusone(in[95:64]);
   assign out[127:96] = '0;
   
endmodule

