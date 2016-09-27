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

module spec (input logic [127:0] in,
	     output logic [127:0] out);

  logic [3:0][3:0] foo;
   assign out[15:0] = foo;

   always_comb
     for (int i=0; i<4; i=i+1) begin
       foo[i][0] = in[i];
     end

   always_comb
     for (int i=0; i<4; i=i+1) begin
       for (int j=0; j<3; j=j+1) begin
	 foo[i][j+1] = in[i];
       end
     end

   
  logic [95:0] bar;
   assign out[127:16] = bar;
   // this combo is ok with VCS but not NCV (??)
   always_comb
     for (int i=0; i<16; i=i+1) begin
       bar[i] = in[i];
     end
   always_comb
     for (int k=0; k<16; k=k+1) begin
       bar[k+16] = in[k];
     end




   always_comb begin
     for (int i=32; i<48; i=i+1) begin
       // int j;
       // j=32;
       bar[i] = in[i];
     end
   end

  //  always_comb
  //    if (in[20]) begin
  //      int j;
  //      j=48;
  //      for (int i=0; i<16; i=i+1) begin
  // 	 out[i+j] = in[i];
  //      end
  //    end

  // logic [3:0][3:0] arr;

  //  always_comb
  //    if (in[20]) begin
  //      for (int i=0; i<2; i=i+1) begin
  // 	 arr[i] = '0;
  // 	 arr[i][in[19]] = in[i];
  //      end
  //    end


  //  always_comb
  //    if (in[20]) begin
  //      for (int i=0; i<2; i=i+1) begin
  // 	 arr[i+2] = '0;
  // 	 arr[i+2][in[19]] = in[i];
  //      end
  //    end

  //  always_comb
  //    out[79:64] = arr;

endmodule
