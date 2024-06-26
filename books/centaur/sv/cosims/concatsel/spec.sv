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



module spec (input logic [127:0] in,
	     output wire [127:0] out);

   logic [2:0] 			 idx1;
   logic [2:0] 			 idx2;
   logic [2:0] 			 idx3;

   assign idx1 = in[2:0];
   assign idx2 = in[5:3];
   assign idx3 = in[8:6];
   assign idx4 = in[11:9];
   assign idx5 = in[14:12];
   
   
   
   logic [3:0] 			 utmp1;
   logic [3:0] 			 utmp2;
   logic [3:0] 			 utmp3;
   logic [3:0] 			 utmp4;

   logic signed [3:0] 		 stmp1;
   logic signed [3:0] 		 stmp2;
   logic signed [3:0] 		 stmp3;
   logic signed [3:0] 		 stmp4;

   
   assign utmp1 = { in[24:15] } [2];
   assign utmp2 = { in[34:25] } [2:0];
   assign utmp3 = { in[44:35] } [idx1+:3];
   assign utmp4 = { in[54:45] } [idx2-:3];

   assign stmp1 = { in[64:55] } [2];
   assign stmp2 = { in[74:65] } [2:0];
   assign stmp3 = { in[84:75] } [idx1+:3];
   assign stmp4 = { in[94:85] } [idx2-:3];

   logic [7:0] 			 uout1;
   logic [7:0] 			 uout2;
   logic [7:0] 			 uout3;
   logic [7:0] 			 uout4;
   logic [7:0] 			 uout5;
   logic [7:0] 			 uout6;
   logic [7:0] 			 uout7;
   logic [7:0] 			 uout8;

   logic signed [7:0] 		 sout1;
   logic signed [7:0] 		 sout2;
   logic signed [7:0] 		 sout3;
   logic signed [7:0] 		 sout4;
   logic signed [7:0] 		 sout5;
   logic signed [7:0] 		 sout6;
   logic signed [7:0] 		 sout7;
   logic signed [7:0] 		 sout8;


   assign uout1 = { utmp1, utmp2, utmp3, utmp4 } [idx3];
   assign uout2 = { utmp1, utmp2, utmp3, utmp4 } [13:6];
   assign uout3 = { utmp1, utmp2, utmp3, utmp4 } [idx4+:6];
   assign uout4 = { utmp1, utmp2, utmp3, utmp4 } [idx5+4-:6];

   assign uout5 = { stmp1, stmp2, stmp3, stmp4 } [idx3];
   assign uout6 = { stmp1, stmp2, stmp3, stmp4 } [13:6];
   assign uout7 = { stmp1, stmp2, stmp3, stmp4 } [idx4+:6];
   assign uout8 = { stmp1, stmp2, stmp3, stmp4 } [idx5+4-:6];

   assign sout1 = { utmp1, utmp2, utmp3, utmp4 } [idx3];
   assign sout2 = { utmp1, utmp2, utmp3, utmp4 } [13:6];
   assign sout3 = { utmp1, utmp2, utmp3, utmp4 } [idx4+:6];
   assign sout4 = { utmp1, utmp2, utmp3, utmp4 } [idx5+4-:6];

   assign sout5 = { stmp1, stmp2, stmp3, stmp4 } [idx3];
   assign sout6 = { stmp1, stmp2, stmp3, stmp4 } [13:6];
   assign sout7 = { stmp1, stmp2, stmp3, stmp4 } [idx4+:6];
   assign sout8 = { stmp1, stmp2, stmp3, stmp4 } [idx5+4-:6];

   assign out = { uout1,
		  uout2,
   		  uout3,
		  uout4,
		  uout5,
		  uout6,
		  uout7,
		  uout8,
		  sout1,
		  sout2,
		  sout3,
		  sout4,
		  sout5,
		  sout6,
		  sout7,
		  sout8 };

endmodule // spec
