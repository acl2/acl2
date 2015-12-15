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


module rfl #(e=2, r=1) (input [r-1:0][15:0] in,
	       	       output [r-1:0][15:0] out);

`define cb ( ( e ) / r)

   for (genvar rp=0; rp<r; rp++)
     begin
       // if (rp == (r-1)) begin
       
	   //  wire [e - ( r * `cb )-1 : 0] i = in[rp];
	   //  wire [e - ( r * `cb )-1 : 0] o;
	   //  assign out[rp] = o;
	   // fff #( e - ( r * `cb ) ) foo (o, i);

	 localparam w = e - ( r * `cb ) + 1;
	    wire [w-1 : 0] i = in[rp];
	    wire [w-1 : 0] o;
	    assign out[rp] = o;
	   fff #( w ) foo (o, i);

	   initial begin
	    #10;
	    $display("rp: %d, $bits(i): %d, expr: %d, w: %d", rp, $bits(i), e - ( r * `cb ), w);
           end
       // 	 end
       // else
       // begin
       // 	    wire [`cb-1 : 0] i = in[rp];
       // 	    wire [`cb-1 : 0] o;
       // 	    assign out[rp] = o;
       // 	    fff #( `cb ) foo (o, i);
       // 	   initial begin
       // 	    #10;
       // 	    $display("rp: %d, $bits(i): %d, cb: %d", rp, $bits(i), `cb);
       //     end
       // end
     end

endmodule // rfl

module fff #(w=64) (output [w-1:0] f,
		    input [w-1:0] v);

  genvar i;
   for (i=0; i<w; i++)
     if (i==0)
       assign f[i] = f[i];
     else
       assign f[i] = ~v[i];

endmodule



module spec (input logic [127:0] in,
	     output logic [127:0] out);

   wire [2:0][15:0] i = in;
   wire [2:0][15:0] o;
    assign out = 0;

   rfl rflinst (i, o);

endmodule // spec
