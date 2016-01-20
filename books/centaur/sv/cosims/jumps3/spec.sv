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
	     output [127:0] out);

  typedef enum logic[2:0] { continue0, break0, return0,
			    continue1, break1, return1,
			    fallthrough, init
			   }  path_t;

   typedef path_t pathgroup_t [8];

   function automatic pathgroup_t trace (input logic [5:0] in [8]);
     // Just generally nasty
     integer count = 0;
     pathgroup_t reached;
     for(integer i = 0; i < 8;++i) begin

       reached[i] = init;

       if (in[i][0]) begin reached[i] = continue0; continue; end
       if (in[i][1]) begin reached[i] = break0; break; end
       if (in[i][2]) begin reached[i] = return0; return reached; end

       if (in[i][3]) begin reached[i] = continue1; continue; end
       if (in[i][4]) begin reached[i] = break1; break; end
       if (in[i][5]) begin reached[i] = return1; return reached; end

       reached[i] = fallthrough;

     end
     return reached;
  endfunction


  logic [5:0] ins1 [8];
  assign ins1 = {>> {in[47:0]}};
  logic [5:0] ins2 [8];
  assign ins2 = {>> {in[95:48]}};
   
   assign out[63:0] = {>> {trace(ins1)}};
   assign out[127:64] = {>> {trace(ins2)}};

			      
endmodule // spec

