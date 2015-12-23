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
// Original authors: Sol Swords <sswords@centtech.com>
//                   Jared Davis <jared@centtech.com>

package foo ;
  parameter [3:0] five = 5;
endpackage

package bar ;
  parameter [3:0] six = 6;
endpackage


module spec (input logic [127:0] in,
	     output wire [127:0] out);

  // This is a test of a lot of scoping stuff with for generates.

  parameter version = 1;

  begin
    // Unnamed block -- doesn't introduce its own scope
    wire [3:0] aa = in[3:0];
    localparam [3:0] aa2 = 3;
    import foo::five;
  end

  begin : named
    // Named block has its own scope, so there's no name clash
    wire [3:0] aa = in[7:4];
  end

  generate
    begin
      // Unnamed block doesn't introduce its own scope
      genvar i;
      wire [3:0] ww = in[11:8];
      wire [3:0] vv;
      for(i = 0; i < 4;++i)
      begin
	not(vv[i], ww[i]);
      end
      import bar::*;
    end
  endgenerate

  begin : named2
    // Named block introduces a new scope, so there's no name clash
    genvar i;
    wire [3:0] ww = in[15:12];
    wire [3:0] vv;
    for(i = 0; i < 4;++i)
    begin
      not(vv[i], ww[i]);
    end
  end

  wire [15:0] ifelse_stuff;

  if (version == 1)
  begin : ifelsename
    // New scope here, so no name clash.
    wire [3:0] ww3 = in[19:16];
    wire [3:0] aa = ~ww3;
    assign ifelse_stuff = { ww3, aa };
  end
  else if (version == 2)
  begin : ifelsename
    // New scope here, so no name clash.
    wire [3:0] ww3 = in[23:20];
    wire [3:0] aa = ~ww3;
    assign ifelse_stuff = { ww3, aa };
  end

// Same thing without the blocks being named:

  wire [15:0] ifelse_stuff2;

  if (version == 1)
  begin
    // New scope here, so no name clash.
    wire [3:0] ww3 = in[58:54];
    wire [3:0] aa = ~ww3;
    assign ifelse_stuff2 = { ww3, aa };
  end
  else if (version == 2)
  begin
    // New scope here, so no name clash.
    wire [3:0] ww3 = in[53:50];
    wire [3:0] aa = ~ww3;
    assign ifelse_stuff2 = { ww3, aa };
  end


  wire [15:0]  case_stuff;

  case (version)
    1 :
    // New scope here, so no name clash.
    begin : casename
      wire ww4 = in[27:24];
      wire [3:0] aa = ww4;
      assign case_stuff = { ww4, aa };
    end

    2 :
    begin : casename
      // New scope here, so no name clash.
      wire ww4 = in[31:28];
      wire [3:0] aa = ww4;
      assign case_stuff = { ww4, aa };
    end

  endcase


  // Same thing without the blocks being named

  wire [15:0]  case_stuff2;

  case (version)
    1 :
    // New scope here, so no name clash.
    begin
      wire ww4 = in[63:60];
      wire [3:0] aa = ww4;
      assign case_stuff2 = { ww4, aa };
    end

    2 :
    begin
      // New scope here, so no name clash.
      wire ww4 = in[68:64];
      wire [3:0] aa = ww4;
      assign case_stuff2 = { ww4, aa };
    end

  endcase


  for(genvar j = 0;j < 3;++j)
  begin : subblock
    // New scope here, so no name clash
    wire [3:0] ww5 = in[(32+j) +: 4];
    wire [3:0] aa = ww5 + j;
  end

  assign out = { six, five,
                 subblock[2].ww5,
                 subblock[1].ww5,
                 subblock[0].ww5,
                 subblock[2].aa,
                 subblock[1].aa,
                 subblock[0].aa,
                 case_stuff,
                 case_stuff2,
		 ifelse_stuff,
		 ifelse_stuff2,
		 named2.vv, named2.ww,
		 vv, ww,
		 named.aa,
		 aa2, aa } ;

endmodule

