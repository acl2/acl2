// VL 2014 -- Verilog Toolkit, 2014 Edition
// Copyright (C) 2008-2015 Centaur Technology
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
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
//   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>

// more tests of port handling

`ifdef VL_SYSTEST_VCS
  // VCS doesn't seem to like "var" inputs, so use `VAR instead and just make it
  // empty for VCS.
 `define VAR
`else
 `define VAR var
`endif



`ifdef SYSTEM_VERILOG_MODE

module MA (output logic [3:0] out,
           input wire [3:0]  in1,
           input logic [3:0] in2);
  parameter foo = 1;
  wire make_foo_matter = foo;
  always @(in1 or in2)
  begin
    out = in1[1] ? (in1 ^ in2) : (in1 & in2);
  end
endmodule

module MB (output logic [3:0] out,
           input `VAR [3:0] in1, in2);
  parameter foo = 1;
  wire make_foo_matter = foo;
  always @(in1 or in2) out = in1[0] ? (in1 | in2) : (in1 & in2);
endmodule

module MC (output `VAR logic [3:0] out1, out2,
           input logic [3:0] in1, in2);
  parameter foo = 1;
  wire make_foo_matter = foo;
  always @(in1 or in2) out1 = in1[2] ? (in1 ^ in2) : (in1 & in2);
  assign out2 = ~out1;
endmodule

module MD (output reg [3:0] out,
           input logic [3:0] in1,
           input wire [3:0] in2);
  parameter foo = 1;
  wire make_foo_matter = foo;
  always @(in1 or in2) out = in1[1] ? (in1 ^ in2) : (in1 & in2);
endmodule

module ME (output logic [3:0] out,
           input logic [3:0] in1,
           input [3:0] in2);
  parameter foo = 1;
  wire make_foo_matter = foo;
  always @(in1 or in2) out = in1[1] ? (in1 < in2) : (in1 * in2);
endmodule

module MF (output `VAR reg [3:0] out,
           input signed [3:0] in1, in2);
  parameter foo = 1;
  wire make_foo_matter = foo;
  always @(in1 or in2) out = in1[1] ? (in1 < in2) : (in1 % in2);
endmodule

module MG (output wire [3:0] out,
           input `VAR logic signed [3:0] in1, in2);
  parameter foo = 1;
  wire make_foo_matter = foo;
  assign out = in1[1] ? (in1 < in2) : (in1 % in2);
endmodule

module MH (output [3:0] out,
           input logic signed [3:0] in1, in2);
  parameter foo = 1;
  wire make_foo_matter = foo;
  assign out = in1[1] ? (in1 < in2) : (in1 / in2);
endmodule


/*+VL

// Silly checks, these should fail because in2 is not declared.
module ShouldFail1(output [3:0] out);
  wire [1:0] in1;
  MA ainst(.*);
endmodule

module ShouldFail2(output [3:0] out);
  wire [1:0] in1;
  MA ainst(.out, .in1, .in2);
endmodule

module ShouldFail4(output [3:0] out);
  wire [1:0] in1;
  MA ainst(.out, .in1, .*);
endmodule

// This one isn't fatal.
module ShouldWarn(output [3:0] out);
  wire [3:0] in1;
  MA ainst(.out, .in1);
endmodule

*/


module dut (

in1, in2,

aout1, aout2, aout3,
bout1, bout2, bout3, bout4, bout5, bout6, bout7,
cout1, cout2, cout3, cout4, cout5, cout6, cout7,
dout1, dout2, dout3, dout4, dout5, dout6, dout7,
eout1, eout2, eout3, eout4, eout5, eout6, eout7,
fout1, fout2, fout3, fout4, fout5, fout6, fout7,
gout1, gout2, gout3, gout4, gout5, gout6, gout7,
hout1, hout2, hout3, hout4, hout5, hout6, hout7,
iout1, iout2, iout3, iout4, iout5, iout6, iout7


);

  parameter size = 1;
  wire [size-1:0] make_size_matter;

  input [3:0] 	   in1, in2;
  output [3:0] 	   aout1, aout2, aout3;

  MA ainst1 (aout1, in1, in2);                   // positional connections
  MA ainst2 (.out(aout2), .in1(in1), .in2(in2)); // named connections
  MA ainst3 (.in1(in1), .out(aout3), .in2(in2)); // reordered, named connections

  output [3:0] 	   bout1, bout2, bout3, bout4, bout5, bout6, bout7;
  MB binst1 (bout1, in1, in2);                             // positional connections
  MB binst2 (.out(bout2), .in1(in1), .in2(in2));           // named connections
  MB binst3 (.in1(in2), .out(bout3), .in2(in1));           // reordered, named connections
  MB binst4 (.in1(4'b1100), .out(bout4), .in2(in1));       // fixed constant on input port
  MB binst5 (.in1(4'b1100 + in2), .out(bout5), .in2(in1)); // expression to input port
  MB binst6 (.in1, .out(bout6), .in2);                     // name-only connections
  MB binst7 (.out(bout7), .in1, .in2(in1));

  output [3:0] 	   cout1, cout2, cout3, cout4, cout5, cout6, cout7;
  MC cinst1 (cout1, cout2, in1, in2);
  MC cinst2 (.out1(cout3), .out2(cout4), .in1(in1), .in2(in2));
  MC cinst3 (.out1(cout5), .in1(in1), .in2(in2), .out2(cout6));
  MC cinst4 (.out1(cout7), .in1(in1 + 4'b1001), .in2(in2), .out2());

  output [3:0] 	   dout1, dout2, dout3, dout4, dout5, dout6, dout7;
  MD dinst1 (dout1, in1, in2);
  MD dinst2 (.out(dout2), .in1(in1), .in2(in2));
  MD dinst3 (.in1(in1), .in2(in2), .out(dout3));
  MD dinst4 (.in1(in1 + 1'd1), .in2(in2), .out(dout4));
  MD dinst5 (.in1(in1 + 1'sd1), .in2(in2), .out(dout5));
  MD dinst6 (.in1(in1 + 1'sd1), .in2, .out(dout6));
  MD dinst7 (.in1(in1 + 1'd1), .out(dout7), .in2);

  output [3:0] 	   eout1, eout2, eout3, eout4, eout5, eout6, eout7;
  ME einst1 (eout1, in1, in2);
  ME einst2 (.out(eout2), .in1(in1), .in2(in2));
  ME einst3 (.in1(in1), .in2(in2), .out(eout3));
  ME einst4 (.in1(in1 + 1'd1), .in2(in2), .out(eout4));
  ME einst5 (.in1(in1 + 1'sd1), .in2(in2), .out(eout5));
  assign eout6 = 0;
  assign eout7 = 0;

  output [3:0] 	   fout1, fout2, fout3, fout4, fout5, fout6, fout7;
  MF finst1 (fout1, in1, in2);
  MF finst2 (.out(fout2), .in1(in1), .in2(in2));
  MF finst3 (.in1(in1), .in2(in2), .out(fout3));
  MF finst4 (.in1(in1 + 1'd1), .in2(in2), .out(fout4));
  MF finst5 (.in1(in1 + 1'sd1), .in2(in2), .out(fout5));
  MF finst6 (.out(fout6), .*);
  MF finst7 (.out(fout7),
                         `ifdef VL_SYSTEST_VCS
                         // VCS doesn't permit using .foo with .*
                         .in1(in1)
                         `else
                         .in1
                         `endif,
                .*);

  output [3:0] 	   gout1, gout2, gout3, gout4, gout5, gout6, gout7;
  MG ginst1 (gout1, in1, in2);
  MG ginst2 (.out(gout2), .in1(in1), .in2(in2));
  MG ginst3 (.in1(in1), .in2(in2), .out(gout3));
  MG ginst4 (.in1(in1 + 1'd1), .in2(in2), .out(gout4));
  MG ginst5 (.in1(in1 + 1'sd1), .in2(in2), .out(gout5));
  assign gout6 = 0;
  assign gout7 = 0;

  output [3:0] 	   hout1, hout2, hout3, hout4, hout5, hout6, hout7;
  MH hinst1 (hout1, in1, in2);
  MH hinst2 (.out(hout2), .in1(in1), .in2(in2));
  MH hinst3 (.in1(in1), .in2(in2), .out(hout3));
  MH hinst4 (.in1(in1 + 1'd1), .in2(in2), .out(hout4));
  MH hinst5 (.in1(in1 + 1'sd1), .in2(in2), .out(hout5));
  assign hout6 = 0;
  assign hout7 = 0;

  output [3:0] 	   iout1, iout2, iout3, iout4, iout5, iout6, iout7;
  assign iout1 = 0;
  assign iout2 = 0;
  assign iout3 = 0;
  assign iout4 = 0;
  assign iout5 = 0;
  assign iout6 = 0;
  assign iout7 = 0;


endmodule


/*+VL

module make_tests () ;

wire [3:0] in1, in2,
 aout1, aout2, aout3,
 bout1, bout2, bout3, bout4, bout5, bout6, bout7,
 cout1, cout2, cout3, cout4, cout5, cout6, cout7,
 dout1, dout2, dout3, dout4, dout5, dout6, dout7,
 eout1, eout2, eout3, eout4, eout5, eout6, eout7,
 fout1, fout2, fout3, fout4, fout5, fout6, fout7,
 gout1, gout2, gout3, gout4, gout5, gout6, gout7,
 hout1, hout2, hout3, hout4, hout5, hout6, hout7,
 iout1, iout2, iout3, iout4, iout5, iout6, iout7;

 dut #(1) dir_test_1 ( in1, in2,
 aout1, aout2, aout3,
 bout1, bout2, bout3, bout4, bout5, bout6, bout7,
 cout1, cout2, cout3, cout4, cout5, cout6, cout7,
 dout1, dout2, dout3, dout4, dout5, dout6, dout7,
 eout1, eout2, eout3, eout4, eout5, eout6, eout7,
 fout1, fout2, fout3, fout4, fout5, fout6, fout7,
 gout1, gout2, gout3, gout4, gout5, gout6, gout7,
 hout1, hout2, hout3, hout4, hout5, hout6, hout7,
 iout1, iout2, iout3, iout4, iout5, iout6, iout7
 );

endmodule

*/

`endif
