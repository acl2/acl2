// ESIM Symbolic Hardware Simulator
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



// REG1: Probably the simplest possible register in Verilog, lacking even an
// enable wire or any kinds of reset stuff.

module reg1 (q, d, clk);
  parameter width = 1;
  output [width-1:0] q;
  input [width-1:0]  d;
  input 	     clk;

  reg [width-1:0]    q;
  always @(posedge clk)
    q <= d;

endmodule



// EREG*: Various ways to write a very basic register with an enable signal.

module ereg1 (q, d, en, clk);
  parameter width = 1;
  output [width-1:0] q;
  input [width-1:0]  d;
  input 	     en;
  input 	     clk;

  // This is a perfectly good way to write the register, which is well-behaved
  // in Verilog and in our E translation.
  wire [width-1:0]   next = en ? d : q;
  reg1 #(width) r (q, next, clk);

endmodule

module ereg2 (q, d, en, clk);
  parameter width = 1;
  output [width-1:0] q;
  input [width-1:0]  d;
  input 	     en;
  input 	     clk;

  // This is also a perfectly good way to write the register, and is
  // well-behaved in both Verilog and in our E translation.
  reg [width-1:0]    q;
  always @(posedge clk)
    q <= en ? d : q;

endmodule

module ereg3 (q, d, en, clk);
  parameter width = 1;
  output [width-1:0] q;
  input [width-1:0]  d;
  input 	     en;
  input 	     clk;

  // This is a pretty lousy way to define a register, because the Verilog
  // semantics of IF statements are very bad.  For instance, during simulation,
  // if the enable signal goes to X then the Verilog simulator will act as
  // though the register is disabled.  This is very unsafe!
  //
  // For our translation to E, though, this will be treated as equivalent to
  // the other eregs.

  reg [width-1:0]    q;
  always @(posedge clk)
    if (en) q <= d;

endmodule


module ereg4 (q, d, en, clk);
  parameter width = 1;
  output [width-1:0] q;
  input [width-1:0]  d;
  input 	     en;
  input 	     clk;

  // This is even worse than ereg3 for similar reasons.  The semantics of CASE
  // in Verilog are quite bad.  However, for E translation it is basically just
  // as good as the other registers.

  reg [width-1:0]    q;
  always @(posedge clk)
    case (en)
      1'b1:    q <= d;
    endcase

endmodule

module ereg5 (q, d, en, clk);
  parameter width = 1;
  output [width-1:0] q;
  input [width-1:0]  d;
  input 	     en;
  input 	     clk;

  // A slight variant of ereg4.  Not good for Verilog simulation, but fine for
  // E translation.
  reg [width-1:0]    q;
  always @(posedge clk)
    case (en)
      1'b1:    q <= d;
      default: ;
    endcase

endmodule

module ereg6 (q, d, en, clk);
  parameter width = 1;
  output [width-1:0] q;
  input [width-1:0]  d;
  input 	     en;
  input 	     clk;

  // Another slight variant of ereg4.  Not good for Verilog simulation, but
  // fine for E translation.
  reg [width-1:0]    q;
  always @(posedge clk)
    case (en)
      1'b1:    q <= d;
      default: q <= q;
    endcase
endmodule



// MREG*: Various ways to write a register with a built-in mux and an enable.

module mreg1 (q, sel, d1, d0, en, clk);
  parameter width = 1;
  output [width-1:0] q;
  input [width-1:0]  d1, d0;
  input 	     sel, en;
  input 	     clk;

  // This is a perfectly good way to write the register, which is well-behaved
  // in Verilog and in our E translation.
  wire [width-1:0]   d = sel ? d1 : d0;
  wire [width-1:0]   next = en ? d : q;
  reg1 #(width) r (q, next, clk);

endmodule

module mreg2 (q, sel, d1, d0, en, clk);
  parameter width = 1;
  output [width-1:0] q;
  input [width-1:0]  d1, d0;
  input 	     sel, en;
  input 	     clk;

  // This should be entirely equivalent, and well-behaved in both Verilog and
  // in our E translation.
  reg [width-1:0]    q;
  always @(posedge clk)
    q <= en
	  ? (sel ? d1 : d0)
          : q;

endmodule

module mreg3 (q, sel, d1, d0, en, clk);
  parameter width = 1;
  output [width-1:0] q;
  input [width-1:0]  d1, d0;
  input 	     sel, en;
  input 	     clk;

  // This is a lousy way to write it because of the semantics of IF statements,
  // and it will behave badly when EN or SEL are X.  But in our E translation
  // it should be equivalent.

  reg [width-1:0]    q;
  always @(posedge clk)
    begin
      if (en)
	begin
	  if (sel)
	    q <= d1;
	  else
	    q <= d0;
	end
    end

endmodule


module mreg4 (q, sel, d1, d0, en, clk);
  parameter width = 1;
  output [width-1:0] q;
  input [width-1:0]  d1, d0;
  input 	     sel, en;
  input 	     clk;

  // This is also bad in Verilog simulations because CASE statements have
  // bad semantics, but we treat it as equivalent in our E translation.

  reg [width-1:0]    q;
  always @(posedge clk)
    begin
      case( {en,sel} )
	2'b11: q <= d1;
	2'b10: q <= d0;
      endcase
    end

endmodule


module mreg5 (q, sel, d1, d0, en, clk);
  parameter width = 1;
  output [width-1:0] q;
  input [width-1:0]  d1, d0;
  input 	     sel, en;
  input 	     clk;

  // This is also bad in Verilog simulations because CASE statements have
  // bad semantics, but we treat it as equivalent in our E translation.

  reg [width-1:0]    q;
  always @(posedge clk)
    begin
      case(en)
	1'b1:
	  case(sel)
	    1'b1: q <= d1;
	    1'b0: q <= d0;
	  endcase
      endcase
    end

endmodule






// Stupid test bench module that doesn't do anything useful, but instantiates
// the above parameterized modules at various widths, so that VL will
// unparameterize them.

module test () ;

  wire clk, en, sel;

  wire q1, d1;
  wire [1:0] q2, d2;
  wire [3:0] q4, d4;

  reg1 r1a (q1, d1, clk);
  reg1 #(2) r1b (q2, d2, clk);
  reg1 #(4) r1c (q4, d4, clk);


  ereg1 er1a (q1, d1, en, clk);
  ereg1 #(2) er1b (q2, d2, en, clk);
  ereg1 #(4) er1c (q4, d4, en, clk);

  ereg2 er2a (q1, d1, en, clk);
  ereg2 #(2) er2b (q2, d2, en, clk);
  ereg2 #(4) er2c (q4, d4, en, clk);

  ereg3 er3a (q1, d1, en, clk);
  ereg3 #(2) er3b (q2, d2, en, clk);
  ereg3 #(4) er3c (q4, d4, en, clk);

  ereg4 er4a (q1, d1, en, clk);
  ereg4 #(2) er4b (q2, d2, en, clk);
  ereg4 #(4) er4c (q4, d4, en, clk);

  ereg5 er5a (q1, d1, en, clk);
  ereg5 #(2) er5b (q2, d2, en, clk);
  ereg5 #(4) er5c (q4, d4, en, clk);

  ereg6 er6a (q1, d1, en, clk);
  ereg6 #(2) er6b (q2, d2, en, clk);
  ereg6 #(4) er6c (q4, d4, en, clk);


  mreg1 mr1a (q1, sel, d1, d1, en, clk);
  mreg1 #(2) mr1b (q2, sel, d2, d2, en, clk);
  mreg1 #(4) mr1c (q4, sel, d4, d4, en, clk);

  mreg2 mr2a (q1, sel, d1, d1, en, clk);
  mreg2 #(2) mr2b (q2, sel, d2, d2, en, clk);
  mreg2 #(4) mr2c (q4, sel, d4, d4, en, clk);

  mreg3 mr3a (q1, sel, d1, d1, en, clk);
  mreg3 #(2) mr3b (q2, sel, d2, d2, en, clk);
  mreg3 #(4) mr3c (q4, sel, d4, d4, en, clk);

  mreg4 mr4a (q1, sel, d1, d1, en, clk);
  mreg4 #(2) mr4b (q2, sel, d2, d2, en, clk);
  mreg4 #(4) mr4c (q4, sel, d4, d4, en, clk);

  mreg5 mr5a (q1, sel, d1, d1, en, clk);
  mreg5 #(2) mr5b (q2, sel, d2, d2, en, clk);
  mreg5 #(4) mr5c (q4, sel, d4, d4, en, clk);

endmodule
