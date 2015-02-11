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

// Using a global random seed seems like a good idea -- When each instance of
// randomBit2 had its own seed, they seemed to just always produce the same
// values on NCVerilog, which was terrible.

module random_top ();
  integer seed;
endmodule

module randomBit2 (q) ;
  // Generates a random two-valued bit every #DELAY ticks.
  parameter delay = 1;
  output q;
  reg q;
  always #delay q <= $random(random_top.seed);
endmodule

module randomVec2 (q);
  // Generates a WIDTH-bit random two-valued vector every #DELAY ticks.
  parameter width = 1;
  parameter delay = 1;
  output [width-1:0] q;
  randomBit2 #(delay) core [width-1:0] (q[width-1:0]);
endmodule

module randomBit4 (q) ;
  // Generates a random four-valued bit every #DELAY ticks.
  parameter delay = 1;
  output q;
  reg [1:0] r;
  always #delay r <= $random(random_top.seed);
  assign q = (r == 2'b 00) ? 1'b0
	   : (r == 2'b 01) ? 1'b1
	   : (r == 2'b 10) ? 1'bX
           :                 1'bZ;
endmodule

module randomVec4 (q);
  // Generates an WIDTH-bit random four-valued vector every #DELAY ticks.
  parameter width = 1;
  parameter delay = 1;
  output [width-1:0] q;
  randomBit4 #(delay) core [width-1:0] (q[width-1:0]);
endmodule


module test () ;

  // This is a hard test bench to write.
  //
  // Problem 1.  Verilog semantics for four-valued clocks are, well, insane.
  // For instance, an X -> 1 transition is considered a posedge.  Because of
  // this sort of thing, we only try to show that our translated flops simulate
  // the same for a two-valued clock.  BOZO can we lift this restriction?
  //
  //
  // Problem 2.  Even the most basic flop imaginable, say:
  //
  //   always @(posedge clk) q <= d;     // "original"
  //
  // has a race condition(!) in Verilog when (posedge clk) happens at the same
  // time as d is changing.  This race condition ends up biting us because
  // "obviously" equivalent things, e.g.,
  //
  //   wire d_next = d;
  //   always @(posedge clk) q <= d;
  //
  // Can end up behaving differently than "original."  That's too bad, because
  // it means that if we want to write tests to show that our translated flops
  // simulate in the same way as the original flops, we have to set up our test
  // code to make sure that the data and clock don't simultaneously change.
  //
  //
  // Problem 3.  Verilog semantics for if-statements are also insane.  Because
  // of this, we only test that our translated G flops (which include
  // conditionals) are conservative approximations of the originals.



  // Basic scheme:
  // All inputs change together (randomly) every 3 ticks.
  // CLK is delayed to 1 tick later than the other inputs.

  wire clk_pre;
  wire [3:0] d1, d2, d3;
  wire 	     en;

  randomBit2 #(3)   mk_clk (clk_pre);
  randomBit4 #(3)   mk_en  (en);
  randomVec4 #(4,3) mk_d1  (d1);
  randomVec4 #(4,3) mk_d2  (d2);
  randomVec4 #(4,3) mk_d3  (d3);

  // Delayed clock to ensure that the clock doesn't change at the same time
  // as the other inputs; see Problem 2 above.
  wire #1 clk = clk_pre;

  // one-bit random data elements for one-bit tests
  wire c1 = d1[0];
  wire c2 = d2[0];
  wire c3 = d3[0];

  // F Modules -- Size 1 Tests
  wire spec_f1q1, spec_f1q2;
  wire impl_f1q1, impl_f1q2;
  f1         f1spec (spec_f1q1, spec_f1q2, c1, c2, clk);
  \f1$size=1 f1impl (impl_f1q1, impl_f1q2, c1, c2, clk);
  wire ok_f1q1 = spec_f1q1 === impl_f1q1;
  wire ok_f1q2 = spec_f1q2 === impl_f1q2;
  wire ok_f1 = ok_f1q1 & ok_f1q2;

  wire spec_f2q1, spec_f2q2;
  wire impl_f2q1, impl_f2q2;
  f2         f2spec (spec_f2q1, spec_f2q2, c1, c2, clk);
  \f2$size=1 f2impl (impl_f2q1, impl_f2q2, c1, c2, clk);
  wire ok_f2q1 = spec_f2q1 === impl_f2q1;
  wire ok_f2q2 = spec_f2q2 === impl_f2q2;
  wire ok_f2 = ok_f2q1 & ok_f2q2;

  wire spec_f3q1, spec_f3q2;
  wire impl_f3q1, impl_f3q2;
  f3         f3spec (spec_f3q1, spec_f3q2, c1, c2, clk);
  \f3$size=1 f3impl (impl_f3q1, impl_f3q2, c1, c2, clk);
  wire ok_f3q1 = spec_f3q1 === impl_f3q1;
  wire ok_f3q2 = spec_f3q2 === impl_f3q2;
  wire ok_f3 = ok_f3q1 & ok_f3q2;

  wire okf = &{ok_f1, ok_f2, ok_f3};


  // G Modules -- Size 1 Tests
  wire spec_g1q1, spec_g1q2;
  wire impl_g1q1, impl_g1q2;
  g1         g1spec (spec_g1q1, spec_g1q2, c1, c2, en, clk);
  \g1$size=1 g1impl (impl_g1q1, impl_g1q2, c1, c2, en, clk);
  wire ok_g1q1 = (spec_g1q1 === impl_g1q1) | (impl_g1q1 === 1'bx);
  wire ok_g1q2 = (spec_g1q2 === impl_g1q2) | (impl_g1q2 === 1'bx);
  wire ok_g1 = ok_g1q1 & ok_g1q2;

  wire spec_g2q1, spec_g2q2, spec_g2q3;
  wire impl_g2q1, impl_g2q2, impl_g2q3;
  g2         g2spec (spec_g2q1, spec_g2q2, spec_g2q3, c1, c2, en, clk);
  \g2$size=1 g2impl (impl_g2q1, impl_g2q2, impl_g2q3, c1, c2, en, clk);
  wire ok_g2q1 = (spec_g2q1 === impl_g2q1) | (impl_g2q1 === 1'bx);
  wire ok_g2q2 = (spec_g2q2 === impl_g2q2) | (impl_g2q2 === 1'bx);
  wire ok_g2q3 = (spec_g2q3 === impl_g2q3) | (impl_g2q3 === 1'bx);
  wire ok_g2 = ok_g2q1 & ok_g2q2 & ok_g2q3;

  wire spec_g3q1, spec_g3q2;
  wire impl_g3q1, impl_g3q2;
  g3         g3spec (spec_g3q1, spec_g3q2, c1, c2, en, clk);
  \g3$size=1 g3impl (impl_g3q1, impl_g3q2, c1, c2, en, clk);
  wire ok_g3q1 = (spec_g3q1 === impl_g3q1) | (impl_g3q1 === 1'bx);
  wire ok_g3q2 = (spec_g3q2 === impl_g3q2) | (impl_g3q2 === 1'bx);
  wire ok_g3 = ok_g3q1 & ok_g3q2;

  wire spec_g4q1, spec_g4q2;
  wire impl_g4q1, impl_g4q2;
  g4         g4spec (spec_g4q1, spec_g4q2, c1, c2, en, clk);
  \g4$size=1 g4impl (impl_g4q1, impl_g4q2, c1, c2, en, clk);
  wire ok_g4q1 = (spec_g4q1 === impl_g4q1) | (impl_g4q1 === 1'bx);
  wire ok_g4q2 = (spec_g4q2 === impl_g4q2) | (impl_g4q2 === 1'bx);
  wire ok_g4 = ok_g4q1 & ok_g4q2;

  wire spec_g5q1, spec_g5q2;
  wire impl_g5q1, impl_g5q2;
  g5         g5spec (spec_g5q1, spec_g5q2, c1, c2, en, clk);
  \g5$size=1 g5impl (impl_g5q1, impl_g5q2, c1, c2, en, clk);
  wire ok_g5q1 = (spec_g5q1 === impl_g5q1) | (impl_g5q1 === 1'bx);
  wire ok_g5q2 = (spec_g5q2 === impl_g5q2) | (impl_g5q2 === 1'bx);
  wire ok_g5 = ok_g5q1 & ok_g5q2;

  wire spec_g6q1, spec_g6q2;
  wire impl_g6q1, impl_g6q2;
  g6         g6spec (spec_g6q1, spec_g6q2, c1, c2, en, clk);
  \g6$size=1 g6impl (impl_g6q1, impl_g6q2, c1, c2, en, clk);
  wire ok_g6q1 = (spec_g6q1 === impl_g6q1) | (impl_g6q1 === 1'bx);
  wire ok_g6q2 = (spec_g6q2 === impl_g6q2) | (impl_g6q2 === 1'bx);
  wire ok_g6 = ok_g6q1 & ok_g6q2;

  wire okg = &{ok_g1, ok_g2, ok_g3, ok_g4, ok_g5, ok_g6};



  // F Modules -- Size 4 Tests
  wire [3:0] spec_f1wq1, spec_f1wq2;  // "f1 wide q1", "f1 wide q2", ...
  wire [3:0] impl_f1wq1, impl_f1wq2;
  f1 #(4)    f1wspec (spec_f1wq1, spec_f1wq2, d1, d2, clk);
  \f1$size=4 f1wimpl (impl_f1wq1, impl_f1wq2, d1, d2, clk);
  wire ok_f1wq1 = spec_f1wq1 === impl_f1wq1;
  wire ok_f1wq2 = spec_f1wq2 === impl_f1wq2;
  wire ok_f1w = ok_f1wq1 & ok_f1wq2;

  wire [3:0] spec_f2wq1, spec_f2wq2;  // "f2 wide q1", "f2 wide q2", ...
  wire [3:0] impl_f2wq1, impl_f2wq2;
  f2 #(4)    f2wspec (spec_f2wq1, spec_f2wq2, d1, d2, clk);
  \f2$size=4 f2wimpl (impl_f2wq1, impl_f2wq2, d1, d2, clk);
  wire ok_f2wq1 = spec_f2wq1 === impl_f2wq1;
  wire ok_f2wq2 = spec_f2wq2 === impl_f2wq2;
  wire ok_f2w = ok_f2wq1 & ok_f2wq2;

  wire [3:0] spec_f3wq1, spec_f3wq2;  // "f3 wide q1", "f3 wide q2", ...
  wire [3:0] impl_f3wq1, impl_f3wq2;
  f3 #(4)    f3wspec (spec_f3wq1, spec_f3wq2, d1, d2, clk);
  \f3$size=4 f3wimpl (impl_f3wq1, impl_f3wq2, d1, d2, clk);
  wire ok_f3wq1 = spec_f3wq1 === impl_f3wq1;
  wire ok_f3wq2 = spec_f3wq2 === impl_f3wq2;
  wire ok_f3w = ok_f3wq1 & ok_f3wq2;

  wire okfw = &{ok_f1w, ok_f2w, ok_f3w};



  function approximates_p;
    input [3:0] spec;
    input [3:0] impl;
    approximates_p = (spec === impl) |
		     (&{ spec[0] === impl[0] | impl[0] === 1'bx,
                         spec[1] === impl[1] | impl[1] === 1'bx,
                         spec[2] === impl[2] | impl[2] === 1'bx,
                         spec[3] === impl[3] | impl[3] === 1'bx });
  endfunction

  // G Modules -- Size 4 Tests
  wire [3:0] spec_g1wq1, spec_g1wq2;
  wire [3:0] impl_g1wq1, impl_g1wq2;
  g1 #(4)    g1wspec (spec_g1wq1, spec_g1wq2, d1, d2, en, clk);
  \g1$size=4 g1wimpl (impl_g1wq1, impl_g1wq2, d1, d2, en, clk);
  wire ok_g1wq1 = approximates_p(spec_g1wq1, impl_g1wq1);
  wire ok_g1wq2 = approximates_p(spec_g1wq2, impl_g1wq2);
  wire ok_g1w = ok_g1wq1 & ok_g1wq2;

  wire [3:0] spec_g2wq1, spec_g2wq2, spec_g2wq3;
  wire [3:0] impl_g2wq1, impl_g2wq2, impl_g2wq3;
  g2 #(4)    g2wspec (spec_g2wq1, spec_g2wq2, spec_g2wq3, d1, d2, en, clk);
  \g2$size=4 g2wimpl (impl_g2wq1, impl_g2wq2, impl_g2wq3, d1, d2, en, clk);
  wire ok_g2wq1 = approximates_p(spec_g2wq1, impl_g2wq1);
  wire ok_g2wq2 = approximates_p(spec_g2wq2, impl_g2wq2);
  wire ok_g2wq3 = approximates_p(spec_g2wq3, impl_g2wq3);
  wire ok_g2w = ok_g2wq1 & ok_g2wq2 & ok_g2wq3;

  wire [3:0] spec_g3wq1, spec_g3wq2;
  wire [3:0] impl_g3wq1, impl_g3wq2;
  g3 #(4)    g3wspec (spec_g3wq1, spec_g3wq2, d1, d2, en, clk);
  \g3$size=4 g3wimpl (impl_g3wq1, impl_g3wq2, d1, d2, en, clk);
  wire ok_g3wq1 = approximates_p(spec_g3wq1, impl_g3wq1);
  wire ok_g3wq2 = approximates_p(spec_g3wq2, impl_g3wq2);
  wire ok_g3w = ok_g3wq1 & ok_g3wq2;

  wire [3:0] spec_g4wq1, spec_g4wq2;
  wire [3:0] impl_g4wq1, impl_g4wq2;
  g4 #(4)    g4wspec (spec_g4wq1, spec_g4wq2, d1, d2, en, clk);
  \g4$size=4 g4wimpl (impl_g4wq1, impl_g4wq2, d1, d2, en, clk);
  // The ifs are irrelevant here, so we require exact matching
  wire ok_g4wq1 = (spec_g4wq1 === impl_g4wq1);
  wire ok_g4wq2 = (spec_g4wq2 === impl_g4wq2);
  wire ok_g4w = ok_g4wq1 & ok_g4wq2;

  wire [3:0] spec_g5wq1, spec_g5wq2;
  wire [3:0] impl_g5wq1, impl_g5wq2;
  g5 #(4)    g5wspec (spec_g5wq1, spec_g5wq2, d1, d2, en, clk);
  \g5$size=4 g5wimpl (impl_g5wq1, impl_g5wq2, d1, d2, en, clk);
  wire ok_g5wq1 = approximates_p(spec_g5wq1, impl_g5wq1);
  wire ok_g5wq2 = approximates_p(spec_g5wq2, impl_g5wq2);
  wire ok_g5w = ok_g5wq1 & ok_g5wq2;

  wire [3:0] spec_g6wq1, spec_g6wq2;
  wire [3:0] impl_g6wq1, impl_g6wq2;
  g6 #(4)    g6wspec (spec_g6wq1, spec_g6wq2, d1, d2, en, clk);
  \g6$size=4 g6wimpl (impl_g6wq1, impl_g6wq2, d1, d2, en, clk);
  wire ok_g6wq1 = approximates_p(spec_g6wq1, impl_g6wq1);
  wire ok_g6wq2 = approximates_p(spec_g6wq2, impl_g6wq2);
  wire ok_g6w = ok_g6wq1 & ok_g6wq2;

  wire okgw = &{ok_g1w, ok_g2w, ok_g3w, ok_g4w, ok_g5w, ok_g6w};
  wire allok = &{okf, okg, okfw, okgw};

`ifndef VL_SYSTEST_VCS
  // BOZO I seem to get various failures on VCS even when trying to check
  // less frequently, e.g., on clock edges. So just don't check anything on
  // VCS.

  always @(allok)
    begin
      if (allok !== 1'b1)
      begin
	$display("failure at time %d", $time);
	$display("Note: we've seen 'spurious' failures on Verilog-XL.");

	if (!ok_f1q1) $display("f1q1: spec %b, impl %b", spec_f1q1, impl_f1q1);
	if (!ok_f1q2) $display("f1q2: spec %b, impl %b", spec_f1q2, impl_f1q2);
	if (!ok_f2q1) $display("f2q1: spec %b, impl %b", spec_f2q1, impl_f2q1);
	if (!ok_f2q2) $display("f2q2: spec %b, impl %b", spec_f2q2, impl_f2q2);
	if (!ok_f3q1) $display("f3q1: spec %b, impl %b", spec_f3q1, impl_f3q1);
	if (!ok_f3q2) $display("f3q2: spec %b, impl %b", spec_f3q2, impl_f3q2);

	if (!ok_g1q1) $display("g1q1: spec %b, impl %b", spec_g1q1, impl_g1q1);
	if (!ok_g1q2) $display("g1q2: spec %b, impl %b", spec_g1q2, impl_g1q2);
	if (!ok_g2q1) $display("g2q1: spec %b, impl %b", spec_g2q1, impl_g2q1);
	if (!ok_g2q2) $display("g2q2: spec %b, impl %b", spec_g2q2, impl_g2q2);
	if (!ok_g2q3) $display("g2q2: spec %b, impl %b", spec_g2q3, impl_g2q3);
	if (!ok_g3q1) $display("g3q1: spec %b, impl %b", spec_g3q1, impl_g3q1);
	if (!ok_g3q2) $display("g3q2: spec %b, impl %b", spec_g3q2, impl_g3q2);
	if (!ok_g4q1) $display("g4q1: spec %b, impl %b", spec_g4q1, impl_g4q1);
	if (!ok_g4q2) $display("g4q2: spec %b, impl %b", spec_g4q2, impl_g4q2);
	if (!ok_g5q1) $display("g5q1: spec %b, impl %b", spec_g5q1, impl_g5q1);
	if (!ok_g5q2) $display("g5q2: spec %b, impl %b", spec_g5q2, impl_g5q2);
	if (!ok_g6q1) $display("g6q1: spec %b, impl %b", spec_g6q1, impl_g6q1);
	if (!ok_g6q2) $display("g6q2: spec %b, impl %b", spec_g6q2, impl_g6q2);

	if (!ok_f1wq1) $display("f1wq1: spec %b, impl %b", spec_f1wq1, impl_f1wq1);
	if (!ok_f1wq2) $display("f1wq2: spec %b, impl %b", spec_f1wq2, impl_f1wq2);
	if (!ok_f2wq1) $display("f2wq1: spec %b, impl %b", spec_f2wq1, impl_f2wq1);
	if (!ok_f2wq2) $display("f2wq2: spec %b, impl %b", spec_f2wq2, impl_f2wq2);
	if (!ok_f3wq1) $display("f3wq1: spec %b, impl %b", spec_f3wq1, impl_f3wq1);
	if (!ok_f3wq2) $display("f3wq2: spec %b, impl %b", spec_f3wq2, impl_f3wq2);

	if (!ok_g1wq1) $display("g1wq1: spec %b, impl %b", spec_g1wq1, impl_g1wq1);
	if (!ok_g1wq2) $display("g1wq2: spec %b, impl %b", spec_g1wq2, impl_g1wq2);
	if (!ok_g2wq1) $display("g2wq1: spec %b, impl %b", spec_g2wq1, impl_g2wq1);
	if (!ok_g2wq2) $display("g2wq2: spec %b, impl %b", spec_g2wq2, impl_g2wq2);
	if (!ok_g2wq3) $display("g2wq2: spec %b, impl %b", spec_g2wq3, impl_g2wq3);
	if (!ok_g3wq1) $display("g3wq1: spec %b, impl %b", spec_g3wq1, impl_g3wq1);
	if (!ok_g3wq2) $display("g3wq2: spec %b, impl %b", spec_g3wq2, impl_g3wq2);
	if (!ok_g4wq1) $display("g4wq1: spec %b, impl %b", spec_g4wq1, impl_g4wq1);
	if (!ok_g4wq2) $display("g4wq2: spec %b, impl %b", spec_g4wq2, impl_g4wq2);
	if (!ok_g5wq1) $display("g5wq1: spec %b, impl %b", spec_g5wq1, impl_g5wq1);
	if (!ok_g5wq2) $display("g5wq2: spec %b, impl %b", spec_g5wq2, impl_g5wq2);
	if (!ok_g6wq1) $display("g6wq1: spec %b, impl %b", spec_g6wq1, impl_g6wq1);
	if (!ok_g6wq2) $display("g6wq2: spec %b, impl %b", spec_g6wq2, impl_g6wq2);

      end
    end
`endif

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars();
    #100000;
    $finish;
  end

endmodule






