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

// see flopcode/compare.v

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


module testcore (check,
		 clk, reset, resetb, set,
		 en1, en2, d1, d2, d3);

  // whether or not to check failures (past "initial reset" phase)
  input check;

  // clocks signals, should not change when data changes
  input clk;
  input reset, resetb;
  input set;

  // data signals
  input en1, en2;
  input [3:0] d1, d2, d3;

  // This core testing module can be instantiated with different
  // kinds timings for its clocks and data signals.

  // One-bit random data elements for one-bit tests
  wire c1 = d1[0];
  wire c2 = d2[0];
  wire c3 = d3[0];

  wire sf1, if1;
  f1 #(1)    f1_spec (sf1, c1, clk, reset);
  \f1$size=1 f1_impl (if1, c1, clk, reset);
  wire okf1 = sf1 === if1;

  wire sf2, if2;
  f2 #(1)    f2_spec (sf2, c1, clk, set);
  \f2$size=1 f2_impl (if2, c1, clk, set);
  wire okf2 = sf2 === if2;

  wire if3, sf3;
  f3 #(1)    f3_spec (sf3, c1, clk, resetb);
  \f3$size=1 f3_impl (if3, c1, clk, resetb);
  wire okf3 = sf3 === if3;

  wire if4, sf4;
  f4 #(1)    f4_spec (sf4, c1, clk, resetb);
  \f4$size=1 f4_impl (if4, c1, clk, resetb);
  wire okf4 = sf4 === if4;

  wire if5, sf5;
  f5 #(1)    f5_spec (sf5, c1, clk, reset);
  \f5$size=1 f5_impl (if5, c1, clk, reset);
  wire okf5 = sf5 === if5;

  wire if6, sf6;
  f6 #(1)    f6_spec (sf6, c1, clk, resetb);
  \f6$size=1 f6_impl (if6, c1, clk, resetb);
  wire okf6 = sf6 === if6;

  wire ok = &{okf1, okf2, okf3, okf4, okf5, okf6};

  // Simple checking strategy:
  always #1
    begin
    $display("Checking at time %d: check = %b, ok = %b", $time, check, ok);
    if (check && ok !== 1'b1)
      begin
  	$display("failure at time %d", $time);
      end
    end

endmodule


module test () ;

  // I think there is a race if we allow clk and reset to transition
  // simultaneously.  In particular, if reset falls while clock rises,
  // what happens?  It seems like there is a race:
  //
  //   - If CLK rises first, then RESET is still high when the
  //     always block is evaluated.  Q gets 0.
  //
  //   - If RESET falls first, then it is low when the rising CLK
  //     edge causes the always block to evaluate.  Q gets D.


  // Timing setup 1:
  //  - Data signals change every 20 ticks.
  //  - Preliminary clocks change every 10 ticks.
  //
  // This ensures that data/prelim clocks are changing in lockstep.
  // We delay the true clocks by 5 ticks, so we get:
  //
  //            _______________________________________
  //  data      __X______________X_____________X_______
  //
  //            _______________________________________
  //  pre clks  __X______________X_____________X_______
  //
  //            _______________________________________
  //  true clks _______X_________________X_____________
  //
  // This ensures that data and true clocks are never changing at the
  // same time, to rule out data/clk races.
  //
  // BOZO what about clock/clock races?

  // We probably had better have that clocks and sets/resets are booleans.
  wire 	     clk_pre, reset_pre, set_pre;
  randomBit2 #(10)   mk_clk   (clk_pre);
  randomBit2 #(10)   mk_reset (reset_pre);
  randomBit2 #(10)   mk_set   (set_pre);

  // We'll try to leave all of the data signals as purly four-valued.
  wire [3:0] d1, d2, d3;
  wire 	     en1, en2;
  randomBit4 #(20)   mk_en1   (en1);
  randomBit4 #(20)   mk_en2   (en2);
  randomVec4 #(4,20) mk_d1    (d1);
  randomVec4 #(4,20) mk_d2    (d2);
  randomVec4 #(4,20) mk_d3    (d3);

  // Clock/reset change 5 ticks after data.
  wire #5 clk = clk_pre;
  wire #5 reset = reset_pre;
  wire #5 set = set_pre;
  wire resetb = ~reset;

  reg  check;

  testcore test1 (check,
		  clk, reset, resetb, set,
		  en1, en2, d1, d2, d3);

  initial begin
    $dumpfile("compare.vcd");
    $dumpvars();
    check = 0;
    #30;
    check = 1;
    #10000;
    $finish;
  end

endmodule
