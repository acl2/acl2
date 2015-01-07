// VL Verilog Toolkit
// Copyright (C) 2008-2014 Centaur Technology
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

parameter top_spurious;
parameter top_unset;
parameter top_normal = 3;
parameter top_unused = 4;

module m0 () ;

  wire [3:0] w1_spurious;
  wire [3:0] w1_unset;
  wire [3:0] w1_normal = top_normal;
  wire [3:0] w1_unused;
  assign w1_unused = w1_normal + w1_unset + top_unset;

endmodule


typedef integer top_unused_t;
typedef integer top_used_t;

function top_f_used (input logic [3:0] a);
  logic [3:0] b = a;
  top_f_used = b;
endfunction

function top_f_unused (input logic [3:0] a);
  logic [3:0] b = a;
  top_f_unused = b;
endfunction


module m1 (output top_used_t myout) ;

  assign myout = top_f_used(4'b1101);

endmodule


module m2 () ;

  logic [3:0] l1_spurious;
  logic [3:0] l1_unset;
  logic [3:0] l1_normal = 4'b0;
  logic [3:0] l1_unused;
  initial
  begin
    l1_unused = l1_unset + l1_normal;
  end

endmodule

module m3 () ;

  parameter delay = 5;

  wire clk;

  reg [3:0] r1_spurious;
  reg [3:0] r1_unset;
  reg [3:0] r1_normal = top_normal;
  reg [3:0] r1_unused;

  always @(posedge clk)
    r1_unused <= #(delay) r1_unset + r1_normal;

endmodule


typedef logic [3:0] opcode_t;
typedef struct {
  opcode_t opcode;
  logic [3:0]  arg1;
  logic [3:0]  arg2;
} instruction_t;



package pkg1 ;

  // See module m4 for where these get used.

  logic [3:0]  p1_spurious;
  logic [3:0]  p1_unused;
  logic [3:0]  p1_unset;
  logic [3:0]  p1_normal;

  function pfn_used (input a) ;
    reg pr1_unset;
    reg pr1_normal;
    begin
      begin : foo
	reg pr1_unused = pr1_unset;
      end
    end
    pr1_normal = a;
    pfn_used = pr1_normal;
  endfunction

  function pfn_unused (input a) ;
    reg pr2_unset;
    reg pr2_normal;
    begin
      begin : foo
	reg pr2_unused = pr2_unset;
      end
    end
    pr2_normal = a;
    if (pr2_normal)
       pfn_unused = 1;
    else
       pfn_unused = 0;
  endfunction

endpackage


module m4 () ;

  import pkg1::*;

  logic [3:0] u1 = 1;
  logic [3:0] u2;

  assign p1_unused = 2;


  always @(p1_unset)
     u2 = p1_normal;

  initial begin
    p1_normal = u2 + pfn_used(u1);
  end

endmodule

function noreturn (input a);
  reg nr_unused;
  nr_unused = a;
  // doesn't assign to noreturn
endfunction


// BOZO some bit-level tests
