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
parameter top_normal = top_unset + 1;
parameter top_unused = top_normal + 1;

module m0 () ;

  wire [3:0] w1_spurious;
  wire [3:0] w1_unset;
  wire [3:0] w1_normal = top_normal;
  wire [3:0] w1_unused;
  assign w1_unused = w1_normal + w1_unset;

endmodule


typedef integer top_unused_t;
typedef integer top_used_t;

module m2 (output top_used_t o) ;

  assign o = 5;

endmodule


function top_f_used (input logic [3:0] a);
  logic [3:0] b = a;
  top_f_used = b;
endfunction

function top_f_unused (input logic [3:0] a);
  logic [3:0] b = a;
  top_f_unused = b;
endfunction

package p ;
  logic [3:0] PA;
endpackage


module m1 () ;

  import p::*;

  wire [3:0] w1_spurious;
  wire [3:0] w1_unset;
  wire [3:0] w1_normal = top_f_used(PA) + top_normal;
  wire [3:0] w1_unused;
  assign w1_unused = w1_normal + w1_unset;

  reg [3:0] r1_spurious;
  reg [3:0] r1_unset;
  reg [3:0] r1_unused;
  reg [3:0] r1_normal;
  initial begin
    r1_normal = 3;
    r1_unused = r1_normal + r1_unset;
  end

  reg [3:0] r2_spurious;
  reg [3:0] r2_unset;
  reg [3:0] r2_unused;
  reg [3:0] r2_normal;
  always_comb
  begin
    r2_normal = 3;
    r2_unused = r2_normal + r2_unset;
  end

  function m1_f1 (input logic a) ;
    logic [3:0] b;
    begin : foo
      logic [3:0] c;
      c = a;
      b = c;
    end
    m1_f1 = b;
  endfunction


endmodule




module m3 (output logic [3:0] perfectly_ok) ;

  logic [3:0] part_used;
  logic [3:0] part_set;

  assign part_used = 0;
  assign part_set[2:0] = part_used[1];
  assign perfectly_ok = part_set;

endmodule
