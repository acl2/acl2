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


// basic tests of functions

module fns (o1, o2, o3, o4, o5, o6, a) ;

parameter size = 1;

input [3:0] a;

wire use_size = size;


// test the most basic function

function identity1 ;
  input in;
  identity1 = in;
endfunction

output [3:0] o1;
assign o1[0] = identity1(a[0]);
assign o1[1] = identity1(a[0]);
assign o1[2] = identity1(identity1(a[1]));
assign o1[3] = identity1(a[2]);


// test a function with a range

function [1:0] identity2 ;
  input [1:0] in;
  begin
    identity2 = in;
  end
endfunction

output [3:0] o2;
assign o2[1:0] = identity2(a[1:0]);
assign o2[3:2] = identity2(a[1:0]);


// test a function that reads from a wire other than its input

function closure1 ;
  input in;
  closure1 = in & a[3];
endfunction

output [3:0] o3;
assign o3[0] = closure1(a[0]);
assign o3[1] = closure1(a[1]);
assign o3[2] = closure1(a[2]);
assign o3[3] = closure1(a[3]);


// test a function that has a register

function sillybuf ;
  input in;
  reg r;
  begin
    r = ~in;
    sillybuf = ~r;
  end
endfunction

output [3:0] o4;
assign o4[0] = sillybuf(a[0]);
assign o4[1] = sillybuf(a[1]);
assign o4[2] = sillybuf(a[2]);
assign o4[3] = sillybuf(a[3]);


// test a function that calls one function defined above, and another function
// defined below.

function updown ;
  input in;
  reg r1;
  reg r2;
  begin
    r1 = sillybuf(in);
    r2 = sillyinv(r1);
    updown = sillyinv(r2);
  end
endfunction

function sillyinv ;
  input in;
  reg r1;              // test out a function with some unused registers
  reg r2;
  reg r3;
  begin
    r2 = ~in;
    r3 = ~in;
    sillyinv = r2;
  end
endfunction

output [3:0] o5;
assign o5[0] = updown(a[0]);
assign o5[1] = updown(a[1]);
assign o5[2] = updown(a[2]);
assign o5[3] = updown(a[3]);


// test of a function that isn't even used

function unused ;
  input in;
  unused = in;
endfunction





// test a function with parameters, and which ignores its input, and which
// shadows some of the variables in the module, and references a module wire
// that isn't its input, and calls multiple functions, and has an unused
// parameter, and has an unused reg, and a local param, and puts its decls
// in a strange order

function [1:0] param ;
  input in;
  parameter p = 1;
  reg unused_reg;
  localparam q = 0;
  reg o2;
  reg o1;
  begin
    o1 = p & a[2];
    o2 = q;
    param = {sillybuf(o1), sillybuf(sillyinv(sillyinv(o2)))};
  end
endfunction

output [3:0] o6;
assign o6[1:0] = param(a[3:2]);
assign o6[3:2] = param(param(a[1:0]));

// test a function with names that shadow the outer module's names

// test a function with the alternate syntax

// test functions with size mismatches between their arguments and inputs

// test a signed function



endmodule


/*+VL

module make_tests();

  wire [3:0] o1, o2, o3, o4, o5, o6;
  wire [3:0] a;

  fns my_inst (o1, o2, o3, o4, o5, o6, a);

endmodule

*/
