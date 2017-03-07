// ALU with a Doomsday Counter
// Copyright (C) 2014, Oracle and/or its affiliates. All rights reserved.
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
// Original authors: Andrew Brock <andrew.brock@oracle.com>
//                   David L. Rager <david.rager@oracle.com>

`define CYCLES 65

module doomsday(
  input wire clk, rst,
  input wire [3:0] a, b,
  output wire [3:0] ans);

  reg [3:0] count;
  wire [3:0] count_in;

  wire op;
  assign op = count[3];
  assign count_in = count + 1'b1;

  always @(posedge clk)
    if(rst)
      count <= 4'b0000;
    else
      count <= count_in;

  assign ans = op ? a-b : a+b;

endmodule //doomsday

module driver;
  reg clk, rst;
  wire [3:0] ans;
  reg [3:0] a, b, sum;
  initial clk = 0;
  always #1 clk = ~clk;

  doomsday the_counter(.clk(clk), .rst(rst), .a(a), .b(b), .ans(ans));

  always @(posedge clk) begin
    a <= $random();
    b <= $random();
    sum <= a+b;
  end

  initial begin
    $monitor($stime,,"%h %h %h %h", a, b, sum, ans);
    rst <= 1'b1;
    @(posedge clk)
    rst <= 1'b0;
    repeat(`CYCLES) @(posedge clk);
    $finish;
  end
endmodule // driver
