/*

VL Regression Suite
Copyright (C) David L. Rager

License: (An MIT/X11-style license)

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the "Software"),
to deal in the Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute, sublicense,
and/or sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.

Original author: David Rager <ragerdl@defthm.com>

Other entities should feel free to add to the "VL Regression Suite"
with files that have different licenses and/or copyrights.

 */

module compose (qq, d, clk);
  output qq;
  input d;
  input clk;

  reg 	q;
  reg qq;

  always @(posedge clk)
    q <= ~d;

  always @(posedge clk)
    qq <= ~q;

endmodule


module compose_three (qqq, d, clk);
  output qqq;
  input d;
  input clk;

  reg 	q;
  reg qq;
  reg qqq;

  always @(posedge clk)
    q <= ~d;

  always @(posedge clk)
    qq <= ~q;

  always @(posedge clk)
    qqq <= ~qq;

endmodule


module compose_four (qqqq, d, clk);
  output qqqq;
  input d;
  input clk;

  reg q;
  reg qq;
  reg qqq;
  reg qqqq;

  always @(posedge clk)
    q <= ~d;

  always @(posedge clk)
    qq <= ~q;

  always @(posedge clk)
    qqq <= ~qq;

   always @(posedge clk)
    qqqq <= ~qqq;

endmodule
