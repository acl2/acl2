/*

VL Regression Suite
Copyright (C) David L. Rager

Note: The license below is based on the template at:
http://opensource.org/licenses/BSD-3-Clause

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

o Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

o Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

o Neither the name of the University of Texas, Austin nor the names of
  its contributors may be used to endorse or promote products derived
  from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

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
