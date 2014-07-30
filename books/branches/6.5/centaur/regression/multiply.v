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


// multiply.v
//
// These are simple multipliers.

module multiply1 (
  output [0:0] out,
  input [0:0] abus,
  input [0:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply2 (
  output [1:0] out,
  input [1:0] abus,
  input [1:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply3 (
  output [2:0] out,
  input [2:0] abus,
  input [2:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply4 (
  output [3:0] out,
  input [3:0] abus,
  input [3:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply8 (
  output [7:0] out,
  input [7:0] abus,
  input [7:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply10 (
  output [9:0] out,
  input [9:0] abus,
  input [9:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply12 (
  output [11:0] out,
  input [11:0] abus,
  input [11:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply16 (
  output [15:0] out,
  input [15:0] abus,
  input [15:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply32 (
  output [31:0] out,
  input [31:0] abus,
  input [31:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply64 (
  output [63:0] out,
  input [63:0] abus,
  input [63:0] bbus
);
assign out = abus * bbus;
endmodule

/*
 module multiply128 (
  output [127:0] out,
  input [127:0] abus,
  input [127:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply256 (
  output [255:0] out,
  input [255:0] abus,
  input [255:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply512 (
  output [511:0] out,
  input [511:0] abus,
  input [511:0] bbus
);
assign out = abus * bbus;
endmodule

module multiply1024 (
  output [1023:0] out,
  input [1023:0] abus,
  input [1023:0] bbus
);
assign out = abus * bbus;
endmodule

*/
