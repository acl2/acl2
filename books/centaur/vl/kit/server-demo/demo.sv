// VL Verilog Toolkit
// Copyright (C) 2008-2016 Centaur Technology
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


// Demo for the VL Server

parameter BUS_WIDTH = 4;
parameter ADDR_WIDTH = 8;


function logic [3:0] id4 (input [3:0] a);
  id4 = a;
endfunction

function logic [15:0] encode4 (input [3:0] a);
  encode4 = { a == 15, a == 14, a == 13, a == 12,
              a == 11, a == 10, a == 9, a == 8,
              a == 7, a == 6, a == 5, a == 4,
              a == 3, a == 2, a == 1, a == 0 };
endfunction

function logic [3:0] decode4 (logic [15:0] enc);
  integer i;
  for(i = 15; i > 0; i--) begin
    if (enc[i])
       return i;
  end
  return 'x;
endfunction

package BusPkg;

  typedef logic [3:0] opcode_t;
  typedef logic [6:0] port_t;
  typedef logic [5:0] flags_t;

  function port_t portIdentity (input port_t a);
    portIdentity = a;
  endfunction

endpackage


package PlanePkg;

  typedef logic [3:0] wing_t;
  typedef logic [6:0] cockpit_t;
  typedef logic [5:0] engine_t;
  typedef logic [5:0] wheel_t;

  parameter numPilots = 2;
  parameter numPassengers = 372;

endpackage


interface IBus ;

  import BusPkg::*;

  logic valid;
  opcode_t opcode;
  port_t port;
  flags_t flags;

  modport consumer (input valid, opcode, port, flags);
  modport producer (output valid, opcode, port, flags);

endinterface


interface IPlane ;

  import PlanePkg::*;

  wing_t leftWing;
  wing_t rightWing;

  engine_t mainEngine;
  engine_t backupEngine;

  wheel_t frontWheel;
  wheel_t backWheel;
  wheel_t bottomWheel;
  wheel_t topWheel;     // Might not be a good idea

endinterface


typedef struct {
  string       name;
  int 	       age;
  int 	       weight;
  int 	       height;
} student_t;


module EventGen (IBus bus, input [3:0] mode, input clk);

  wire [$bits(mode)-1:0] modebar;

  for(genvar i = 0; i < $bits(mode); ++i)
  begin : makeModeBar
    not(modebar[i], mode[i]);
  end

  wire anyMode = |mode;
  wire noMode = &modebar;

  reg [3:0] prevMode;
  always @(posedge clk) prevMode = mode;

endmodule


module top () ;

  IBus theBus();

  reg clk;
  always #100 clk = ~clk;

  wire [3:0] mode;
  assign mode = (3 + 4) * theBus.opcode[2:0] << theBus.flags[0];

  EventGen generator (theBus, mode, clk);

endmodule


