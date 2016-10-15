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
//
// This demo is mostly intended to let us have a small model that we can use
// for debugging pretty-printing, linking, etc.

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

typedef enum logic [3:0] {
   IDLE,
   LIGHT_SPEED,
   LUDICROUS_SPEED[1:0],
   PLAID
} speed_t;


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


interface IPlane (input clk, input clk2);

  import PlanePkg::*;

  wing_t leftWing;
  wing_t rightWing;

  engine_t mainEngine;
  engine_t backupEngine;

  wheel_t frontWheel;
  wheel_t backWheel;
  wheel_t bottomWheel;
  wheel_t topWheel;     // Might not be a good idea

  parameter gasTanks = 17;

  for(genvar i = 0; i < gasTanks; ++i)
  begin : gasline
    logic enable;
    logic lineClk = clk & enable;
    typedef enum logic { REGULAR = 0, UNLEADED = 1} gastype_t;

  end

endinterface


typedef struct {
  string       name;
  int 	       age;
  int 	       weight;
  int 	       height;
} student_t;


module EventGen (IBus bus, input [3:0] mode, input clk, input student_t hi);

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


module onehotMux4(output [7:0] o,
                  input sel1, sel2, sel3, sel4,
                  input [7:0] data1, data2, data3, data4);

  // This assignment is hard to pretty-print with indentation because some
  // lines use spaces and some use tabs.  But we should at least see the
  // correct line breaking to easily identify that basic mux here.

  assign o = {8{sel1}} & data1
           | {8{sel2}} & data2
	   | {8{sel3}} & data3
           | {8{sel4}} & data4;

  wire [7:0] other_style;

  assign other_style = {8{sel1}} & data1 |
		       {8{sel2}} & data2 |
		       {8{sel3}} & data3 |
		       {8{sel4}} & data4;

  wire another_style;

  wire [7:0] sel1w = {8{sel1}};
  wire [7:0] sel2w = {8{sel2}};
  wire [7:0] sel3w = {8{sel3}};
  wire [7:0] sel4w = {8{sel4}};

  assign another_style = sel1w & data1 |
			 sel2w & data2 |
			 sel3w & data3 |
			 sel4w & data4;

endmodule



// This mux is really just a test of some ?: operator indenting.
module qmarkMux4(
  output [7:0] o,
  input [2:0] sel,
  input [7:0] data0, data1, data2, data3
);

  assign o = (sel == 0) ? data0
           : (sel == 1) ? data1
           : (sel == 2) ? data2
           :              data3;

  // some other tests of ?: operator indenting preservation

  wire other_style;
  assign other_style = (sel == 0) ? data0 :
                       (sel == 1) ? data1 :
                       (sel == 2) ? data2 :
                                    data3 ;

  wire other_style2;
  assign other_style2 = (sel == 0) ? data0
                      :
                        (sel == 1) ? data1
                      :
                        (sel == 2) ? data2
                      :
                         data3 ;



  wire awful_style;
  assign awful_style = (sel == 0)
                          ? data0

                          : (sel == 1)
                               ? data1

                               : (sel == 2)
                                   ? data2 :

                                     data3 ;

  wire awful_style2 = (sel == 0)

                          ? data0

                          : (sel == 1)

                               ? data1

                               : (sel == 2)

                                   ? data2 :

                                     data3 ;


endmodule


module top () ;

  IBus theBus();

  reg clk;
  always #100 clk = ~clk;
  wire clk2 = clk;

  IPlane EnolaGay (clk, clk2);
  IPlane TheCanary(.clk, .*);
  IPlane AirforceOne(.*);

  wire [BUS_WIDTH-1:0] foo;

  wire [3:0] mode;
  assign mode = (3 + 4) * theBus.opcode[2:0] << theBus.flags[0];

  EventGen generator (.bus(theBus),
                      .mode(mode),
                      .clk);

  typedef struct packed {
    logic [3:0]  inco;
    logic [ADDR_WIDTH-1:0]  herent;
  } importantType_t;

  importantType_t realWiresHaveHorribleNamesLikeThisA,
                  realWiresHaveHorribleNamesLikeThisB,
                  realWiresHaveHorribleNamesLikeThisC,
                  realWiresHaveHorribleNamesLikeThisD,
                  realWiresHaveHorribleNamesLikeThisE,
		  realWiresHaveHorribleNamesLikeThisF,
		  realWiresHaveHorribleNamesLikeThisG,
		  realWiresHaveHorribleNamesLikeThisH,
		  realWiresHaveHorribleNamesLikeThisI,
		  realWiresHaveHorribleNamesLikeThisJ,
		  realWiresHaveHorribleNamesLikeThisK,
		  realWiresHaveHorribleNamesLikeThisL,
		  realWiresHaveHorribleNamesLikeThisM,
		  realWiresHaveHorribleNamesLikeThisN,
		  realWiresHaveHorribleNamesLikeThisO,
		  realWiresHaveHorribleNamesLikeThisP,
                  realWiresHaveHorribleNamesLikeThisQ;

  lottaports soManyUglyPorts(
                  realWiresHaveHorribleNamesLikeThisA,
                  realWiresHaveHorribleNamesLikeThisB,
                  realWiresHaveHorribleNamesLikeThisC,
                  realWiresHaveHorribleNamesLikeThisD,
                  realWiresHaveHorribleNamesLikeThisE,
		  realWiresHaveHorribleNamesLikeThisF,
		  realWiresHaveHorribleNamesLikeThisG,
		  realWiresHaveHorribleNamesLikeThisH,
		  realWiresHaveHorribleNamesLikeThisI,
		  realWiresHaveHorribleNamesLikeThisJ,
		  realWiresHaveHorribleNamesLikeThisK,
		  realWiresHaveHorribleNamesLikeThisL,
		  realWiresHaveHorribleNamesLikeThisM,
		  realWiresHaveHorribleNamesLikeThisN,
		  realWiresHaveHorribleNamesLikeThisO,
		  realWiresHaveHorribleNamesLikeThisP,
                  realWiresHaveHorribleNamesLikeThisQ
             );

  lottaports soManyMoreUglyPorts(.*);

endmodule



module lottaports (input [7:0] a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p,
                   output logic [7:0] q);

  // Wow, this has a lot of ports.

endmodule



module safetyValve;

  initial $finish();

endmodule
