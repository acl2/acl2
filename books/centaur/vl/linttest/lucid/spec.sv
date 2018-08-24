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

/*+VL `define HAVE_VL */

// We no longer expect to support top-level unset parameters

// `ifdef HAVE_VL
// parameter top_spurious;
// parameter top_unset;
// `else
// // NCVerilog/VCS don't like parameters without initial values
// parameter top_spurious = 1;
// parameter top_unset = 1;
// `endif

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

function top_f_dpiexported (input logic [3:0] a);
  logic [3:0] b;
  b = a;
  top_f_dpiexported = b;
endfunction

export "DPI" function top_f_dpiexported;

import "DPI" function logic top_f_dpiimported_unused (logic [3:0] a);
import "DPI" function logic top_f_dpiimported_normal (logic [3:0] a);


module m1 (output top_used_t myout) ;

  assign myout = top_f_used(4'b1101);
  wire temp = top_f_dpiimported_normal(myout);

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

//@VL LINT_IGNORE_LUCID_UNSET
function noreturn2 (input a);
  reg nr_unused;
  nr_unused = a;
  // doesn't assign to noreturn
endfunction



module m5 () ;

  parameter width = 4;

  wire [3:0] m5_unused, m5_unset;
  m6 #(width) my_m6 (m5_unused, m5_unset);

  assign m5_unset[2:0] = 0;  // leaves bit 1 unset

  // some bits unset, some bits unused
  wire [3:0] doublebad;
  assign doublebad[2:0] = 0;
  assign m5_unused[2:0] = doublebad[2:0];

endmodule


module m6
  #(parameter width = 1)
  (output [width-1:0] xout, input [width-1:0] xin);
  assign xout = xin;

  // This has some unset bits when width is less than 5.
  wire [5:0] foo;
  assign foo[width-1:0] = 0;

endmodule


module m7 () ;

// just check some complex lhs expressions

  wire unset1, unset2, unset3;
  wire unused1, unused2, unused3;

  assign {unused1, {{{{{{unused2, unused3}}}}}}} = {{unset1, unset2}, unset3};

endmodule


typedef struct packed {
  logic [3:0]  token;
  logic        fuzzy;
  logic [63:0] payload;
  logic [2:0]  checksum;
} transaction_t;

module m8sub (output transaction_t outtrans, input transaction_t intrans) ;
  assign outtrans.token[1] = intrans.token[0];
endmodule


module m8 () ;

  transaction_t normal_trans;
  transaction_t unset_trans;
  transaction_t unused_trans;
  transaction_t spurious_trans;

  assign normal_trans.token = 0;

  wire [63:0] xx0 = normal_trans.payload;
  wire [63:0] xx1 = unset_trans.payload;

  assign unused_trans.payload = 0;

  transaction_t subout, subin;
  m8sub mysub (subout, subin);

endmodule


interface MemReq ;
  logic [63:0] w1_spurious;
  logic        w1_normal;
  logic [7:0]  w1_unused;
  logic [3:0]  w1_unset;

  logic [3:0]  w1_partial_unused;
  logic [63:0] w1_partial_unset;
endinterface

module m9write (MemReq foo) ;
  assign foo.w1_normal = 0;
  assign foo.w1_unused = 0;
  assign foo.w1_partial_unused = 0;
  assign foo.w1_partial_unset[5:0] = 0;
endmodule

module m9writewrap(MemReq foo) ;
  m9write writecore (foo);
endmodule

module m9read (MemReq foo) ;
  logic blah = { foo.w1_normal,
                 foo.w1_unset,
                 foo.w1_partial_unused[2:0],
                 foo.w1_partial_unset };
endmodule

module m9readwrap(MemReq foo);
  m9read readcore (foo);
endmodule

module m9 () ;

  MemReq mr_spurious();
  MemReq mr_used1();
  MemReq mr_used2();

  m9writewrap write (mr_used1);
  m9readwrap read (mr_used2);

endmodule



module mh1 () ;

  // These will get set hierarchically in mh2.
  wire w1_spurious;
  wire w1_normal;
  wire w1_unused;
  wire w1_unset;

endmodule

module mh2 () ;

  mh1 inst1 ();
  mh1 inst2 ();

  assign inst1.w1_normal = inst2.w1_unset;
  assign inst2.w1_normal = inst1.w1_unset;

  assign inst1.w1_unused = inst2.w1_normal;
  assign inst2.w1_unused = inst1.w1_normal;

endmodule


module idx1 ();

  parameter [3:0] a1 = 0;
  parameter [3:0] a2 = 0;

  wire [3:0] normal1 = 0;
  wire [3:0] normal2 = 0;
  wire [3:0] normal3 = 0;

  wire unused1;
  logic [3:0] unused2;
  logic [3:0] unused3;

  assign  unused1 = normal1[normal2];
  initial unused2[normal3] = 0;

  assign unused3 = normal1[a1:a2];

endmodule

module idxtop () ;

  // So it won't get thrown away
  idx1 #(.a1(4), .a2(4)) idxinst ();

endmodule


interface dsInterface;
  logic [3:0] dsi_normal;
  logic [3:0] dsi_spurious;
  logic [3:0] dsi_unset;
  logic [3:0] dsi_unused;
endinterface

module dotstar (output logic [3:0] out1,
                output logic [3:0] out2,
		input logic [3:0]  in1,
		input logic [3:0]  in2,
                dsInterface dsi) ;

  assign out1 = dsi.dsi_normal;
  assign out2 = dsi.dsi_unset;
  assign dsi.dsi_unused = in1;
  assign dsi.dsi_normal = in2;

endmodule

module dotstarwrap () ;

  logic [3:0] out1, out2, in1, in2;
  dsInterface dsi ();

  dotstar inst (.*);

endmodule


module mg1 () ;

  localparam p1_used = 4;

  wire [3:0] w1_normal;

  // Tricky case: this usage of p1 got missed by our original, naive generate
  // handling.
  if (p1_used >= 4) assign w1_normal = 1;
  else              assign w1_normal = 0;

endmodule


module mg2 () ;

  wire [3:0] xx, yy;

  genvar     genvar1;
  genvar     genvar2;

  generate
    for(genvar1 = 0; genvar1 < 4; genvar1 = genvar1+1)
    begin
      not(xx[genvar1], yy[genvar1]);
    end
  endgenerate

endmodule




interface ImPort ;

  logic      reqVld;
  logic [3:0] reqMain;
  logic       dataVld;
  logic [63:0] dataMain;
  logic        dataSpurious;

  modport server (input reqVld, reqMain, output dataVld, dataMain);
  modport client (output reqVld, reqMain, input dataVld, dataMain);

endinterface

module imserve (
 input logic  foo,
 output logic bar,
 ImPort.server port1, port2
);

  assign port1.dataVld = port1.reqVld;
  assign port1.dataMain = 0;

  assign port2.dataVld = port2.reqVld;
  assign port2.dataMain = 0;

  wire w1_normal;
  wire w1_spurious;
  wire w1_unset;
  wire w1_unused;

  assign w1_normal = w1_unset;
  assign w1_unused = w1_normal;
  assign bar = foo;

endmodule

module imservewrap (
 input logic  foo,
 output logic bar,
 ImPort.server port1, port2
);

  imserve server1 (.*);

endmodule

module imsim ();

  ImPort port1 ();
  ImPort port2 ();

  logic foo, bar;
  imservewrap server1 (.*);

endmodule


primitive awfulbuf (o, i) ;

  output o;
  input  i;

  table
    0 : 0 ;
    1 : 1 ;
  endtable

endprimitive


module useprim ;

  wire w1_spurious;
  wire w1_unused;
  wire w1_unset;

  awfulbuf (w1_unused, w1_unset);

endmodule



module trickyscope;

  // This once caused a scopestack/shadowcheck mismatch

  integer loopvar1;
  always_comb
  begin
    for (loopvar1=0; loopvar1 < 4 ; loopvar1=loopvar1+1)
    begin
      $display("Hello %d", loopvar1);
    end
  end

  logic [16-1:0] counter_unused;
  assign counter_unused = 0;

  integer loopvar2;

  always_comb
  for(int loopvar3 = 0; loopvar2 < 4; loopvar3=10)
  begin
    $display("Didnt use loopvar3.");
  end

  integer loopvar4;
  always_comb
  begin
    for (int loopvar4=0; loopvar4 < 4 ; loopvar4=loopvar4+1)
    begin
      $display("Hello %d", loopvar4);
    end
  end

endmodule


module minuscolon ;

  wire [10:0] normal1;
  wire [10:0] normal2;

  assign normal1[3 -: 4] = normal2[3 -: 4];
  assign normal1[7 -: 4] = normal2[7 -: 4];
  assign normal1[9:8] = normal2[9:8];
  assign normal1[10] = normal2[10];

endmodule


typedef struct {
  opcode_t opcode;
  logic [3:0]  arg1;
  logic [3:0]  arg2;
} instruction2_t;

module pattern;

  instruction2_t myinst;

  initial begin
    myinst = instruction2_t'{
              opcode: 0,
              arg1: 1,
              arg2: 2
             };
  end

endmodule



module tricky_init ;

  wire w1_normal;
  wire w2_normal;
  wire w3_unused;
  wire w4_unset;
  wire w5_spurious;

  initial begin
    w1_normal = w4_unset;
  end

  initial begin
    w2_normal = w4_unset;
  end

  final begin
    w3_unused = w2_normal;
  end

  final begin
    w3_unused = w1_normal;
  end

endmodule


interface fancy_mp;

  logic [3:0] foo;

  modport mp1 (input foo);
  modport mp2 (input foo);
  modport mp3 (input foo);
  modport mp4 (input foo);

endinterface

module fancy_mptest_sub (fancy_mp xx);

endmodule

module fancy_mptest_sub2 (fancy_mp.mp3 xx);

endmodule

module fancy_mptest ;

  fancy_mp xx();

  fancy_mptest_sub sub1 (xx.mp1);
  fancy_mptest_sub sub2 (.xx(xx.mp2));

endmodule



interface fancy_mp_param;

  // parameterized interfaces make modport handling trickier

  parameter width = 3;
  logic [width-1:0] foo;

  modport mp1 (input foo);
  modport mp2 (input foo);
  modport mp3 (input foo);
  modport mp4 (input foo);

endinterface

module fancy_mp_paramtest_sub (fancy_mp_param xx);

endmodule

module fancy_mp_paramtest_sub2 (fancy_mp_param.mp3 xx);

endmodule

module fancy_mp_paramtest ;

  fancy_mp_param #(5) xx();

  fancy_mp_paramtest_sub sub1 (xx.mp1);
  fancy_mp_paramtest_sub sub2 (.xx(xx.mp2));
  fancy_mp_paramtest_sub2 sub3 (.*);

endmodule



// This next test is based on a real example that was acting crazy.

package fcasttest_package;

  function yes_usedfun1 (input logic [3:0] a);
    logic [3:0] b = a;
    return b;
  endfunction

  function yes_usedfun2 (input logic [3:0] a);
    logic [3:0] b = a;
    return b;
  endfunction

  function not_usedfun (input logic [3:0] a);
    logic [3:0] b = a;
    return b;
  endfunction

endpackage

module fcasttest ;

  import fcasttest_package::*;

  logic [3:0] xx;

  typedef logic [3:0] foo_t;

  parameter size = 4;
  for(genvar i = 0; i < size; ++i) begin
    logic [3:0] blah1 = yes_usedfun1(xx);
    logic [3:0] blah2 = foo_t'(yes_usedfun2(xx));
  end


endmodule



module gen3 ;

  begin : myblock
    wire [3:0] aa;
  end

  wire [3:0] bb = aa;  // oops, should be myblock.aa

endmodule




module cosim_gen7 ( input logic [127:0] in, output wire [127:0] out);

  parameter version = 1;
  parameter mode = 1;

  logic aa1_unset;
  logic aa1_unused;
  logic aa1_spurious;

  // Very tricky: the nested conditional generate does NOT introduce an extra
  // scope.  Thus it is legal to refer to foo.a directly, even though you might
  // think it should be something like genblock_0.foo.a or whatever the stupid
  // name generation scheme is.

  if (version == 1)
    if (mode == 1) begin : foo
      wire [3:0] bb1_unset;
      wire [3:0] bb1_unused = aa1_unset;
      wire [3:0] bb1_spurious;
    end
    else
       wire cc1_unused = in;

  assign aa1_unused = foo.bb1_unset;

endmodule



module typotest ;

   wire [3:0] eventsFromNearby;
   wire [3:0] eventsFromAfar;

   assign eventsFromNarby = 30;
   assign eventsFromAjar = 20;

   wire [4:0] totalEvents = eventsFromNearby + eventsFromAfar;

   wire [3:0] kindsOfSoda;
   wire [3:0] kindsOfFruit;

   wire [3:0] kindsOfSda = kindsOfSoda;
   wire [3:0] kindsOfFrut = kindsOfFruit;


endmodule


primitive awful_flop(out, data, clock);

   // total nonsense sequential UDP -- shouldn't have any warnings

   output     out;
   input      data, clock;

   reg 	      out;
   table
      0   r  :  ?  :  0 ;
   endtable
endprimitive


module enumtest;

   enum { FOO = 1, BAR = 2 } a, b;

   assign a = b ? FOO : BAR;

endmodule
