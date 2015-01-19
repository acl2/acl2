module m0 (output o, input a, b);
  assign o = a & b;
endmodule

module m1 ;
  initial $display("Hello, world!");
endmodule

interface i0 ;
  logic [3:0] foo, bar;
endinterface

interface i1 (output o, input a);
  logic       b, c;
endinterface



module top ;

  logic w1, w2, w3, w4, w5, w6;

  // Ports don't agree with anything else.
  m0 m0_normal (w1, w2, w4);

  // Same ports all the way across.
  m0 m0_sp_a (w1, w2, w3);
  m0 m0_sp_b (.o(w1), .a(w2), .b(w3));

  // Same inputs but not outputs.
  m0 m0_si_a (w4, w2, w6);
  m0 m0_si_b (.o(w5), .a(w2), .b(w6));

  // I think we shouldn't warn about duplicates when they have no ports, since
  // those are likely to be checker code or something we're not really going to
  // be understanding.
  m1 m1_normal_a ();
  m1 m1_normal_b ();

  // I think we should never warn about interfaces.  Unlike module instances,
  // the interface instance doesn't tell us much of anything.  It is perfectly
  // sensible to have multiple instances of the same interface, and the ports
  // of the interface, if any, aren't the only way info flows into/out of the
  // interface.
  i0 i0_normal_a ();
  i0 i0_normal_b ();

  // Same ports, but don't warn because they're interfaces.
  i1 i1_normal_a (w4, w5);
  i1 i1_normal_b (w4, w5);

  // Same inputs, but don't warn because they're interfaces.
  i1 i1_normal_c (w4, w5);
  i1 i1_normal_d (w5, w5);





  wire 	xx0, xx1, xx2;
  genvar i;
  generate
    for(i = 0; i < 3; ++i) begin : foo
      m0 m0arr(xx0, xx1, xx2);
      i0 i0arr();
    end
  endgenerate

endmodule
