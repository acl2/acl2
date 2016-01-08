interface simplebus ;

  logic [2:0] foo;

endinterface

module sub1 (simplebus thebus) ;

endmodule

primitive udp_buf (o, i);

  output o;
  input  i;

  table
    // i   :   o
       1   :   1 ;
       0   :   0 ;
  endtable

endprimitive

module top (output topout, input topin);

  simplebus sb ();

  wire o, i;
  udp_buf mybuf (o, i);

  sub1 mysub1 (mybuf);  // oops, can't use UDP as the argument

endmodule
