
primitive udp_buf (o, i);

  output o;
  input  i;

  table
    // i   :   o
       1   :   1 ;
       0   :   0 ;
  endtable

endprimitive

interface simplebus ;

  wire myout, myin;

  udp_buf mybuf_inst (myout, myin);  // oops, not allowed to instantiate primitives in interfaces (probably)

  // I can't point to anywhere in the SystemVerilog standard that says
  // you can't do this.
  //
  //   - But I don't think I see a way to have them according to the grammar?
  //   - And you're definitely explicitly prohibited from having module instances (25.3, page 713)
  //   - NCVerilog seems to allow them.
  //   - VCS prohibits them:  Interface "simplebus" has a module instantiation which is not allowed.

endinterface

module top (output topout, input topin);

  wire foo;

  simplebus sb ();

endmodule

