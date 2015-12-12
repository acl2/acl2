
interface simplebus ;

  logic a, b;

  // modport blah( input .foo( {a, b} ) );
  //   -- This should probably be legal, but:
  //      - VCS Version J-2014.12-SP3-1 says this isn't implemented yet
  //      - NCVerilog 15.10-p001 says Unsupported modport expression for port identifier 'foo'.

  // this one should definitely be illegal, right?
  //   - NCV says it's an unsupported modport expression
  //   - VCS accepts it?  who knows what it means
  modport blah( input .foo(a+b) );

endinterface

module top (output topout, input topin);

  wire foo;

  simplebus sb ();

endmodule

