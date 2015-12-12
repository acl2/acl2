
interface simplebus (input clk);

  logic a, b;

  parameter foo = 3;

  modport blah( input foo ); // oops, can't connect ports to parameter

endinterface

module top (output topout, input topin);

  wire clk;

  simplebus sb (clk);

endmodule


