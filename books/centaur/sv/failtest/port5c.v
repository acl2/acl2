interface IFoo;
  logic [3:0] status;
endinterface

interface IBar;
  logic [3:0] status;
endinterface

module top (output topout, input topin);

  IFoo foo1();
  IBar bar1();

  wire a, b;

  sub mysub(.foo1(a+b), .bar1(bar1));  // oops, interface connected to a+b

endmodule

module sub (IFoo foo1, IBar bar1) ;

endmodule
