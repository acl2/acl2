interface IFoo;
  logic [3:0] status;
endinterface

interface IBar;
  logic [3:0] status;
endinterface

module top (output topout, input topin);

  IFoo foo1();
  IFoo bar1();

  sub mysub(foo1, bar1); // oops, bar1 is the wrong kind of interface

endmodule

module sub (IFoo foo1, IBar bar1) ;

endmodule
