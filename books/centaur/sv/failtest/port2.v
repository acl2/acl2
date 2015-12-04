interface IFoo;
  logic [3:0] status;
endinterface

interface IBar;
  logic [3:0] status;
endinterface

module top (output topout, input topin);

  IFoo foo1();
  IFoo foo2();
  IBar bar1();

  sub mysub(.foo1, .foo2, .bar1);  // oops, foo2 doesn't exist


endmodule

module sub (IFoo foo1, IBar bar1) ;

endmodule
