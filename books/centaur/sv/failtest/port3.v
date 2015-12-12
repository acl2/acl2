interface IFoo;
  logic [3:0] status;
endinterface

interface IBar;
  logic [3:0] status;
endinterface

module top (output topout, input topin);

  IFoo foo1();

  sub mysub(.foo1, .bar1);  // oops, no declaration for bar1


endmodule

module sub (IFoo foo1, IBar bar1) ;

endmodule
