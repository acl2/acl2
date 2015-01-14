module top (output topout, input topin);

  wire w;
  sub mysub (.a); // can't use .a when no wire named a

endmodule


module sub (a);

  input a;

endmodule
