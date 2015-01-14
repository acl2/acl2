module top (output topout, input topin);

  wire w;
  sub mysub (.*); // can't use .* when no wire named a

endmodule


module sub (a);

  input a;

endmodule
