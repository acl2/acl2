module top (output topout, input topin);

  wire o, a, b;

  sub mysub (o, a, b);

endmodule


module sub (inout var o, // illegal to use 'inout' and 'var'
            input a,
            input b);

  assign o = a & b;

endmodule
