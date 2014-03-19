module blankport (o, , a, b);
 output[1:0] o;
 input [1:0] a, b;
 assign o = a & b;
endmodule


