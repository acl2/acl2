module sub1 ;
endmodule

module sub2 ();
   initial $display("Hello from %m");
endmodule

module top (input a);

   buf mysub1 (o, a);

   bind mysub1 sub2 mysub2 ();

endmodule
