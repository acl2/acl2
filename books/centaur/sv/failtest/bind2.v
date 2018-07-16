module sub1 ;
endmodule

module sub2 ;
   initial $display("Hello from %m");
endmodule

module top (input a);

   sub1 mysub1 ();

   // Oops, module oops isn't defined
   bind oops : mysub1 sub2 mysub2 ();

endmodule
