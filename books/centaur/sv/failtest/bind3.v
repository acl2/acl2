module sub1 ;
endmodule

module sub2 ;
   initial $display("Hello from %m");
endmodule

module top (input a);

   sub1 mysub1 ();

   // Oops, instance oops isn't defined
   bind sub1 : oops sub2 mysub2 ();

endmodule
