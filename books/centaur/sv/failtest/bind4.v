module sub1 ;
endmodule

module sub2 (input a);
   initial $display("Hello from %m");
endmodule

module top (input a);

   sub1 mysub1 ();

   // oops: a isn't defined in sub1.
   //  -- curiously some tools accept this and infer an implicit wire for A
   //  -- but other tools "properly"? reject it.
   bind mysub1 sub2 mysub2 (a);

endmodule
