module top (input a);

   wire clk;

   // Some tools accept this and others reject this.
   // The standard says inout is equivalent to input and output,
   // so this seems like it should be allowed.
   clocking myclocking @(clk);
      input a;
      output a;
   endclocking

endmodule
