module top (input a);

   wire clk;

   // Some tools reject this.  Others accept it, even though it
   // seems clear malformed.

   clocking myclocking @(clk);
      input a;
      input a; // oops, already declared as input
   endclocking

endmodule
