module top (input a);

   wire clk;
   wire c;

   clocking myclocking @(clk);
      input b = c;
   endclocking

   wire w = b;  // oops, b is not in scope here

endmodule
