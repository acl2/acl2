module top (input a);

   wire clk;
   wire c;

   default clocking @(clk);

      // Some tools reject this and say that unnamed clocking blocks can't have clocking items
      // but others accept it.  I don't see this prohibition in the standard?

      input b = c;

   endclocking

endmodule
