module top (input a);

   clocking myclocking @(b); // oops, b isn't declared

   endclocking

endmodule
