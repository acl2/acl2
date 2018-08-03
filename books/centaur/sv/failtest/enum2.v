
module top ();

   enum {FOO, BAR} a, b;
   enum {FOO, BAR} c;     // oops, FOO and BAR declared above

endmodule
