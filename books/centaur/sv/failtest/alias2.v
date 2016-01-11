module top ;

  wire b;
  alias a = b;   // implicitly declares a
  wire a;        // oops, implicitly declared above

endmodule
