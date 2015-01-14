module top (output topout, input topin);

  wire o, a;
  sub #(1) mysub (o, a);

endmodule

module sub (o, a);
  parameter size = 4;
  localparam sizedec = size - 2;
  output o;
  input  a;

  // NCV/VCS seem to handle negative indices in some smarter way.
  // The spec is unclear about what to do here, but we think this
  // should be a huge wire.
  wire [sizedec:0] oops = 0; // the spec is unclear but we think this is a huge wire
  assign oops = a;


/*
  initial begin
    $display("Sizedec is %b", sizedec);           // NCV: 11111111111111111111111111111111
    $display("Oops is %b", oops);                 // NCV: XX
    $display("Sizeof oops is %d", $bits(oops));   // NCV: 2
  end
 */


endmodule
