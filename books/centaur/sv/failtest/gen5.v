// Not sure whether this should be legal

// NCV rejects it with weird output:
//
// file: gen5.v
// 	module worklib.sub:v
// 		errors: 0, warnings: 0
//     for(sub.i = 0; sub.i < 4; sub.i = sub.i+1) begin

// VCS rejects it as a syntax error:
//
// Error-[SE] Syntax error
//   Following verilog source has syntax error :
//   "gen5.v", 14: token is '.'
//       for(sub.i = 0; sub.i < 4; sub.i = sub.i+1) begin

module sub;

  genvar i;

endmodule

module top ;

  wire [3:0] aa;
  wire [3:0] bb;

  generate
    for(sub.i = 0; sub.i < 4; sub.i = sub.i+1) begin
      not (aa[sub.i], bb[sub.i]);
    end
  endgenerate

endmodule
