module top ;

  wire cond;
  wire [3:0] xx0, xx1, xx2;
  wire [2:0] yy0, yy1, yy2;


  wire [3:0] as_normal1 = xx0;
  wire [3:0] as_normal2 = 0;
  wire [3:0] as_normal3 = 15;
  wire [3:0] as_normal4 = '0;
  wire [3:0] as_normal5 = '1;
  wire [3:0] as_normal6 = 1'b0;

  wire [3:0] as_warn1 = yy0;         // warn because 2-bit answer gets extended to 4 bits
  wire [3:0] as_warn2 = yy0 & yy2;   // warn because 3-bit answer gets extended to 4 bits
  wire [3:0] as_warn3 = xx0 < xx1;   // warn because 1-bit answer gets extended to 4 bits



endmodule
