


module top ;

  // There is a master clock that is toggling.
  reg clk = 0;
  always #100 clk = ~clk;

  // Here are some delayed versions of the clock.
  wire #10 clk_del = clk;
  wire #20 clk_del20 = clk;

  // Some variables to mess with.
  integer r1 = 0;
  integer r2 = 0;

  // R1 and R2 will update shortly after the clock.  R2 will always be greater
  // than R1, but they start out the same.
  always @(posedge clk_del) r1 <= r1 + 1;
  always @(posedge clk_del) r2 <= r2 + 2;

  // Stop after 3000 ticks.
  initial begin
    #3000;
    $finish;
  end


  // The following experiment can be used to determine the precedence of
  // clocking sequences compared to AND sequences.  This is very tricky because
  // assertions have some idea of a "semantic leading clock".  I don't want to
  // pay much attention to that.

  // Here is a basic assertion that causes several failures.  On NCVerilog and
  // VCS, these failures happen at times 300, 500, 700, etc.

  // assert property (@(posedge clk)
  //                    1             // on the first cycle, just check True
  //                    ##1           // then in the next cycle
  //                    r1 > r2       // check that r1 > r2.
  //                    );


  // Now let's put in a delay.  On NCVerilog we see that the assertion is now
  // failing at times 120, 320, 520, and so forth.  Actually that probably
  // doesn't make sense anyway, it should probably first fail at 320.  But
  // whatever, that's not what I'm worried about yet. On VCS we are told that
  // the clocks mismatch in the AND sequence operator.

  // assert property (@(posedge clk)
  //                      1                                     // on the first cycle just check True
  //                      ##1                                   // then on the next cycle
  //                      ( @(clk_del20)                        // wait for the delayed clock
  //                            1'b1 and r1 > r2                // and check true and the failure
  //                            )
  //                       );

  // If we instead submit the following, then on NCVerilog we again see that
  // the assertion is failing at 120, 320, 520, etc.  However, on VCS we find
  // that this time the assertion works, and we also get failures at times 120,
  // 320, 520, etc.

  // assert property (@(posedge clk)
  //                     1
  //                     ##1
  //                     ( @(clk_del20)
  //                             ( 1'b1 and r1 > r2 )
  //                          )
  //                     );

  // If we instead submit the following, NCVerilog tells us that we have assertion
  // failures at times 300, 500, 700, etc.  However, VCS tells us that we again
  // have a clock mismatch in the AND sequence operator.

  // assert property (@(posedge clk)
  //                    1
  //                    ##1
  //                    (
  //                         ( @(clk_del20) 1'b1 )
  //                                and
  //                             (r1 > r2)
  //                    ));

  // So it looks like NCVerilog treats @(clk_del20) 1'b1 and r1 > r2
  // identically to:
  //
  //    @(clk_del20) (1'b1 and r1 > r2)
  //
  // whereas VCS treats it identically to:
  //
  //    (@(clk_del20) 1'b1) and (r1 > r2)

  // Hooray for standards.


  // The nice thing about NCV's behavior is that we can just check it against
  // OR and know whether it's lesser precedence than everything.


  // NCV gives us violations at times 120, 320, ...
  // assert property (@(posedge clk)
  //                      1                                     // on the first cycle just check True
  //                      ##1                                   // then on the next cycle
  //                      ( @(clk_del20)                        // wait for the delayed clock
  //                            1'b0 or r1 > r2                 // and check true and the failure
  //                            )
  //                       );

  // And again at 120, 320, ...
  // assert property (@(posedge clk)
  //                      1                                     // on the first cycle just check True
  //                      ##1                                   // then on the next cycle
  //                      ( @(clk_del20)                        // wait for the delayed clock
  //                            (1'b0 or r1 > r2)               // and check true and the failure
  //                            )
  //                       );

  // And these fail at times 300, 500, etc., so I think yes it's definitely
  // lower precedence even than OR.

  assert property (@(posedge clk)
                       1                                     // on the first cycle just check True
                       ##1                                   // then on the next cycle
                       ( ( @(clk_del20) 1'b0)
                                or
                             (r1 > r2)
                             )
                        );


endmodule

