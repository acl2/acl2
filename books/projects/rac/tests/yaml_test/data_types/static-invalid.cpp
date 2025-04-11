// RAC begin

int foo() {
  // This must not be accepted by the parser since it add state to the
  // function.
  static int foo = 3;
  return 0;
}
