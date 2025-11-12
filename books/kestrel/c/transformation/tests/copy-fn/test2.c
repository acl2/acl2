int foo(int x) {
  if (x) {
    return foo(x - 1);
  } else {
    int (*foo)(int) = 0;
    // This call should *not* be replaced. It is not a recursive call.
    return foo(x);
  }
}
