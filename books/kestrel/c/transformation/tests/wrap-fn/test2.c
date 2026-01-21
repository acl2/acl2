extern double foo(int x, int y) {
  return 0;
}

int main(void) {
  int (*foo)(double, double) = 0;
  // This `foo` refers to the local function pointer, *not* the file-scope `foo`
  // function that we are wrapping.
  return foo(0.0, 1.0);
}
