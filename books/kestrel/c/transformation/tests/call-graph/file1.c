extern int call_main(int x);

static int foo(void) {
  int x = call_main(0);
  return x;
}

static int fibonacci(int x) {
  if (x <= 1) {
    return x;
  }
  return fibonacci(x-1) + fibonacci(x-2);
}
