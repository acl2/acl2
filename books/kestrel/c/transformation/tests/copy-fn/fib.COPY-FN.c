int fibonacci(int x) {
  if (x <= 1) {
    return x;
  }
  return fibonacci(x - 1) + fibonacci(x - 2);
}
int fib(int x) {
  if (x <= 1) {
    return x;
  }
  return fib(x - 1) + fib(x - 2);
}
