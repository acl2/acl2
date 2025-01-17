int fibonacci(int x) {
  if (x <= 1) {
    return x;
  }
  return fibonacci(x-1) + fibonacci(x-2);
}
