int bar(int x, int y) {
  return x + y;
}
int foo(int y) {
  int x = 5;
  return bar(x, y);
}
