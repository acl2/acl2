int foo(int x) {
  if (x == 0) {
    return x;
  }
  return (_Generic((x), default: foo))(({
    int foo = x - 1;
    foo;
  }));
}
int bar(int x) {
  if (x == 0) {
    return x;
  }
  return (_Generic((x), default: bar))(({
    int foo = x - 1;
    foo;
  }));
}
