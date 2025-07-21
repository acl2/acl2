void bar(int *);

int foo(int y) {
  int x = 5;
  // Split should be triggered here
  bar(&y);
  return x + y;
}
