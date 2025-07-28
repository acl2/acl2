void bar(int *);

int foo() {
  int x = 5;
  int y = 0;
  // Split should be triggered here
  bar(&y);
  return x + y;
}
