int setuid(int);
int fork(void);

int foo(int y) {
  int x = 5;
  // Split
  setuid(y);
  x += 1;
  // Split
  fork();
  // Split
  setuid(x);
  return x + y;
}
