int bar(void);

int foo(int x) {
  int (*const arr[])(void) = { bar };
  int ret = arr[0]();
  return ret;
}
