#ifndef MY_CONST
#error("MY_CONST not defined.");
#endif

int foo () {
  int x = MY_CONST;
  int y = 2;
  return x+y;
}
