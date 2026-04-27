struct myStruct {
  int a;
  int b;
};

static struct myStruct my = {
  .a = 0,
  .b = 0,
};

struct S {
  int x;
};

static struct S static_s;

int foo(void) {
  int x = my.a + (-my.b);
  struct myStruct my;
  if (static_s.x) {
    return my.a + (-my.b);
  }
  return 0;
}
