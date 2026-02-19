struct myStruct {
  int foo;
  _Bool bar;
  unsigned long int baz;
};

static struct myStruct my = {
  .foo = 0,
  .bar = 0,
  .baz = 42
};

int main(void) {
  int x = my.foo + (-my.baz);
  struct myStruct my;
  return my.foo + (-my.baz);
}
