struct myStruct {
  int foo, bar;
  unsigned int baz;
};

static struct myStruct my = {
  .foo = 0,
  .bar = 0,
  .baz = 42
};

int main(void) {
  int x = my.foo + (-my.baz);
  int size = sizeof(my);
  struct myStruct my;
  return my.foo + (-my.baz);
}
