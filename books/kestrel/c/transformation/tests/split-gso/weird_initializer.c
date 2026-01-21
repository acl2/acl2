struct myStruct {
  int foo;
  _Bool bar;
  unsigned long int baz;
};

static struct myStruct my = {0};

int main(void) {
  int x = my.foo + (-my.baz);
  int size = sizeof(my);
  struct myStruct my;
  return my.foo + (-my.baz);
}
