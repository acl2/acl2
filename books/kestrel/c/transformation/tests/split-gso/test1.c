struct myStruct {
  int foo;
  _Bool bar;
  unsigned long int baz;
};

static struct myStruct my;

int main(void) {
  return my.foo + (-my.bar);
}
