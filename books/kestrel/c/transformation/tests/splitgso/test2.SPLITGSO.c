struct myStruct { int foo; _Bool bar; unsigned long int baz; };
struct s1 { int foo; _Bool bar; };
struct s2 { unsigned long int baz; };
static struct s1 my1 = {.foo = 0, .bar = 0};
static struct s2 my2 = {.baz = 42};
int main(void) {
  int x = my1.foo + (-my2.baz);
  struct myStruct my;
  return my.foo + (-my.baz);
}
