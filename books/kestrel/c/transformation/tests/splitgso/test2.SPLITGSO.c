struct myStruct { int foo; _Bool bar; unsigned long int baz; };
struct s1 { int foo; _Bool bar; };
struct s2 { unsigned long int baz; };
static struct s1 my1;
static struct s2 my2;
int main(void) {
  int x = my1.foo + (-my2.baz);
  struct myStruct my;
  return my.foo + (-my.baz);
}
