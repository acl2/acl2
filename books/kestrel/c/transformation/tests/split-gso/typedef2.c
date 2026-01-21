typedef struct myStruct {
  int foo;
  _Bool bar;
  unsigned long int baz;
} myStruct_t;

static myStruct_t my;

int main(void) {
  return my.foo + (-my.baz);
}
