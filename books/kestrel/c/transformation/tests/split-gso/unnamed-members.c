struct myStruct {
  int a;
  int b : 4;
  union { int c; int d; };
  _Bool e;
  int : 4;
  unsigned long int f;
};

static struct myStruct my = { .c = 1, 1, 1 };

int main(void) {
  return my.a + (-my.e);
}
