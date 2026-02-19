static int foo = 0;

int internal_foo(void) {
  return foo;
}

extern int foo;
