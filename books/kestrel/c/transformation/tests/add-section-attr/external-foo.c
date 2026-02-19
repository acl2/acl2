int foo;

int internal_foo(void);

int main(void) {
  foo = 42;
  return internal_foo();
}
