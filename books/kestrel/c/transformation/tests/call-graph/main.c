int main(void);

extern int call_main(int x) {
  return main();
}

static void foo(void) {
  main();

  // Not resolved
  (*(&foo))();
}

int main(void) {
  foo();
  return 0;
}
