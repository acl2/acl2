int main(void);

extern int call_main(int x) {
  return main();
}

static void foo(void) {
    main();

    // Not resolved
    void (*bar)(void) = &foo;
    // Note: this may superficially look like bar is a function.
    bar();
}

int main(void) {
  foo();
  return 0;
}
