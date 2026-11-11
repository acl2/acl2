void leaf(void) {
}

void forms(void) {
  (leaf)();
  (*leaf)();
  (&leaf)();
}

void through_pointer(void (*fp)(void)) {
  fp();
}

void (*global_fp)(void) = leaf;

void through_global_pointer(void) {
  global_fp();
}

void shadowed(void (*leaf)(void)) {
  leaf();
}

void undefined(void);

void calls_undefined(void) {
  undefined();
}

long calls_builtin(long x) {
  return __builtin_expect(x, 0);
}

int calls_unknown_builtin(unsigned x) {
  return __builtin_parity(x);
}

void with_asm(void) {
  __asm__("nop");
}

int size(int n) {
  return n;
}

void vla_param(int n, int a[size(n)]) {
}
