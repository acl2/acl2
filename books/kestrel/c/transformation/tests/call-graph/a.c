int shared(void);

static int helper(void) {
  return 1;
}

int entry(void) {
  return helper() + shared();
}
