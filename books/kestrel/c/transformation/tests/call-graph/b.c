static int helper(void) {
  return 2;
}

int shared(void) {
  return helper();
}
