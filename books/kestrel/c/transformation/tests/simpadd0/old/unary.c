int f(int x) {
  return !x;
}

int g(int x) {
  return ~(x = 3);
}

int h(int x) {
  return -(x + 0);
}
