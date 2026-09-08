struct s {
  unsigned int a;
  unsigned int b;
};

struct s gso;

unsigned int f(unsigned int x) {
  return x + gso.a + gso.b;
}
