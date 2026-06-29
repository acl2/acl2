struct pair {
  int fst;
  int snd;
};

int f(void);

int main(void) {
  struct pair x = { .fst = f(), .snd = 2 };
  return x.snd;
}
