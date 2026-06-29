struct pair {
  int fst;
  int snd;
};

int main(void) {
  struct pair x = { .fst = 1, .snd = 2 };
  struct pair *ptr = &x;
  return x.fst + ptr->snd;
}
