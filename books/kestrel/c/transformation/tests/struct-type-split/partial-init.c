struct pair {
  int fst;
  int snd;
};

int main(void) {
  struct pair left = { .fst = 1 };
  struct pair right = { .snd = 2 };
  return left.snd + right.fst;
}
