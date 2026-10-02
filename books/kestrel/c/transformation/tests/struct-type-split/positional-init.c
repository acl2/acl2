struct pair {
  int fst;
  int snd;
};

int main(void) {
  struct pair x = { 1, 2 };
  return x.snd;
}
