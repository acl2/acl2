struct triple {
  int x;
  int y;
  int z;
};

int main(void) {
  struct triple t = { .y = 2, 3 };
  return t.x + t.z;
}
