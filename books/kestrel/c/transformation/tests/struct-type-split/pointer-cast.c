struct point {
  int x;
  int z;
};

static struct point p;

int main(void) {
  void *q = (void *)&p;
  return 0;
}
