struct point {
  int x;
  int z;
};

union holder {
  struct point p;
  int i;
};

static union holder h;

int main(void) {
  return h.i;
}
