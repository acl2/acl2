struct point {
  int x;
  int z;
};

static struct point p;

struct point get(void) {
  return p;
}

int main(void) {
  return get().x;
}
