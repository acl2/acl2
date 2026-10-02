struct point {
  int x;
  int z;
};

static struct point p;

int main(void) {
  return sizeof(struct point);
}
