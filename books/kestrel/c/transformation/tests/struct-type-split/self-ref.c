struct point {
  int x;
  int z;
  struct point *next;
  struct point **indirect;
  struct point *children[2];
};

static struct point p = {.x = 1, .z = 2, .next = &p};

int main(void) {
  return p.next->x + p.next->z;
}
