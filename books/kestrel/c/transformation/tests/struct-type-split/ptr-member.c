struct point {
  int x;
  int z;
};

struct node {
  struct point *p;
};

static struct point pt;
static struct node n = { .p = &pt };

int main(void) {
  return n.p->x;
}
