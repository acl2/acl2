struct point {
  int x;
  int z;
};

typedef struct point *pp_t;

static struct point p;
static pp_t q = &p;

int main(void) {
  return q->z;
}
