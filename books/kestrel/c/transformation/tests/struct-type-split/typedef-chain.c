struct point {
  int x;
  int z;
};

typedef struct point pt_t;

typedef pt_t pt2_t;

static pt2_t p;

int main(void) {
  p.x = 1;
  return p.x + p.z;
}
