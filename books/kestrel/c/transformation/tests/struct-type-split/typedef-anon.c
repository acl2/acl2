typedef struct {
  int x;
  int z;
} point_t;

static point_t p;

int main(void) {
  p.x = 4;
  return p.x + p.z;
}
