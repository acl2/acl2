struct s {
  int a;
  int b;
};

struct selfref {
  int x;
  struct selfref *y;
};

static struct selfref sr;

static struct s s;

int main(void) {
  struct selfref *p = (struct selfref *) &sr;
  return s.b;
}
