struct point {
  int x;
  int z;
};

struct outer {
  struct {
    int count;
  };
  struct point arr[];
};
