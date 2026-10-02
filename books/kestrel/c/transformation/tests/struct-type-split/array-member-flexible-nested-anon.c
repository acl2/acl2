struct point {
  int x;
  int z;
};

struct outer {
  int count;
  struct {
    int length;
    struct point arr[];
  };
};
