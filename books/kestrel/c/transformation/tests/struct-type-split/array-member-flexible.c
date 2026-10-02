struct point {
  int x;
  int z;
};

struct outer {
  int size;
  struct point arr[];
};
