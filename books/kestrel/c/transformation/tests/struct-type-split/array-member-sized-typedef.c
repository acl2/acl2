struct point {
  int x;
  int z;
};

typedef struct point point_array[2];

struct outer {
  point_array arr;
};
