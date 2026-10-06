struct bitfield {
  int : 8;
  int z;
};

struct anonymous_struct {
  struct { int x; };
  int z;
};

struct anonymous_union {
  union { int x; int y; };
  int z;
};
