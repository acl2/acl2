// RAC begin

struct S {
  int a;
  int b;
};

int get(S ss) { return ss.b; }

int set() {
  S ss = {};
  ss.a = 2;
  ss.b = 9;

  S copied = ss;

  return ss.a + ss.b;
}
// RAC end
