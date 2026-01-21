// RAC begin

struct S {
  int a = 3;
  int b = 4;
};

int foo() {
  S s = {};
  return s.a;
}

int bar() {
  S s = { 2 };
  return s.a;
}
