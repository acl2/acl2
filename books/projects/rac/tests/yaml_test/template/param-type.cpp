// RAC begin

struct A {
  int a;
};
struct B {
  int a;
};

template <int a>
int foo(A b) {
  return a;
}

int bar() {
  B s = {};
  return foo<0>(0);
}

// RAC end
