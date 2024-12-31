// RAC begin

struct A {
  int a;
};
struct B {
  int a;
};

template <int a, A b>
int foo() {
  return a;
}

int bar() {
  B s = {};
  return foo<s, 0>();
}

// RAC end
