// RAC begin

template <int a>
int foo() {
  return a;
}

int bar() { return foo(); }

// RAC end
