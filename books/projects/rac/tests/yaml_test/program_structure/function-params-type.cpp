// RAC begin

struct A { int a; };
struct B { int a; };

int foo(int a, A b) { return a; }


int bar() {
  B s;
  return foo(s, 0);
}

// RAC end
