#include <array>
using namespace std;

// RAC begin
//
struct A
{
  struct { int a; int b; } w;
};



int foo()
{
  A a;
  a.w.a = 3;
  a.w.b = 4;

  return a.w.a + a.w.b;
}

// RAC end
