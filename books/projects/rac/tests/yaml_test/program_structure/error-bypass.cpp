#include <array>
using namespace std;

// RAC begin

int foo(int a, array<int, 3> b) { return a && b; }
int bar(int a, array<int, 3> b) { return a && b; }

// RAC end
