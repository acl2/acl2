// RAC begin

int foo(int x) {

  int a = 2;
  switch (x) {
    default:
      a = 0;
    case 1:
      a = 1;
    }
  return a;
}
