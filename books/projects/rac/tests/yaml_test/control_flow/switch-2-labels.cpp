// RAC begin

int foo(int x) {

  int a = 0;
  switch (x) {
  case 0:
  case 1:
    a = 2;
    break;
  default:
    a = 0;
    break;
  }
  return a;
}
