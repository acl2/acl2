// This example shows the need to pass by reference given a mix of
// mutation pointer aliasing.

int main(void) {
  int x = 0;
  int * y = &x;

  // Split here
  x++;
  return *y;
}
