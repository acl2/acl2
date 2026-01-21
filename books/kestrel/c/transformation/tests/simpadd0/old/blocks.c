void f() {
  int x = 1;
  int y = x + 0;
  {
    unsigned char x = 10;
    int y = (int) x;
    {
      int x = 2;
      int y = x + 0;
    }
  }
}
