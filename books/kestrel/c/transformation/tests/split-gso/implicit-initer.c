struct myStruct {
  int x;
  _Bool y;
  unsigned long int z;
};

static struct myStruct my = { 1, 0, .x = 2, 1, .z = 2 };

int main(void) {
  return my.x + (-my.y);
}
