double foo(int, int *);
static double wrapper_foo(int wrapper_foo_arg, int *wrapper_foo_arg_0) {
  return foo(wrapper_foo_arg, wrapper_foo_arg_0);
}
int main(void) {
  return wrapper_foo(0, 0);
}
