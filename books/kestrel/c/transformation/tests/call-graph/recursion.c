int fact(int n) {
  return n <= 1 ? 1 : n * fact(n - 1);
}

int even(int n);

int odd(int n) {
  return n == 0 ? 0 : even(n - 1);
}

int even(int n) {
  return n == 0 ? 1 : odd(n - 1);
}

int not_recursive(int n) {
  return fact(n);
}

void callback(void (*f)(void)) {
  f();
}

void declared_only(void);
