unsigned long add_and_sub_all(long arr[], unsigned int len) {
  long total = 0l;
  for (unsigned int i = 0; i < len; i++) {
    total += arr[i];
  }
  for (unsigned int i = 0; i < len; i++) {
    total -= arr[i];
  }
  return (unsigned long)total;
}
