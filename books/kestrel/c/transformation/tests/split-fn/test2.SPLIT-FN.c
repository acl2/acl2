unsigned long sub_all(long arr[], unsigned int len, long total) {
  for (unsigned int i = 0; i < len; i++) {
    total -= arr[i];
  }
  return (unsigned long) total;
}
unsigned long add_and_sub_all(long arr[], unsigned int len) {
  long total = 0l;
  for (unsigned int i = 0; i < len; i++) {
    total += arr[i];
  }
  return sub_all(arr, len, total);
}
