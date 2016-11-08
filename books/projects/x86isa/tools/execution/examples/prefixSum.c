// gcc -o prefixSum.o prefixSum.c

#include <stdio.h>
#define N 6

/*
void computePrefixSum (int* data, int* prefixSum, int n) {

  prefixSum[0] = 0;

  for (int i = 1; i < n; i++) {
    prefixSum[i] = prefixSum[i-1] + data[i-1];
  }
}
*/

int computePrefixSum (int* data, int n) {

  int prefixSum = 0;

  for (int i = 0; i < n; i++) {
    prefixSum = prefixSum + data[i];
  }

  return prefixSum;
}

int main(int argc, char ** argv) {
  int data[N] = {7, 2, 3, 1, 9, 2};
  int total;
  int j;

  total = computePrefixSum(data, N);

  for(j = 0; j < N; j++)
    printf("data[%d] = %d\n", j, data[j]);

  printf("\nTotal: %d\n", total);

  return 0;
}
