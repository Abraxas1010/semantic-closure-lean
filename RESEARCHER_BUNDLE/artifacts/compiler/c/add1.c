#include <stdio.h>

long long add1(long long x) {
  return (x + 1);
}

int main(void) {
  long long x = 41;
  printf("%lld\n", add1(x));
  return 0;
}
