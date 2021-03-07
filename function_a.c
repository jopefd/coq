#include <stdio.h>

int a(int n, int x) {
  printf("vudu eh pra jacu\n");
  if (n == 0) {
    return x + 1;
  } else if (x == 0) {
    return a(n - 1, 1);
  } else {
    return a(n - 1, a(n, x - 1));
  }
}

int main(void) {
  a(3, 2);
  return 0;
}
