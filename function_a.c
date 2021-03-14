#include <stdio.h>

int a_calls = 0;
int a_new_args_calls = 0;

int a(int n, int x) {
  a_calls++;
  
  if (n == 0) {
    return x + 1;
  } else if (x == 0) {
    a_new_args_calls++;
    return a(n - 1, 1);
  } else {
    a_new_args_calls++;
    return a(n - 1, a(n, x - 1));
  }
}

int main(void) {
  int a0 = a(3, 0);
  printf("%i\n", a0);
  int a1 = a(3, 1);
  printf("%i\n", a1);
  int a2 = a(3, 2);
  printf("%i\n", a2);
  int a3 = a(3, 3);
  printf("%i\n", a3);

  return 0;
}
