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
  a(3, 2);
  printf("%i\n", a_calls);
  printf("%i\n", a_new_args_calls);
  a(7, 5);
  printf("%i\n", a_calls);
  printf("%i\n", a_new_args_calls);
  
  return 0;
}
