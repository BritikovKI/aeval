// RUN: %sea pf -O0 --abc=%abc_encoding %dsa "%s" 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include <stdio.h>

int MAX_ARRAY = 10;

// To test loops that decrements a counter
int main(int argc, char** argv) {
  int a[MAX_ARRAY];
  int i;
  for (i = MAX_ARRAY - 1; i >= 0; i--) {
    a[i] = i;
  }
  // for underflow check
  printf("%d\n", a[i + 1]);
  // for overflow check
  printf("%d\n", a[MAX_ARRAY - 1]);
  return 0;
}
