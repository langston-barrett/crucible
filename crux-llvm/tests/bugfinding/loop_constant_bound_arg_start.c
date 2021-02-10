#include <stdio.h>
void loop_constant_bound_arg_start(int i) {
  for (; i < 100; i++) {
    printf("%d\n", i);
  }
}
