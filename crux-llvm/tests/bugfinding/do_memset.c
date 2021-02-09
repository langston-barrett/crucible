#include <string.h>
void do_memcpy(void *dest, unsigned long len) {
  memset(dest, 0, len);
}
