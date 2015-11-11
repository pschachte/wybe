/* cbits
$ clang -fPIC -shared cbits.c -o cbits.so
*/

#include <stdio.h>
#include <stdlib.h>

// putchard - putchar that takes a double and returns 0.
void print_int(int X) {
  printf("%d", X);
  fflush(stdout);
}

void print_float(double X) {
  printf("%f", X);
  fflush(stdout);
}

void print_string(const char *s) {
  puts(s);
  fflush(stdout);
}
