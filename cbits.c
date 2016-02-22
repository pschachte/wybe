/* cbits
$ clang -fPIC -shared cbits.c -o cbits.so
*/

#include <stdio.h>
#include <assert.h>
#include <gc/gc.h>
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

int read_char() {
    int ch;
    ch = getchar();
    return ch;        
}

// Boehm GC
void *wybe_malloc(int size) {
    GC_INIT();
    return GC_MALLOC(size);
}
