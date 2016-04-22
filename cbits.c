/* cbits
   $ clang -fPIC -shared cbits.c -o cbits.so
*/

#include <stdio.h>
#include <assert.h>
#include <gc/gc.h>
#include <stdlib.h>
#include <stdint.h>

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

int ipow(int base, int exp) {
    int result = 1;
    while (exp)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }

    return result;
}

int isqrt(int x) {
    double s;
    s = sqrt((double) x);
    return (int)s;
}


// Boehm GC
void *wybe_malloc(int size) {
    return GC_MALLOC(size);
}

void gc_init(){
    GC_INIT();
}

