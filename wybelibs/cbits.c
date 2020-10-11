/* cbits -- support code for the wybe library
   $ clang -c cbits.c -o cbits.o
*/

#include <stdio.h>
#include <assert.h>
#include <gc.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>

unsigned long long g_malloc_count = 0;

int print_int(int x) {
    return printf("%d", x);
}

int print_float(double x) {
    return printf("%f", x);
}

int print_string(const char *s) {
    return printf("%s", s);
}

int log_int(int x) {
  return fprintf(stderr, "%d", x);
}

int log_float(double x) {
  return fprintf(stderr, "%f", x);
}

int log_string(const char *s) {
  return fprintf(stderr, "%s", s);
}

int log_char(const char c) {
  return fprintf(stderr, "%c", c);
}

int read_char() {
    int ch;
    ch = getchar();
    return ch;
}

int read_int() {
    int x;
    scanf("%d", &x);
    return x;
}

double read_float() {
    double x;
    scanf("%lf", &x);
    return x;
}

char *read_line() {
    // init size
    size_t size = 32;
    // "string" can't contain pointers, so we can use the atomic version
    // to avoid GC scans it.
    char *str = GC_malloc_atomic(sizeof(char) * size);
    int c;
    size_t len = 0;
    while (EOF != (c = getchar()) && c != '\n') {
        str[len++] = c;
        if(len == size) str = GC_realloc(str, sizeof(char) * (size *= 2));
    }
    str[len++] = '\0';
    return GC_realloc(str, sizeof(char) * len);
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
    g_malloc_count += 1;
    return GC_MALLOC(size);
}


void gc_init() {
    // XXX this is a workaround, more detail can be found here:
    // https://github.com/pschachte/wybe/issues/59
    setenv("GC_MARKERS", "1", false);
    GC_INIT();
}


int malloc_count() {
    // XXX may overflow
    return (int)g_malloc_count;
}


void error_exit(char *message) {
    fprintf( stderr, "%s\n", message);
    exit(1);
}
