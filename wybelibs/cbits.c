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

int64_t print_int(int64_t x) {
    return (int64_t)printf("%ld", x);
}

int64_t print_float(double x) {
    return (int64_t)printf("%f", x);
}

int64_t print_string(const char *s) {
    return (int64_t)printf("%s", s);
}

int64_t log_int(int64_t x) {
  return (int64_t)fprintf(stderr, "%ld", x);
}

int64_t log_float(double x) {
  return (int64_t)fprintf(stderr, "%f", x);
}

int64_t log_string(const char *s) {
  return (int64_t)fprintf(stderr, "%s", s);
}

int64_t log_char(const char c) {
  return (int64_t)fprintf(stderr, "%c", c);
}

int64_t read_char() {
    int64_t ch;
    ch = getchar();
    return ch;
}

int64_t read_int() {
    int64_t x;
    scanf("%ld", &x);
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

int64_t ipow(int64_t base, int64_t exp) {
    int64_t result = 1;
    while (exp)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }

    return result;
}

int64_t isqrt(int64_t x) {
    double s;
    s = sqrt((double) x);
    return (int64_t)s;
}


// Boehm GC
void *wybe_malloc(int64_t size) {
    g_malloc_count += 1;
    return GC_MALLOC(size);
}


void gc_init() {
    // XXX this is a workaround, more detail can be found here:
    // https://github.com/pschachte/wybe/issues/59
    setenv("GC_MARKERS", "1", false);
    GC_INIT();
}


int64_t malloc_count() {
    // XXX may overflow
    return (int64_t)g_malloc_count;
}


void error_exit(char *message) {
    fprintf( stderr, "%s\n", message);
    exit(1);
}
