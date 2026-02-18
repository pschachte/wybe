/* cbits -- support code for the wybe library
   $ clang -c cbits.c -o cbits.o
*/

#include <stdio.h>
#include <assert.h>
#include <gc.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdbool.h>
#include <math.h>
#include <time.h>

unsigned long long g_malloc_count = 0;
clock_t benchmark_clock;
bool benchmark_in_progress = false;

/********************** Support for Wybe int type **********************/

intptr_t print_int(intptr_t x) { return (intptr_t)printf("%"PRIdPTR, x); }

intptr_t read_int() {
    intptr_t x;
    scanf("%"SCNdPTR, &x);
    return x;
}

intptr_t log_int(intptr_t x) { return (intptr_t)fprintf(stderr, "%"PRIdPTR, x); }

intptr_t ipow(intptr_t base, intptr_t exp) {
    intptr_t result = 1;
    while (exp > 0)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }

    return result;
}

intptr_t isqrt(intptr_t x) {
    double s;
    s = sqrt((double) x);
    return (intptr_t)s;
}

intptr_t signum(intptr_t x) {
    return (x > 0) - (x < 0); 
}


/********************** Support for Wybe count type **********************/

uintptr_t print_count(uintptr_t x) { return (uintptr_t)printf("%"PRIuPTR, x); }

uintptr_t read_count() {
    uintptr_t x;
    scanf("%"SCNuPTR, &x);
    return x;
}

uintptr_t log_count(uintptr_t x) { return (uintptr_t)fprintf(stderr, "%"PRIuPTR, x); }

uintptr_t upow(uintptr_t base, uintptr_t exp) {
    uintptr_t result = 1;
    while (exp > 0)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }

    return result;
}

uintptr_t usqrt(uintptr_t x) {
    double s;
    s = sqrt((double) x);
    return (uintptr_t)s;
}


/********************** Support for Wybe int64 type **********************/

int64_t print_int64(int64_t x) { return (int64_t)printf("%"PRId64, x); }

int64_t read_int64() {
    int64_t x;
    scanf("%"SCNd64, &x);
    return x;
}

int64_t log_int64(int64_t x) { return (int64_t)fprintf(stderr, "%"PRId64, x); }

int64_t ipow64(int64_t base, int64_t exp) {
    int64_t result = 1;
    while (exp > 0)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }

    return result;
}

int64_t isqrt64(int64_t x) {
    double s;
    s = sqrt((double) x);
    return (int64_t)s;
}

int64_t signum64(int64_t x) {
    return (x > 0) - (x < 0); 
}


/********************** Support for Wybe count64 type **********************/

uint64_t print_count64(uint64_t x) { return (uint64_t)printf("%"PRIu64, x); }

uint64_t read_count64() {
    uint64_t x;
    scanf("%"SCNu64, &x);
    return x;
}

uint64_t log_count64(uint64_t x) { return (uint64_t)fprintf(stderr, "%"PRIu64, x); }

uint64_t upow64(uint64_t base, uint64_t exp) {
    uint64_t result = 1;
    while (exp > 0)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }

    return result;
}

uint64_t usqrt64(uint64_t x) {
    double s;
    s = sqrt((double) x);
    return (uint64_t)s;
}


/********************** Support for Wybe int32 type **********************/

int32_t print_int32(int32_t x) { return (int32_t)printf("%"PRId32, x); }

int32_t read_int32() {
    int32_t x;
    scanf("%"SCNd32, &x);
    return x;
}

int32_t log_int32(int32_t x) { return (int32_t)fprintf(stderr, "%"PRId32, x); }

int32_t ipow32(int32_t base, int32_t exp) {
    int32_t result = 1;
    while (exp > 0)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }

    return result;
}

int32_t isqrt32(int32_t x) {
    double s;
    s = sqrt((double) x);
    return (int32_t)s;
}

int32_t signum32(int32_t x) {
    return (x > 0) - (x < 0); 
}


/********************** Support for Wybe count32 type **********************/

uint32_t print_count32(uint32_t x) { return (uint32_t)printf("%"PRIu32, x); }

uint32_t read_count32() {
    uint32_t x;
    scanf("%"SCNu32, &x);
    return x;
}

uint32_t log_count32(uint32_t x) { return (uint32_t)fprintf(stderr, "%"PRIu32, x); }

uint32_t upow32(uint32_t base, uint32_t exp) {
    uint32_t result = 1;
    while (exp > 0)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }

    return result;
}

uint32_t usqrt32(uint32_t x) {
    double s;
    s = sqrt((double) x);
    return (uint32_t)s;
}


/********************** Support for Wybe int16 type **********************/

int16_t print_int16(int16_t x) { return (int16_t)printf("%"PRId16, x); }

int16_t read_int16() {
    int16_t x;
    scanf("%"SCNd16, &x);
    return x;
}

int16_t log_int16(int16_t x) { return (int16_t)fprintf(stderr, "%"PRId16, x); }

int16_t ipow16(int16_t base, int16_t exp) {
    int16_t result = 1;
    while (exp > 0)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }

    return result;
}

int16_t isqrt16(int16_t x) {
    double s;
    s = sqrt((double) x);
    return (int16_t)s;
}

int16_t signum16(int16_t x) {
    return (x > 0) - (x < 0); 
}


/********************** Support for Wybe count16 type **********************/

uint16_t print_count16(uint16_t x) { return (uint16_t)printf("%"PRIu16, x); }

uint16_t read_count16() {
    uint16_t x;
    scanf("%"SCNu16, &x);
    return x;
}

uint16_t log_count16(uint16_t x) { return (uint16_t)fprintf(stderr, "%"PRIu16, x); }

uint16_t upow16(uint16_t base, uint16_t exp) {
    uint16_t result = 1;
    while (exp > 0)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }

    return result;
}

uint16_t usqrt16(uint16_t x) {
    double s;
    s = sqrt((double) x);
    return (uint16_t)s;
}


/********************** Support for Wybe int8 type **********************/

int8_t print_int8(int8_t x) { return (int8_t)printf("%"PRId8, x); }

int8_t read_int8() {
    int8_t x;
    scanf("%"SCNd8, &x);
    return x;
}

int8_t log_int8(int8_t x) { return (int8_t)fprintf(stderr, "%"PRId8, x); }

int8_t ipow8(int8_t base, int8_t exp) {
    int8_t result = 1;
    while (exp > 0)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }

    return result;
}

int8_t isqrt8(int8_t x) {
    double s;
    s = sqrt((double) x);
    return (int8_t)s;
}

int8_t signum8(int8_t x) {
    return (x > 0) - (x < 0); 
}


/********************** Support for Wybe count8 type **********************/

uint8_t print_count8(uint8_t x) { return (uint8_t)printf("%"PRIu8, x); }

uint8_t read_count8() {
    uint8_t x;
    scanf("%"SCNu8, &x);
    return x;
}

uint8_t log_count8(uint8_t x) { return (uint8_t)fprintf(stderr, "%"PRIu8, x); }

uint8_t upow8(uint8_t base, uint8_t exp) {
    uint8_t result = 1;
    while (exp > 0)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }

    return result;
}

uint8_t usqrt8(uint8_t x) {
    double s;
    s = sqrt((double) x);
    return (uint8_t)s;
}


/********************** Support for Wybe float type **********************/

int64_t print_float(double x) { return (int64_t)printf("%f", x); }

double read_float() {
    double x;
    scanf("%lf", &x);
    return x;
}

int64_t log_float(double x) { return (int64_t)fprintf(stderr, "%f", x); }

/********************** Support for Wybe string type **********************/

int64_t print_string(const char *s) { return (int64_t)printf("%s", s); }

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

int64_t log_string(const char *s) { return (int64_t)fprintf(stderr, "%s", s); }


/********************** Support for Wybe char type **********************/

int64_t read_char() { 
    int64_t c;
    c = (int64_t)getchar();
    return c;
}

int64_t log_char(const char c) { return (int64_t)fprintf(stderr, "%c", c); }


/********************** Support for memory management **********************/

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


/********************** Support for control library **********************/

void error_exit(char* location, char *message) {
    fflush(stdout);
    fprintf( stderr, "%s: %s\n", location, message);
    exit(1);
}


/********************** Support for benchmarking **********************/

void benchmark_start(char* location) {
    if (benchmark_in_progress) {
        fprintf(stderr, "%s: %s\n", location,
                "Starting a new benchmark when there exists a preceding"
                " benchmark that has not been ended");
        exit(1);
    }
    benchmark_in_progress = true;
    benchmark_clock = clock();
}

double benchmark_end(char* location) {
    if (!benchmark_in_progress) {
        fprintf(stderr, "%s: %s\n", location,
                "Ending an unstarted benchmark");
        exit(1);
    }
    benchmark_in_progress = false;
    return ((double) clock() - benchmark_clock) / CLOCKS_PER_SEC;
}
