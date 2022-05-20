/* benchmark_impl.c -- support code for benchmarking library
   $ clang -c benchmark_impl.c -o benchmark_impl.o
*/

#include <time.h>
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>

typedef struct {
    clock_t start;
} benchmark_state_t;

benchmark_state_t *benchmark_start() {
    benchmark_state_t *benchmark_state = (benchmark_state_t*) malloc(sizeof(benchmark_state_t));
    assert(benchmark_state);
    benchmark_state->start = clock();
    return benchmark_state;
}

double benchmark_finish(benchmark_state_t *benchmark_state) {
    assert(benchmark_state);
    clock_t end = clock();
    double cpu_time_used = ((double) end - benchmark_state->start) / CLOCKS_PER_SEC;
    free(benchmark_state);
    return cpu_time_used;
}