/* benchmark_impl.c -- support code for benchmarking library
   $ clang -c benchmark_impl.c -o benchmark_impl.o
*/

#include <time.h>
#include <stdbool.h>
#include <stdlib.h>

double get_clock_time() {
    return ((double) clock()) / CLOCKS_PER_SEC;
}
