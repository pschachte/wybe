// Print the NTH prime number using the Sieve of Eratosthenes

#include <stdio.h>
#include <stdlib.h>

#define NTH 50000

int sieve(int n) {
    int *primes = malloc(n * sizeof(int));
    int prime = 1;
    // loop invariant:  primes[0..i-1] are the first i primes
    for (int i = 0; i < n; i++) {
        for (int candidate = prime+1;; candidate++) {
            // check if candidate is prime
            int is_prime = 1;
            for (int j = 0; j < i; j++) {
                if (candidate % primes[j] == 0) {
                    is_prime = 0;
                    break;
                }
            }
            if (is_prime) {
                primes[i] = prime = candidate;
                break;
            }
        } 
    }
    int result = primes[n-1];
    free(primes);
    return result;
}


int main(void) {
    int n = NTH;
    printf("%d\n", sieve(n));
    return 0;
}
