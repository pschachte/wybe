# Prime number benchmark

Find and print the 75,000th prime number.  All these implementations use a Sieve
of Eratosthenes approach.  The loop counts up from 2, finding primes, and adding
them to a collection.  It determines whether each number is prime by checking to
see whether it is divisible by any of the collected prime number; if not, it is
added to the collection of primes.
