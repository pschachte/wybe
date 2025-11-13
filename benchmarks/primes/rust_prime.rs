// Print the NTH prime number using the Sieve of Eratosthenes

fn sieve(n:i32) -> i32 {
    let mut primes = Vec::new();
    let mut prime = 1;
    // loop invariant:  primes[0..i-1] are the first i primes
    while primes.len() < n as usize {
        let mut candidate = prime + 1;
        loop {
            // check if candidate is prime
            let mut is_prime = true;
            for p in &primes {
                if candidate % p == 0 {
                    is_prime = false;
                    break;
                }
            }
            if is_prime {
                prime = candidate;
                primes.push(prime);
                break;
            } else {
                candidate += 1;
            }
        } 
    }
    prime
}


fn main() -> () {
    let n = 75_000;
    println!("{}", sieve(n));
}
