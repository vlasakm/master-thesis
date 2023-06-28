// // vim: ft=c et sw=4
void *calloc(unsigned long long, unsigned long long);
void free(void *);
int printf(char *, ...);

long count_primes(long n) {
    long capacity = (n + 63) >> 6;
    long *not_prime = calloc(capacity, 8);
    long count = 0;

    for (long p = 2; p < n; p++) {
        if (!(not_prime[p >> 6] & (1ULL << (p & 63)))) {
            count++;
            for (long i = p * p; i <= n; i = i + p) {
                not_prime[i >> 6] = not_prime[i >> 6] | (1ULL << (i & 63));
            }
        }
    }

    free(not_prime);

    return count;
}

int main() {
    long n = 200000000;
    long count = count_primes(n);
    printf("Number of prime numbers up to %ld: %ld\n", n, count);
    return 0;
}
