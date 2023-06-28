// // vim: ft=c et sw=4
void *calloc(unsigned long long, unsigned long long);
void free(void *);
int printf(char *, ...);

long count_primes(long n) {
    long capacity = (n + 63) >> 6;
    long *isPrime = calloc(capacity, 8);
    long count = 0;

    for (long p = 2; p < n; p++) {
        if (!(isPrime[p >> 6] & (1ULL << (p & 63)))) {
            count++;
            for (long i = p * p; i <= n; i = i + p) {
                isPrime[i >> 6] = isPrime[i >> 6] | (1ULL << (i & 63));
            }
        }
    }

    free(isPrime);

    return count;
}

int main() {
    long n = 50000000;
    long count = count_primes(n);
    printf("Number of prime numbers up to %ld: %ld\n", n, count);
    return 0;
}
