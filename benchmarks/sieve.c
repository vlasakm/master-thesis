// // vim: ft=c et sw=4
void *calloc(unsigned long long, unsigned long long);
void free(void *);
int printf(char *, ...);

long count_primes(long n) {
    char *sieve = calloc(n, 8);
    long count = 0;

    for (long p = 2; p < n; p++) {
        if (!sieve[p]) {
            count++;
            for (long i = p * p; i < n; i = i + p) {
                sieve[i] = 1;
            }
        }
    }

    free(sieve);

    return count;
}

int main() {
    long n = 50000000;
    long count = count_primes(n);
    printf("Number of prime numbers up to %ld: %ld\n", n, count);
    return 0;
}
