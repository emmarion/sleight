#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

long ats_cert_sort(const long *src, long *dst, size_t n);
long ats_plain_sort(const long *src, long *dst, size_t n);
long c_sort(const long *src, long *dst, size_t n);

typedef long (*sorter)(const long *, long *, size_t);
static const struct { const char *name; sorter f; } sorts[] = {
  {"cert", ats_cert_sort}, {"plain", ats_plain_sort}, {"c", c_sort}};
enum { NSORTS = sizeof sorts / sizeof sorts[0] };

static int cmp(const void *x, const void *y) {
  long a = *(const long *)x, b = *(const long *)y;
  return (a > b) - (a < b);
}

static void print_u128(unsigned __int128 v) {
  char buf[48]; int k = 47; buf[k] = 0;
  do { buf[--k] = '0' + (int)(v % 10); v /= 10; } while (v);
  fputs(buf + k, stdout);
}

static int bench(const char *name) {
  const size_t n = 1048576;
  long *in = malloc(n * sizeof(long)), *out = malloc(n * sizeof(long));
  uint64_t s = 42;
  for (size_t j = 0; j < n; j++) {
    s = (s * 1103515245u + 12345u) % (1u << 30);
    in[n - 1 - j] = (long)s;
  }
  for (int k = 0; k < NSORTS; k++) {
    if (strcmp(name, sorts[k].name)) continue;
    long ns = sorts[k].f(in, out, n);
    unsigned __int128 sum = 0;
    for (size_t i = 0; i < n; i++) sum += (unsigned __int128)(i + 1) * (unsigned __int128)out[i];
    printf("%s %.3f ms checksum ", name, ns / 1e6);
    print_u128(sum);
    puts("");
    return 0;
  }
  fprintf(stderr, "unknown sort %s\n", name);
  return 1;
}

static int difftest(void) {
  static const long ranges[] = {2, 3, 1000000007};
  uint64_t s = 1;
  long *in = malloc(3000 * sizeof(long)), *ref = malloc(3000 * sizeof(long)),
       *out = malloc(3000 * sizeof(long));
  long cases = 0, fails = 0;
  for (size_t n = 1; n < 3000; n++)
    for (int r = 0; r < 3; r++) {
      for (size_t i = 0; i < n; i++) {
        s = s * 6364136223846793005u + 1442695040888963407u;
        in[i] = (long)((s >> 33) % (uint64_t)ranges[r]);
      }
      memcpy(ref, in, n * sizeof(long));
      qsort(ref, n, sizeof(long), cmp);
      for (int k = 0; k < NSORTS; k++) {
        memset(out, 0xff, n * sizeof(long));
        sorts[k].f(in, out, n);
        cases++;
        if (memcmp(out, ref, n * sizeof(long))) {
          fails++;
          printf("MISMATCH %s n=%zu range=%ld\n", sorts[k].name, n, ranges[r]);
        }
      }
    }
  printf("difftest: %ld cases, %ld mismatches\n", cases, fails);
  return fails != 0;
}

int main(int argc, char **argv) {
  if (argc == 3 && !strcmp(argv[1], "bench")) return bench(argv[2]);
  if (argc == 2 && !strcmp(argv[1], "test")) return difftest();
  fprintf(stderr, "usage: %s bench cert|plain|c | test\n", argv[0]);
  return 2;
}
