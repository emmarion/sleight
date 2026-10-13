#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static void sift(long *a, size_t i, size_t m) {
  for (;;) {
    size_t c = 2 * i + 1;
    if (c >= m) return;
    if (c + 1 < m && a[c] < a[c + 1]) c++;
    long vi = a[i], vc = a[c];
    if (vi >= vc) return;
    a[i] = vc; a[c] = vi; i = c;
  }
}

static void heapsort_c(long *a, size_t n) {
  for (size_t i = n / 2; i > 0; i--) sift(a, i - 1, n);
  for (size_t m = n; m > 1; m--) {
    long r = a[0]; a[0] = a[m - 1]; a[m - 1] = r;
    sift(a, 0, m - 1);
  }
}

long c_sort(const long *src, long *dst, size_t n) {
  long *a = malloc(n * sizeof(long) + 1);
  memcpy(a, src, n * sizeof(long));
  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);
  heapsort_c(a, n);
  clock_gettime(CLOCK_MONOTONIC, &t1);
  memcpy(dst, a, n * sizeof(long));
  free(a);
  return (t1.tv_sec - t0.tv_sec) * 1000000000L + (t1.tv_nsec - t0.tv_nsec);
}
