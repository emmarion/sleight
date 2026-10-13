#include "share/atspre_staload.hats"
#define ATS_DYNLOADFLAG 0

fun sift {n,i,m:nat | i < m; m <= n} .<m-i>.
  (A: &(@[lint][n]), i: size_t i, m: size_t m): void = let
  val c1 = i + i + 1
in
  if c1 < m then let
    val c2 = c1 + 1
    val c = (if c2 < m then (if A[c1] < A[c2] then c2 else c1) else c1)
      : [c:int | i < c; c < m] size_t c
    val vi = A[i] and vc = A[c]
  in
    if vi < vc then (A[i] := vc; A[c] := vi; sift(A, c, m))
  end
end

fun heapify {n,i:nat | i <= n} .<i>.
  (A: &(@[lint][n]), i: size_t i, n: size_t n): void =
  if i > 0 then (sift(A, i - 1, n); heapify(A, i - 1, n))

fun sortdown {n,m:nat | m <= n} .<m>.
  (A: &(@[lint][n]), m: size_t m): void =
  if m > 1 then let
    val m1 = m - 1
    val r = A[i2sz(0)] and t = A[m1]
  in
    A[i2sz(0)] := t; A[m1] := r; sift(A, i2sz(0), m1); sortdown(A, m1)
  end

fn heapsort_plain {n:nat} (A: &(@[lint][n]), n: size_t n): void =
  (heapify(A, half(n), n); sortdown(A, n))

%{^
#include <string.h>
#include <time.h>
static inline long mono_ns_plain(void) {
  struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1000000000L + t.tv_nsec;
}
#define copy_lints(dst, src, n) memcpy((dst), (src), (n) * sizeof(long))
%}

extern fun mono_ns_plain(): lint = "mac#"
extern fun copy_in {l:addr}{n:int}
  (pf: !array_v(lint?, l, n) >> array_v(lint, l, n) | dst: ptr l, src: ptr, n: size_t n): void = "mac#copy_lints"
extern fun copy_out {l:addr}{n:int}
  (pf: !array_v(lint, l, n) | dst: ptr, src: ptr l, n: size_t n): void = "mac#copy_lints"

extern fun ats_plain_sort(src: ptr, dst: ptr, n: Size_t): lint = "ext#"
implement ats_plain_sort(src, dst, n) = let
  val (pf, pfgc | p) = array_ptr_alloc<lint>(n)
  val () = copy_in(pf | p, src, n)
  val t0 = mono_ns_plain()
  val () = heapsort_plain(!p, n)
  val t1 = mono_ns_plain()
  val () = copy_out(pf | dst, p, n)
in
  array_ptr_free(pf, pfgc | p); t1 - t0
end
