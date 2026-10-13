#include "share/atspre_staload.hats"
#define ATS_DYNLOADFLAG 0

#include "heapsort_cert.dats"

%{^
#include <time.h>
static inline long mono_ns(void) {
  struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec * 1000000000L + t.tv_nsec;
}
#define rd_lint(p) (*(const long *)(p))
#define wr_lint(p, x) (*(long *)(p) = (x))
#define cells_alloc(n) malloc((n) * sizeof(long) + 1)
#define cells_free(p) free(p)
%}

dataview cells_v(addr, int) =
  | {l:addr} cells_nil(l, 0)
  | {l:addr}{n:nat} cells_cons(l, n+1) of (lint? @ l, cells_v(l+sz, n))

extern fun cells_alloc {n:nat} (n: size_t n): [l:agz] (cells_v(l, n) | ptr l) = "mac#"
extern fun cells_free {l:addr}{n:int} (cells_v(l, n) | ptr l): void = "mac#"

extern fun mono_ns(): lint = "mac#"
extern fun rd_lint(ptr): [x:int] lint(x) = "mac#"
extern fun wr_lint(ptr, lint): void = "mac#"

fun fill {l:addr}{n:nat} .<n>.
  (pf: cells_v(l, n) | p: ptr l, src: ptr, n: size_t n)
  : [xs:ilist] (LENGTH(xs, n), arr_v(l, xs) | void) =
  if n > 0 then let
    prval cells_cons(c, r) = pf
    val () = !p := rd_lint(src)
    val (pl, pa | ()) = fill(r | ptr_succ<lint>(p), ptr_succ<lint>(src), n - 1)
  in
    (LENGTHcons(pl), arr_cons(c, pa) | ())
  end
  else let prval cells_nil() = pf in (LENGTHnil(), arr_nil() | ()) end

fun drain {l:addr}{xs:ilist}{n:nat} .<n>.
  (pl: LENGTH(xs, n), pa: arr_v(l, xs) | p: ptr l, dst: ptr, n: size_t n)
  : (cells_v(l, n) | void) =
  if n > 0 then let
    prval LENGTHcons(pl) = pl
    prval arr_cons(c, r) = pa
    val () = wr_lint(dst, !p)
    val (r | ()) = drain(pl, r | ptr_succ<lint>(p), ptr_succ<lint>(dst), n - 1)
  in
    (cells_cons(c, r) | ())
  end
  else let prval LENGTHnil() = pl; prval arr_nil() = pa in (cells_nil() | ()) end

extern fun ats_cert_sort(src: ptr, dst: ptr, n: Size_t): lint = "ext#"
implement ats_cert_sort(src, dst, n) = let
  val (pf | p) = cells_alloc(n)
  val (pl, pa | ()) = fill(pf | p, src, n)
  val t0 = mono_ns()
  val (pl, pp, ps | ()) = heapsort(pl, pa | p, n)
  val t1 = mono_ns()
  val (pf | ()) = drain(pl, pa | p, dst, n)
in
  cells_free(pf | p); t1 - t0
end
