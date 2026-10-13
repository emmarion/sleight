staload "libats/SATS/ilist_prf.sats"

stadef sz = sizeof(lint)

dataprop LE(int, int) = {x,y:int | x <= y} LE(x, y)

dataprop SWAP(ilist, int, int, ilist) =
  {xs,zs,ys:ilist}{i,j:nat}{x,y:int}
  SWAP(xs, i, j, ys) of
    (NTH(x, xs, i), NTH(y, xs, j), UPDATE(y, xs, i, zs), UPDATE(x, zs, j, ys))

dataprop PERM(ilist, ilist) =
  | {xs:ilist} PERMnil(xs, xs)
  | {xs,ys,zs:ilist}{i,j:int} PERMsnoc(xs, zs) of (PERM(xs, ys), SWAP(ys, i, j, zs))

dataprop SORTED(ilist) =
  | SORTEDnil(ilist_nil)
  | {x:int} SORTEDone(ilist_sing(x))
  | {x,y:int}{ys:ilist}
    SORTEDcons(ilist_cons(x, ilist_cons(y, ys))) of (LE(x, y), SORTED(ilist_cons(y, ys)))

dataview arr_v(addr, ilist) =
  | {l:addr} arr_nil(l, ilist_nil)
  | {l:addr}{x:int}{xs:ilist}
    arr_cons(l, ilist_cons(x, xs)) of (lint(x) @ l, arr_v(l+sz, xs))

prfun nth_fun {x,y:int}{xs:ilist}{i:nat} .<i>.
  (a: NTH(x, xs, i), b: NTH(y, xs, i)): [x == y] void =
  case+ (a, b) of
  | (NTHbas(), NTHbas()) => ()
  | (NTHind(a), NTHind(b)) => nth_fun(a, b)

prfun nth_exists {xs:ilist}{n,i:int | 0 <= i; i < n} .<i>.
  (pl: LENGTH(xs, n)): [x:int] NTH(x, xs, i) = let
  prval LENGTHcons(pl) = pl
in
  sif i == 0 then NTHbas() else NTHind(nth_exists{..}{n-1,i-1}(pl))
end

prfun nth_bound {x:int}{xs:ilist}{n:int}{i:nat} .<i>.
  (pl: LENGTH(xs, n), a: NTH(x, xs, i)): [i < n] void =
  case+ (a, pl) of
  | (NTHbas(), LENGTHcons(_)) => ()
  | (NTHind(a), LENGTHcons(pl)) => nth_bound(pl, a)

prfun upd_exists {y:int}{x:int}{xs:ilist}{i:nat} .<i>.
  (a: NTH(x, xs, i)): [ys:ilist] UPDATE(y, xs, i, ys) =
  case+ a of NTHbas() => UPDATEbas() | NTHind(a) => UPDATEind(upd_exists{y}(a))

prfun upd_self {x:int}{xs:ilist}{i:nat} .<i>.
  (a: NTH(x, xs, i)): UPDATE(x, xs, i, xs) =
  case+ a of NTHbas() => UPDATEbas() | NTHind(a) => UPDATEind(upd_self(a))

prfun upd_length {y:int}{xs,ys:ilist}{i:nat}{n:int} .<i>.
  (u: UPDATE(y, xs, i, ys), pl: LENGTH(xs, n)): LENGTH(ys, n) =
  case+ (u, pl) of
  | (UPDATEbas(), LENGTHcons(pl)) => LENGTHcons(pl)
  | (UPDATEind(u), LENGTHcons(pl)) => LENGTHcons(upd_length(u, pl))

prfun upd_nth_same {y,z:int}{xs,ys:ilist}{i:nat} .<i>.
  (u: UPDATE(y, xs, i, ys), a: NTH(z, ys, i)): [z == y] void =
  case+ (u, a) of
  | (UPDATEbas(), NTHbas()) => ()
  | (UPDATEind(u), NTHind(a)) => upd_nth_same(u, a)

prfun upd_nth_other {y,z:int}{xs,ys:ilist}{i,k:nat | i != k} .<k>.
  (u: UPDATE(y, xs, i, ys), a: NTH(z, ys, k)): NTH(z, xs, k) =
  case+ (u, a) of
  | (UPDATEbas(), NTHind(a)) => NTHind(a)
  | (UPDATEind(_), NTHbas()) => NTHbas()
  | (UPDATEind(u), NTHind(a)) => NTHind(upd_nth_other(u, a))

(* k2: the position in xs of the value now at position k in ys *)
prfn swap_nth {xs,ys:ilist}{i,j:int}{k:nat}{z:int}
  (sw: SWAP(xs, i, j, ys), a: NTH(z, ys, k))
  : [k2:nat | (k == j && k2 == i) || (k != j && k == i && k2 == j) || (k != i && k != j && k2 == k)]
    NTH(z, xs, k2) = let
  prval SWAP(px, py, u1, u2) = sw
in
  sif k == j then let prval () = upd_nth_same(u2, a) in px end
  else let prval a = upd_nth_other(u2, a) in
    sif k == i then let prval () = upd_nth_same(u1, a) in py end
    else upd_nth_other(u1, a)
  end
end

(* the cell at position i, and the way back to the array with that cell set to y *)
prfun take {l:addr}{xs,ys:ilist}{i:nat}{x,y:int} .<i>.
  (a: NTH(x, xs, i), u: UPDATE(y, xs, i, ys), pa: arr_v(l, xs))
  : (lint(x) @ l+i*sz, lint(y) @ l+i*sz -<lin,prf> arr_v(l, ys)) =
  case+ (a, u) of
  | (NTHbas(), UPDATEbas()) => let
      prval arr_cons(c0, r) = pa
    in
      (c0, llam c => arr_cons(c, r))
    end
  | (NTHind(a), UPDATEind(u)) => let
      prval arr_cons(c0, r) = pa
      prval (c, f) = take(a, u, r)
    in
      (c, llam c => arr_cons(c0, f(c)))
    end

fn get {l:addr}{xs:ilist}{n:int}{i:nat | i < n}
  (pl: LENGTH(xs, n), pa: !arr_v(l, xs) | p: ptr l, i: size_t i)
  : [x:int] (NTH(x, xs, i) | lint x) = let
  prval a = nth_exists{xs}{n,i}(pl)
  prval (c, f) = take(a, upd_self(a), pa)
  val x = !(ptr_add<lint>(p, i))
  prval () = pa := f(c)
in
  (a | x)
end

fn set {l:addr}{xs:ilist}{n:int}{i:nat | i < n}{y:int}
  (pl: LENGTH(xs, n), pa: !arr_v(l, xs) >> arr_v(l, ys) | p: ptr l, i: size_t i, y: lint y)
  : #[ys:ilist] (UPDATE(y, xs, i, ys), LENGTH(ys, n) | void) = let
  prval a = nth_exists{xs}{n,i}(pl)
  prval u = upd_exists{y}(a)
  prval (c, f) = take(a, u, pa)
  val () = !(ptr_add<lint>(p, i)) := y
  prval () = pa := f(c)
in
  (u, upd_length(u, pl) | ())
end

fn swap {l:addr}{xs:ilist}{n:int}{i,j:nat | i < n; j < n}{x,y:int}
  ( pl: LENGTH(xs, n), px: NTH(x, xs, i), py: NTH(y, xs, j)
  , pa: !arr_v(l, xs) >> arr_v(l, ys)
  | p: ptr l, i: size_t i, j: size_t j, x: lint x, y: lint y)
  : #[ys:ilist] (SWAP(xs, i, j, ys), LENGTH(ys, n) | void) = let
  val (u1, pl | ()) = set(pl, pa | p, i, y)
  val (u2, pl | ()) = set(pl, pa | p, j, x)
in
  (SWAP(px, py, u1, u2), pl | ())
end

(* every parent p >= k other than i is >= its children below m *)
propdef HEAPEXC(xs:ilist, k:int, i:int, m:int) =
  {p,j:int | p >= k; p != i; 2*p+1 <= j; j <= 2*p+2; j < m}{x,y:int}
  (NTH(x, xs, j), NTH(y, xs, p)) -<prf> LE(x, y)

propdef HEAP(xs:ilist, k:int, m:int) = HEAPEXC(xs, k, ~1, m)

(* the children of i are <= the parent q of i, when q >= k *)
propdef GRAND(xs:ilist, k:int, i:int, m:int) =
  {q,j:int | q >= k; 2*q+1 <= i; i <= 2*q+2; 2*i+1 <= j; j <= 2*i+2; j < m}{x,y:int}
  (NTH(x, xs, j), NTH(y, xs, q)) -<prf> LE(x, y)

(* xs[i] <= xs[j] whenever i < j and j >= m *)
propdef SUFFIX(xs:ilist, m:int) =
  {i,j:nat | i < j; m <= j}{x,y:int}
  (NTH(x, xs, i), NTH(y, xs, j)) -<prf> LE(x, y)

(* positions >= m of ys hold the same values as in xs; values below m come from below m *)
propdef STAYS(xs:ilist, ys:ilist, m:int) =
  {k:nat}{z:int} NTH(z, ys, k) -<prf>
  [k2:nat | (k >= m && k2 == k) || (k < m && k2 < m)] NTH(z, xs, k2)

prfn le_of_nth {xs:ilist}{i:nat}{x,v,w:int | v <= w}
  (a: NTH(x, xs, i), b: NTH(v, xs, i)): LE(x, w) = let prval () = nth_fun(a, b) in LE() end

(* every child of i below m is <= w *)
propdef CMAX(xs:ilist, i:int, m:int, w:int) =
  {j:int | 2*i+1 <= j; j <= 2*i+2; j < m}{x:int} NTH(x, xs, j) -<prf> LE(x, w)

prfn cmax2 {xs:ilist}{i:nat}{m:int}{v1,v2,w:int | v1 <= w; v2 <= w}
  (p1: NTH(v1, xs, 2*i+1), p2: NTH(v2, xs, 2*i+2)): CMAX(xs, i, m, w) =
  lam {j:int | 2*i+1 <= j; j <= 2*i+2; j < m}{x:int} (a: NTH(x, xs, j)): LE(x, w) =<prf>
    sif j == 2*i+1 then le_of_nth(a, p1) else le_of_nth(a, p2)

prfn cmax1 {xs:ilist}{i:nat}{m:int | m <= 2*i+2}{v1:int}
  (p1: NTH(v1, xs, 2*i+1)): CMAX(xs, i, m, v1) = lam a =<prf> le_of_nth(a, p1)

prfn stays_id {m:int}{xs:ilist} (): STAYS(xs, xs, m) = lam a =<prf> a

prfn grand_none {k,m:nat}{xs:ilist} (): GRAND(xs, k, k, m) = lam (a, b) =<prf> LE()

prfun rootmax {xs:ilist}{n,m:int | m <= n}{r:int}{a:nat | a < m}{x:int} .<a>.
  (pl: LENGTH(xs, n), ph: HEAP(xs, 0, m), pr: NTH(r, xs, 0), pa: NTH(x, xs, a)): LE(x, r) =
  sif a == 0 then le_of_nth(pa, pr)
  else let
    prval pq = nth_exists{xs}{n, (a-1)/2}(pl)
    prval LE() = ph(pa, pq)
    prval LE() = rootmax{xs}{n,m}(pl, ph, pr, pq)
  in
    LE()
  end

prfn suffix_none {xs:ilist}{n:int} (pl: LENGTH(xs, n)): SUFFIX(xs, n) =
  lam (a, b) =<prf> let prval () = nth_bound(pl, b) in LE() end

prfun sorted_of_suffix {xs:ilist}{n:nat} .<n>.
  (pl: LENGTH(xs, n), ps: SUFFIX(xs, 1)): SORTED(xs) =
  case+ pl of
  | LENGTHnil() => SORTEDnil()
  | LENGTHcons(pl1) => (case+ pl1 of
    | LENGTHnil() => SORTEDone()
    | LENGTHcons(_) =>
        SORTEDcons(
          ps(NTHbas(), NTHind(NTHbas())),
          sorted_of_suffix(pl1, lam (a, b) =<prf> ps(NTHind(a), NTHind(b)))))

prfn stays_swap {m:int}{xs0,xs,ys:ilist}{i,j:int | i < m; j < m}
  (sw: SWAP(xs, i, j, ys), ps: STAYS(xs0, xs, m)): STAYS(xs0, ys, m) =
  lam a =<prf> ps(swap_nth(sw, a))

prfn sift_heap {k,m:int}{xs,ys:ilist}{i,c:int | 0 <= k; k <= i; c == 2*i+1 || c == 2*i+2; c < m}{vi,vc:int | vi < vc}
  ( sw: SWAP(xs, i, c, ys), pi: NTH(vi, xs, i), pc: NTH(vc, xs, c)
  , ph: HEAPEXC(xs, k, i, m), pg: GRAND(xs, k, i, m), pmax: CMAX(xs, i, m, vc))
  : HEAPEXC(ys, k, c, m) =
  lam {p,j:int | p >= k; p != c; 2*p+1 <= j; j <= 2*p+2; j < m}{x,y:int}
    (a: NTH(x, ys, j), b: NTH(y, ys, p)): LE(x, y) =<prf> let
    prval a = swap_nth(sw, a)
    prval b = swap_nth(sw, b)
  in
    sif p == i then let
      prval () = nth_fun(b, pc)
    in
      sif j == c then le_of_nth(a, pi) else pmax(a)
    end
    else sif j == i then let
      prval () = nth_fun(a, pc)
    in
      pg(pc, b)
    end
    else ph(a, b)
  end

prfn sift_grand {k,m:int}{xs,ys:ilist}{i,c:int | 0 <= k; k <= i; c == 2*i+1 || c == 2*i+2}
  (sw: SWAP(xs, i, c, ys), ph: HEAPEXC(xs, k, i, m)): GRAND(ys, k, c, m) =
  lam (a, b) =<prf> ph(swap_nth(sw, a), swap_nth(sw, b))

fn child {l:addr}{xs:ilist}{n,i,m:int | 0 <= i; 2*i+1 < m; m <= n}{v1:int}
  (pl: LENGTH(xs, n), p1: NTH(v1, xs, 2*i+1), pa: !arr_v(l, xs) | p: ptr l, i: size_t i, m: size_t m, v1: lint v1)
  : [c,vc:int | c == 2*i+1 || c == 2*i+2; c < m] (NTH(vc, xs, c), CMAX(xs, i, m, vc) | size_t c, lint vc) = let
  val c2 = i + i + 2
in
  if c2 < m then let
    val (p2 | v2) = get(pl, pa | p, c2)
  in
    if v1 < v2 then (p2, cmax2{xs}{i}{m}(p1, p2) | c2, v2) else (p1, cmax2{xs}{i}{m}(p1, p2) | c2 - 1, v1)
  end
  else (p1, cmax1{xs}{i}{m}(p1) | c2 - 1, v1)
end

fun sift {k,m:int}{l:addr}{xp,xs0,xs:ilist}{n,i:int | 0 <= k; k <= i; i < m; m <= n} .<m-i>.
  ( pl: LENGTH(xs, n), ph: HEAPEXC(xs, k, i, m), pg: GRAND(xs, k, i, m)
  , ps: STAYS(xs0, xs, m), pp: PERM(xp, xs)
  , pa: !arr_v(l, xs) >> arr_v(l, ys)
  | p: ptr l, i: size_t i, m: size_t m)
  : #[ys:ilist] (LENGTH(ys, n), HEAP(ys, k, m), STAYS(xs0, ys, m), PERM(xp, ys) | void) = let
  val c1 = i + i + 1
in
  if c1 >= m then (pl, (lam (a, b) =<prf> ph(a, b)): HEAP(xs, k, m), ps, pp | ())
  else let
    val (pi | vi) = get(pl, pa | p, i)
    val (p1 | v1) = get(pl, pa | p, c1)
    val (pc, pmax | c, vc) = child(pl, p1, pa | p, i, m, v1)
  in
    if vi >= vc then
      (pl, lam {p,j:int | p >= k; p != ~1; 2*p+1 <= j; j <= 2*p+2; j < m}{x,y:int}
             (a: NTH(x, xs, j), b: NTH(y, xs, p)): LE(x, y) =<prf>
             sif p == i then let prval LE() = pmax(a); prval () = nth_fun(pi, b) in LE() end
             else ph(a, b), ps, pp | ())
    else let
      val (sw, pl | ()) = swap(pl, pi, pc, pa | p, i, c, vi, vc)
    in
      sift{k,m}(pl, sift_heap{k,m}(sw, pi, pc, ph, pg, pmax), sift_grand{k,m}(sw, ph), stays_swap{m}(sw, ps),
        PERMsnoc(pp, sw), pa | p, c, m)
    end
  end
end

fun heapify {n,i:nat | i <= n}{l:addr}{xp,xs:ilist} .<i>.
  ( pl: LENGTH(xs, n), ph: HEAP(xs, i, n), pp: PERM(xp, xs)
  , pa: !arr_v(l, xs) >> arr_v(l, ys)
  | p: ptr l, i: size_t i, n: size_t n)
  : #[ys:ilist] (LENGTH(ys, n), HEAP(ys, 0, n), PERM(xp, ys) | void) =
  if i > 0 then let
    val (pl, ph, _, pp | ()) =
      sift{i-1,n}(pl, (lam (a, b) =<prf> ph(a, b)): HEAPEXC(xs, i-1, i-1, n),
        grand_none{i-1,n}(), stays_id{n}(), pp, pa | p, i - 1, n)
  in
    heapify{n,i-1}(pl, ph, pp, pa | p, i - 1, n)
  end
  else (pl, ph, pp | ())

prfn down_heap {m:int}{xs,ys:ilist}
  (sw: SWAP(xs, 0, m-1, ys), ph: HEAP(xs, 0, m)): HEAPEXC(ys, 0, 0, m-1) =
  lam (a, b) =<prf> ph(swap_nth(sw, a), swap_nth(sw, b))

prfn down_suffix {m,n:int | 1 < m; m <= n}{xs,ys,zs:ilist}{r:int}
  ( pl: LENGTH(xs, n), ph: HEAP(xs, 0, m), pr: NTH(r, xs, 0), psf: SUFFIX(xs, m)
  , sw: SWAP(xs, 0, m-1, ys), pst: STAYS(ys, zs, m-1))
  : SUFFIX(zs, m-1) =
  lam {i,j:nat | i < j; m-1 <= j}{x,y:int} (a: NTH(x, zs, i), b: NTH(y, zs, j)): LE(x, y) =<prf> let
    prval a = swap_nth(sw, pst(a))
    prval b = swap_nth(sw, pst(b))
  in
    sif j == m-1 then let prval () = nth_fun(b, pr) in rootmax{xs}{n,m}(pl, ph, pr, a) end
    else psf(a, b)
  end

fun sortdown {l:addr}{xp,xs:ilist}{n,m:nat | m <= n} .<m>.
  ( pl: LENGTH(xs, n), ph: HEAP(xs, 0, m), psf: SUFFIX(xs, m), pp: PERM(xp, xs)
  , pa: !arr_v(l, xs) >> arr_v(l, ys)
  | p: ptr l, m: size_t m)
  : #[ys:ilist] (LENGTH(ys, n), SUFFIX(ys, 1), PERM(xp, ys) | void) =
  if m > 1 then let
    val m1 = m - 1
    val (pr | r) = get(pl, pa | p, i2sz(0))
    val (pt | t) = get(pl, pa | p, m1)
    val (sw, pl1 | ()) = swap(pl, pr, pt, pa | p, i2sz(0), m1, r, t)
    val (pl1, ph1, pst, pp | ()) =
      sift{0,m-1}(pl1, down_heap{m}(sw, ph), grand_none{0,m-1}(), stays_id{m-1}(), PERMsnoc(pp, sw), pa | p, i2sz(0), m1)
  in
    sortdown(pl1, ph1, down_suffix{m,n}(pl, ph, pr, psf, sw, pst), pp, pa | p, m1)
  end
  else (pl, (lam (a, b) =<prf> psf(a, b)): SUFFIX(xs, 1), pp | ())

fn heapsort {l:addr}{xs:ilist}{n:nat}
  (pl: LENGTH(xs, n), pa: !arr_v(l, xs) >> arr_v(l, ys) | p: ptr l, n: size_t n)
  : #[ys:ilist] (LENGTH(ys, n), PERM(xs, ys), SORTED(ys) | void) = let
  val (pl, ph, pp | ()) =
    heapify(pl, (lam (a, b) =<prf> LE()): HEAP(xs, n/2, n), PERMnil(), pa | p, half(n), n)
  val (pl, psf, pp | ()) =
    sortdown(pl, ph, suffix_none(pl), pp, pa | p, n)
in
  (pl, pp, sorted_of_suffix(pl, psf) | ())
end
