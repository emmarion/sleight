; expect: 3
; WARNINGS.md 10. The ; warns: lines at the end of the file name lines of this file.


(def-adts $ (D : -> Type) enum (many A : -> (D)) (many B : (many (Nat) n) -> (D)))
(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))

(def-fns _ $ (many f : (many (String) s) (many (Nat) spare) (many (Nat) ghost) (erased (Lt ghost 5) _lt) -> (many (Nat) r))
  (let ((many n) (erased q)) (str-length s))
  (let ((many m) (erased _q)) (str-length s))
  (let ((many proof-only)) m)
  (let ((erased e)) (prove-subterm proof-only (Succ proof-only)))
  (def-lvl idle)
  (def-fns _ $ (many helper : (many (Nat) _x) -> (many (Nat) y)) 0)
  (match many n _
    ((Zero) 1)
    ((Succ j) (values n))))

(def-fns _ $ (many same : (many (D) x) -> (many x is r at x))
  (match many x _ ((A u) (at (u))) (else y (let ((many z)) 0) x)))

(def-fns _ $ (many second : (many (Nat) word) (many (Nat) other at word) -> (many (Nat) r)) other)

(def-fns _ $ (many cells : -> (many (Nat) r))
  (let ((many a)) (Zero))
  (let ((many b)) (Succ (Succ (Zero))))
  (let ((unique u)) (cell-alloc (P (slot-of a) (slot-of b))))
  (let ((unique v))
    (cell-match unique u (((Cell P (slot-of a) (slot-of b)) v at u))
      (P s t back) back))
  (let ((many p)) (share (at (v a b))))
  (let-match many p (P x y)) y)

(def-adts $ (Void : -> Type) enum)
(def-fns _ $ (many absurd explode : (many (Void) v) (many (Nat) k) -> (many (Nat) r)) v)

(def-fns _ $ (many head-or-zero : (many (List (Nat)) l) -> (many (Nat) r))
  (match many l _ ((Cons _ h t c) h) ((Nil _) 0)))

(let ((many seven)) (let ((many vs)) values) (vs 7))

(def-fns _ $ (many typed : (many (Nat) a0) -> (many (Nat) r))
  (let ((many (Nat) w) (erased (Eq (Nat) w w) wp)) (values a0 (Refl (Nat) a0)))
  0)

(let ((many top-unused)) (B 1))
(let ((many kept)) (same top-unused))
(f "abc" (cells) 2 (prove-literal-lt 2 5))
; warns: tests/unused_warn.sl:8:42: warning: unused `spare`; rename it `_spare`
; warns: tests/unused_warn.sl:8:61: warning: `ghost` is referenced only in erased positions; declare it `erased`, or rename it `_ghost`
; warns: tests/unused_warn.sl:9:18: warning: unused `q`; write `_` in its place
; warns: tests/unused_warn.sl:11:9: warning: `proof-only` is referenced only in erased positions; declare it `erased`
; warns: tests/unused_warn.sl:12:9: warning: unused `e`; delete its `let`
; warns: tests/unused_warn.sl:13:12: warning: unused `idle`; delete it
; warns: tests/unused_warn.sl:14:16: warning: unused `helper`; delete it
; warns: tests/unused_warn.sl:17:12: warning: unused `j`; write `_` in its place
; warns: tests/unused_warn.sl:20:42: warning: unused `y`; delete it
; warns: tests/unused_warn.sl:20:50: warning: unused `z`; delete its `let`
; warns: tests/unused_warn.sl:30:10: warning: unused `s`; write `_` in its place
; warns: tests/unused_warn.sl:30:12: warning: unused `t`; write `_` in its place
; warns: tests/unused_warn.sl:32:24: warning: unused `x`; write `_` in its place
; warns: tests/unused_warn.sl:35:53: warning: unused `k`; rename it `_k`
; warns: tests/unused_warn.sl:38:30: warning: unused `t`; write `_` in its place
; warns: tests/unused_warn.sl:38:32: warning: unused `c`; delete it
; warns: tests/unused_warn.sl:43:9: warning: `w` is referenced only in erased positions; declare it `erased`
; warns: tests/unused_warn.sl:43:24: warning: unused `wp`; write `_` in its place
