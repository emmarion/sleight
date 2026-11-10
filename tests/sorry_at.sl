; A tainted entry has no word, so an `at` result is never read back from one: `r` is at the slot of `x`, where a
; tainted `_y` also is, and its word is taken from `x`. A match result written `at` an earlier result is tainted
; when that result is, having no word left to be read from: `b` is tainted with `a`, and `c` is not, nor is
; `d`, which is `at` the untainted `c`.
(def-fns _ $ (many same : (many (Slot) s) (many (Nat) a at s) -> (many (Nat) r at s))
  a)
(def-fns _ $ (many through-coerce : (many (Nat) x) -> (many (Nat) m))
  (let ((erased c)) (sorry (((Coercible (Shared) (Nat) x (Shared) (Nat) x) p))))
  (let ((many _y)) (coerce x c))
  (let ((many r)) (same (slot-of x) x))
  (Succ r))
(def-fns _ $ (many through-sorry : (many (Nat) x) -> (many (Nat) m))
  (let ((many _y)) (sorry (((Nat) r at x))))
  (let ((many r)) (same (slot-of x) x))
  (Succ r))
(def-fns _ $ (many chained : (many (Nat) x) -> (many (Nat) m))
  (let ((many _a) (many b) (many c) (many d)) (match many x (((Nat) a) ((Nat) b at a) ((Nat) c) ((Nat) d at c))
    ((Zero) (values (sorry (((Nat) q at x))) x x x))
    ((Succ p) (values p p x x))))
  (let ((many _u)) (Succ b))
  (nat-add c d))
(MkPair _ _ (through-coerce 5) (through-sorry 5))
;! file "sorry/at-run.sl"
(let ((many x)) (Succ 6))
(let ((many _y)) (sorry (((Nat) r at x))))
(let ((many r)) (same (slot-of x) x))
r
;! file "sorry/at-chained.sl"
(chained 8)
; expect: (MkPair _ _ 6 6)
; expect: 7
; expect: 16
; warns: tests/sorry_at.sl:8:21: warning: this unit uses `sorry` 4 times, first here; nothing that depends on it runs
