; needs: list
; expect: (MkMeters 1)
; A tail call whose result is coerced through a non-erased let still counts: after erasure the lets only rename (section 19).

(def-adts $ (Meters : -> Type)
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))

(def-lvl L)
(def-fns L $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-lvl M)
(let ((erased p)) (prove-predates L M))

(def-fns M $ (many inc-m : (many (Nat) n) -> (many (Meters) r))
  (let ((many k)) (tail (inc (predates p) n)))
  (let ((many m)) (coerce k (coercible-wrap (Shared) MkMeters k)))
  m)

(inc-m (Zero))
; warns: tests/tail_coerce.sl:15:30: warning: unnecessary `(predates _)`; drop it
