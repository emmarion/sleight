; needs: list
; expect: 1
; A delegate whose argument and result pass through coerces: both erase to renamings (section 19).

(def-adts $ (Meters : -> Type)
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))

(def-lvl L)
(def-fns L $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-lvl M)
(let ((erased p)) (prove-predates L M))

(def-fns M $ (many inc-meters : (many (Meters) x) -> (many (Meters) r))
  (let-match erased x (MkMeters n))
  (let ((many k)) (coerce x (coercible-sym (coercible-wrap (Shared) MkMeters n))))
  (let ((many j)) (delegate (inc (predates p) k)))
  (coerce j (coercible-wrap (Shared) MkMeters j)))

(let ((erased ig)) (coercible-of (delegate-of inc-meters)))
(let ((many (Fn L (many (Nat) a) -> (many (Nat) b)) g)) (coerce inc-meters ig))
(g (Zero))
; warns: tests/delegate_coerce.sl:17:34: warning: unnecessary `(predates _)`; drop it
