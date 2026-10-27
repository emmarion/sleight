; needs: lt_subterm div
; expect: 6
; Euclid's algorithm. gcd-mod returns the remainder with an erased proof that it is below the divisor,
; and lt-sub turns that bound into the Subterm proof gcd's recursive call needs.

(def-lvl G)
(let ((erased ng)) (prove-predates nat-lvl G))
(let ((erased sg)) (prove-predates S G))
(def-fns G $ (many gcd-mod : (subterm many (Nat) n) (many (Nat) d1) -> (many (Nat) r) (erased (Lt r (Succ d1)) p))
  (let-match many (lt-dec (predates ng) n (Succ d1)) (No _ _ _ _ le-q) ((Yes _ _ _ _ q) (values n q)))
  (let ((erased q)) (le-lt-succ _ _ le-q))
  (let ((erased lt1)) (match erased q (((Lt d1 n) l)) (absurd LtZ) ((LtS _ _ p1) p1)))
  (let ((many r0) (erased sp)) (sub-pos (predates sg) n d1 lt1))
  (tail $ gcd-mod (subterm sp) r0 d1))

(def-lvl H)
(let ((erased gh)) (prove-predates G H))
(let ((erased lh)) (prove-predates L H))
(def-fns H $ (many gcd : (many (Nat) a) (subterm many (Nat) b) -> (many (Nat) g))
  (let-match many b (Succ b1) ((Zero) a))
  (let ((many r) (erased p)) (gcd-mod (predates gh) a b1))
  (tail $ gcd b (subterm (lt-sub (predates lh) b r p)) r))

(gcd 12 18)
; warns: tests/gcd.sl:10:27: warning: unnecessary `(predates _)`; drop it
; warns: tests/gcd.sl:13:41: warning: unnecessary `(predates _)`; drop it
; warns: tests/gcd.sl:21:39: warning: unnecessary `(predates _)`; drop it
; warns: tests/gcd.sl:22:34: warning: unnecessary `(predates _)`; drop it
