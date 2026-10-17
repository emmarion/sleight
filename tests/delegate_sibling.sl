; expect: 5
; A delegate may name an earlier function of its own block, and a chain of delegates ends at the function
; that is no delegate, which is what every call and every reference runs, in run position and inside a body.
; `via`, earlier in the block, returns a later delegate as a value.

(def-lvl K)
(def-fns K $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))

(def-lvl L)
(let ((erased pkl)) (prove-predates K L))

(def-fns L
  ((many via : -> (many (Fn L (many (Nat) a) (erased (Nat) j) (subterm erased (Succ j) is k) -> (many (Nat) b)) r))
    step1)
  ((many step0 at inc : (many (Nat) a) (subterm erased (Nat) _k) -> (many (Nat) b))
    (delegate (inc (predates pkl) a)))
  ((many step1 at step0 : (many (Nat) a) (erased (Nat) j) (subterm erased (Succ j) is k) -> (many (Nat) b))
    (let ((erased p)) (prove-subterm j k))
    (delegate (step0 a (subterm p) j)))
  ((many step2 at step1 : (many (Nat) a) (erased (Nat) i) (subterm erased (Succ (Succ i)) is k) -> (many (Nat) b))
    (let ((erased p)) (prove-subterm (Succ i) k))
    (delegate (step1 a i (subterm p) (Succ i)))))

(let ((many f)) (via))
(let ((many two)) (step2 (f 0 0 (Succ 0)) 0 (Succ (Succ 0))))

(def-lvl M)
(let ((erased plm)) (prove-predates L M))
(let ((erased pkm)) (prove-predates K M))

(def-fns M $ (many thrice : (many (Nat) x) -> (many (Nat) y))
  (def-fns L
    ((many inner-via : -> (many (Fn L (many (Nat) a) (erased (Nat) j) (subterm erased (Succ j) is k) -> (many (Nat) b)) r))
      inner1)
    ((many inner0 at inc : (many (Nat) a) (subterm erased (Nat) _k) -> (many (Nat) b))
      (delegate (inc (predates pkl) a)))
    ((many inner1 at inner0 : (many (Nat) a) (erased (Nat) j) (subterm erased (Succ j) is k) -> (many (Nat) b))
      (let ((erased p)) (prove-subterm j k))
      (delegate (inner0 a (subterm p) j))))
  (let ((many g)) (inner-via (predates plm)))
  (let ((many y1)) (notail $ g (predates plm) x 0 (Succ 0)))
  (let ((many y2)) (notail $ inner1 (predates plm) y1 0 (Succ 0)))
  (tail $ inc (predates pkm) y2))

(thrice two)
; warns: tests/delegate_sibling.sl:16:20: warning: unnecessary `(predates _)`; drop it
; warns: tests/delegate_sibling.sl:19:24: warning: unnecessary `(subterm _)`; drop it
; warns: tests/delegate_sibling.sl:22:26: warning: unnecessary `(subterm _)`; drop it
; warns: tests/delegate_sibling.sl:36:22: warning: unnecessary `(predates _)`; drop it
; warns: tests/delegate_sibling.sl:39:27: warning: unnecessary `(subterm _)`; drop it
; warns: tests/delegate_sibling.sl:40:30: warning: unnecessary `(predates _)`; drop it
; warns: tests/delegate_sibling.sl:41:32: warning: unnecessary `(predates _)`; drop it
; warns: tests/delegate_sibling.sl:42:37: warning: unnecessary `(predates _)`; drop it
; warns: tests/delegate_sibling.sl:43:15: warning: unnecessary `(predates _)`; drop it
