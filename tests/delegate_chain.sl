; expect: 4
; Delegates chained across blocks, each at a higher level than the one it names: in run position the later
; delegate's value is the first callee's, and inside a body the later block's delegate names an earlier
; block's delegate, both standing for `inc`.

(def-lvl K)
(def-fns K $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))

(def-lvl L)
(let ((erased pkl)) (prove-predates K L))
(def-fns L $ (many inc1 : (many (Nat) n) -> (many (Nat) m)) (delegate (inc (predates pkl) n)))

(def-lvl M)
(let ((erased plm)) (prove-predates L M))
(def-fns M $ (many inc2 : (many (Nat) n) (erased (Nat) note) -> (many (Nat) m)) (delegate (inc1 (predates plm) n)))

(def-lvl N)
(let ((erased pkn)) (prove-predates K N))
(let ((erased pln)) (prove-predates L N))
(let ((erased pmn)) (prove-predates M N))

(def-fns N $ (many add3 : (many (Nat) x) -> (many (Nat) y))
  (def-fns L $ (many bump1 : (many (Nat) n) -> (many (Nat) m)) (delegate (inc (predates pkl) n)))
  (def-fns M $ (many bump2 : (many (Nat) n) -> (many (Nat) m)) (delegate (bump1 (predates plm) n)))
  (let ((many y1)) (notail $ bump2 (predates pmn) x))
  (let ((many y2)) (notail $ inc2 (predates pmn) y1 0))
  (tail $ inc1 (predates pln) y2))

(add3 (inc2 0 0))
; warns: tests/delegate_chain.sl:11:76: warning: unnecessary `(predates _)`; drop it
; warns: tests/delegate_chain.sl:15:97: warning: unnecessary `(predates _)`; drop it
; warns: tests/delegate_chain.sl:23:79: warning: unnecessary `(predates _)`; drop it
; warns: tests/delegate_chain.sl:24:81: warning: unnecessary `(predates _)`; drop it
; warns: tests/delegate_chain.sl:25:36: warning: unnecessary `(predates _)`; drop it
; warns: tests/delegate_chain.sl:26:35: warning: unnecessary `(predates _)`; drop it
; warns: tests/delegate_chain.sl:27:16: warning: unnecessary `(predates _)`; drop it
