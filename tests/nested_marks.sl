; expect: 4
; tail and delegate inside functions a factory produces: each nested function's marks are judged against its
; own tail positions, not the factory's.

(def-lvl F)
(def-fns F $ (many twice : (many (Nat) n) -> (many (Nat) m)) (Succ (Succ n)))

(def-lvl G)
(def-fns G $ (many make : -> (erased (Level) L)
    (many (Fn L (many (Nat) k) -> (many (Nat) r)) t)
    (many (Fn L (many (Nat) k) -> (many (Nat) r)) d))
  (def-lvl L)
  (let ((erased fl)) (prove-predates F L))
  (def-fns L
    ((many t : (many (Nat) k) -> (many (Nat) r)) (tail (twice (predates fl) k)))
    ((many d at twice : (many (Nat) k) -> (many (Nat) r)) (delegate (twice (predates fl) k))))
  (values L t d))

(let ((erased L) (many t) (many d)) (make))
(t (d (Zero)))
; warns: tests/nested_marks.sl:15:63: warning: unnecessary `(predates _)`; drop it
; warns: tests/nested_marks.sl:16:76: warning: unnecessary `(predates _)`; drop it
