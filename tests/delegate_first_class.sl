; expect: 1
; A Delegate travels through a parameter whose function types are abstract, where no Fn or UniqueFn
; former is there to read a side off, and the Coercible is drawn from it at the far end.
(def-fns _ $ (erased relay : (erased (Sharing) sg) (erased Type G) (erased G g)
    (erased (Sharing) sf) (erased Type F) (erased F f)
    (erased (Delegate sg G g sf F f) dp) ->
    (erased (Coercible sg G g sf F f) c))
  (coercible-of dp))

(def-fns _ $ (many id : (many (Nat) x) -> (many (Nat) r)) x)
(def-unique _ $ (unique d at id : (many (Nat) x) -> (many (Nat) r)) (delegate (id x)))
(let ((erased c)) (relay _ _ d _ _ id (delegate-of d)))
(let ((many f)) (coerce d c))
(f (Succ (Zero)))
