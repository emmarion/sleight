; needs: list
; expect: 2
; Subterm recursion through an erased argument (section 12).

(def-adts
  ((Sing : ((Nat) n) -> Type)
    enum
    (many SZero : -> (Sing (Zero)))
    (many SSucc : (erased (Nat) m) (many (Sing m) s) -> (Sing (Succ m)))))

(def-lvl X)
(def-fns X $ (many twice : (subterm erased (Nat) n) (many (Sing n) s) -> (many (Nat) r))
  (let-match many s (SSucc k t) ((SZero) (Zero)))
  (let ((erased p)) (prove-subterm k n))
  (Succ (Succ (notail $ twice (subterm p) k t))))

(twice (Succ (Zero)) (SSucc (Zero) (SZero)))
; warns: tests/erased_subterm.sl:15:31: warning: unnecessary `(subterm _)`; drop it
