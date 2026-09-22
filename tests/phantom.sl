; needs: list
; expect: 0
; A phantom constructor's branch is fully erased and exempt from the match's result erasure.

(def-adts
  ((Opt : -> Type)
    enum
    (many OSome : (many (Nat) n) -> (Opt))
    (erased Ghost : (erased (Nat) n) -> (Opt))))

(def-lvl X)

(def-fns X $ (many get : (many (Opt) o) -> (many (Nat) n))
  (match many o (((Nat) r))
    ((OSome n) n)
    ((Ghost n) n)))

(get (OSome (Zero)))
