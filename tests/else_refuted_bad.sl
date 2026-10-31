; error: `else` covers no constructor
; Every constructor the else would cover is refuted, so there is nothing for it to cover.

(def-adts
  ((ZeroProof : ((Nat) n) -> Type)
    enum
    (many ItIsZero : -> (ZeroProof (Zero)))
    (many IsTwo : (erased (Nat) k) -> (ZeroProof (Succ (Succ k))))))

(def-lvl X)

(def-fns X $ (many g : (many (ZeroProof (Zero)) p) -> (many (Nat) m))
  (match many p (((Nat) r))
    ((ItIsZero) (Zero))
    (else (Succ (Zero)))))

(g (ItIsZero))
