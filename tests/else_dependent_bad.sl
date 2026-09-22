; error: type mismatch
; An else learns nothing about the scrutinee, so its body is checked against the unrefined motive.

(def-adts
  ((Vec : (Type A) ((Nat) n) -> Type)
    enum
    (many VNil : (erased Type A) -> (Vec A (Zero)))
    (many VCons : (erased Type A) (erased (Nat) k) (many A hd) (many (Vec A k) tl) -> (Vec A (Succ k)))))

(def-lvl X)

(def-fns X $ (many same : (erased (Nat) n) (many (Vec (Nat) n) v) -> (many (Vec (Nat) n) w))
  (match many v (((Vec (Nat) n) r))
    ((VCons a k hd tl) v)
    (else (VNil (Nat)))))

(same (Zero) (VNil (Nat)))
