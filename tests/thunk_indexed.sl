; expect: (VCons (Succ (Zero)) (VNil))
; A final function returning a value of an indexed type: the generated printer keeps an arm for each
; constructor whose return type unifies with the type, the opened objects merged as entering a branch does,
; so VNil is refuted at length one and VCons at length zero, and the fields print through their types at the
; instance.

(def-adts
  (Vec : (Type A) ((Nat) n) -> Type
    enum
    (many VNil : (erased Type A) -> (Vec A (Zero)))
    (many VCons : (erased Type A) (erased (Nat) n) (many A x) (many (Vec A n) rest) -> (Vec A (Succ n)))))

(def-lvl L)

(def-fns L $ many one : -> (many (Vec (Nat) (Succ (Zero))) v)
  (VCons _ _ (Succ (Zero)) (VNil _)))

one
