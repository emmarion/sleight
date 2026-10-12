; a ValCtor whose return is headed by a type constructor from an enclosing former
(def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
(def-adts (Box ((Type A)) (MkBox ((Type A) (A x)) (Box A))))
(def-lvl L)
(def-fns L (mk (((TyCtor ((Type A))) F) ((ValCtor ((Type B) (B y)) (F B)) c) ((Nat) n)) (((F (Nat)) r))
  (c (Nat) n)))
(mk Box MkBox (Succ (Zero)))
