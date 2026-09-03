; expect: <function probe>
; ASSUMPTIONS 73: a constructor's index mentions its own Fn binder where the scrutinee's has a closed variable, so the branch is refuted.

(def-lvl L)
(def-adts
  (U : -> Type enum (many MkU : -> (U)))
  (Tag : (Type A) -> Type
    enum
    (many MkTag : -> (Tag (Fn L (many (Nat) x) -> (many x is y)))))
  (TagU : (Type A) -> Type
    enum
    (many MkTagU : -> (TagU (Fn L (many (U) x) -> (many x is y))))))
(def-lvl M)
(def-fns M
  (many probe : (erased (Nat) k)
      (many (Tag (Fn L (many (Nat) x) -> (many k is y))) t) -> (many (Nat) r)
    (match many t (((Nat) r))
      (absurd MkTag)))
  (many probe-u : (erased (U) k)
      (many (TagU (Fn L (many (U) x) -> (many k is y))) t) -> (many (Nat) r)
    (match many t (((Nat) r))
      (absurd MkTagU))))

probe
