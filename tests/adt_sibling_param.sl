; expect: (Succ (Zero))
; A later type in a def-adts block may take an earlier sibling as a parameter: each header is bound before the next is read.

(def-adts
  (Box : -> Type
    enum
    (many MkBox : (many (Nat) n) -> (Box)))
  (Tagged : ((Box) b) -> Type
    enum
    (many MkTagged : (erased (Box) b) -> (Tagged b))))

(let (many b) (MkBox (Succ (Zero))))
(let (many t) (MkTagged b))
(match many b (((Nat) r))
  ((MkBox n) n))
