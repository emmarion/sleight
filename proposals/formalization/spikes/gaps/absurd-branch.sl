(def-adts $ (Empty : -> Type)
  enum)

(def-adts $ (Flag : -> Type)
  enum
  (many Up : -> (Flag))
  (many Down : -> (Flag)))

(def-fns _ $ (many pick : (many (Flag) b) (erased (Empty) x) -> (many (Nat) r))
  (match many b _
    ((Up) (Zero))
    (absurd (Down) x)))

(def-fns _ $ (many reach : (erased (Empty) bad) -> (many (Nat) r))
  (pick (Down) bad))

(MkUnit)
