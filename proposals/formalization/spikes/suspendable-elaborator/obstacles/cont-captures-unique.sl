(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (Nat) notes) -> (Box)))

(def-adts $ (UM : -> Type)
  enum
  (many URet : (many (Nat) v) -> (UM))
  (many UAsk : (many (Nat) s) (many (Fn K (many (Nat) a) -> (unique (Box) b2) (many (UM) next)) k) -> (UM)))

(def-fns W $ (many walk : (unique (Box) b) (many (Nat) s) -> (many (UM) m))
  (def-fns K $ (many answered : (many (Nat) a) -> (unique (Box) b2) (many (UM) next))
    (values b (URet a)))
  (UAsk s answered))

(MkUnit)
