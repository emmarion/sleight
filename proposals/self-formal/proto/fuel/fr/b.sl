(def-lvl L)
(def-adts $ (Res : -> Type) enum
  (many RDone : (many (Nat) n) -> (Res))
  (many RAsk : (many (Nat) q) (many (Fn L (many (Nat) a) -> (many (Res) r)) k) -> (Res)))
(def-fns L $ (many bind : (subterm many (Res) r) (many (Fn L (many (Nat) a) -> (many (Res) r)) g) -> (many (Res) o))
  (match many r _
    ((RDone n) (g n))
    ((RAsk q k) (RAsk q k))))
