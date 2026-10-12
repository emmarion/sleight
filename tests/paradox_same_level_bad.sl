; error: same-level call to `f` decreases no subterm argument
(def-adts $ (Absurd : -> Type) enum)
(def-lvl L)
(def-adts $ (Packed : -> Type)
  enum
  (many Pack : (many (Fn L (many (Packed) q) -> (many (Absurd) n)) f) -> (Packed)))
(def-fns L $ (many g : (many (Packed) q) -> (many (Absurd) n))
  (let-match many q (Pack f))
  (f q))
