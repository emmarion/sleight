(def-lvl B)

(def-fns B $ (many bind : (erased Type X A) (many (ElabM X) m) (many (Fn K (many X x) -> (many (ElabM A) next)) f) -> (many (ElabM A) r))
  (match many m _
    ((Ret _ x) (f x))
    ((Ask _ s k)
      (def-fns K $ (many k2 : (many (Nat) a) (erased (Runs s a) p) -> (many (ElabM A) next))
        (bind _ _ m f))
      (Ask _ s k2))))

(MkUnit)
