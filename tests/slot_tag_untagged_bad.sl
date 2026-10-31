; error: `slot-tag`: `Mixed` is neither tagged nor hollow, so the word of `Plain` is unspecified
(def-adts $ (Mixed : -> Type) union
  (many Plain : -> (Mixed))
  (many Holds : (many (Nat) n) -> (Mixed)))
(def-fns _ $ (erased f : (erased (Mixed) m) ->)
  (match erased m ()
    ((Plain) (slot-tag m) (values))
    ((Holds n) (values))))
(Zero)
