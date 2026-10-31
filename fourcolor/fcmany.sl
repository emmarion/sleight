(def-adts $ (FourColorM : -> Type)
  enum
  (many MkFourColorM : (erased (Level) L)
      (many (Fn L (many (List (Edge)) es) (erased (Drawing es) drawn) ->
          (many (List (Paint)) ks) (erased (Proper ks es) proper)) thm)
      -> (FourColorM)))

(goal many (FourColorM))
