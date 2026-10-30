; The four colour theorem as a program: from the edges of a drawing, a proper four-colouring of its points. The
; drawing's certificate and the colouring's properness are erased. Load after defs.sl.
(def-adts $ (FourColorM : -> Type)
  enum
  (many MkFourColorM : (erased (Level) L)
      (many (Fn L (many (List (Edge)) es) (erased (Drawing es) drawn) ->
          (many (List (Paint)) ks) (erased (Proper ks es) proper)) thm)
      -> (FourColorM)))

(goal many (FourColorM))
