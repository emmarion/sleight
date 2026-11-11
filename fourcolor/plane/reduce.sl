(def-adts $ (Rounding : ((Level) M) ((List (REdge M)) es) -> Type)
  enum
  (many MkRounding : (erased (Level) M) (erased (List (REdge M)) es) (erased (List (Edge)) ns) (erased (List (RN M)) xs)
      (erased (Ends M es ns xs) en) (erased (Coh M xs) coh) (erased (Drawing ns) drawn)
      -> (Rounding M es)))

(def-fns _ $ (erased four-color-r-of : (erased (FourColor) h) (erased (Level) G)
    (erased (Fn G (erased (Level) M N) -> (erased (Level) L)
        (erased (Fn L (erased (List (REdge M)) es) (erased (RDrawing M N es) drawn) -> (erased (Rounding M es) r)) round)) rounds)
    -> (erased (FourColorR) r))
  (let-match erased h (MkFourColor _ t))
  (def-lvl K)
  (def-fns K $ (erased thms : (erased (Level) M N) -> (erased (Level) L)
      (erased (Fn L (erased (List (REdge M)) es) (erased (RDrawing M N es) drawn) ->
          (erased (List (RPaint M)) ks) (erased (RProper M ks es) proper)) thm))
    (let ((erased L1) (erased round)) (rounds M N))
    (def-lvl L)
    (def-fns L $ (erased thm : (erased (List (REdge M)) es) (erased (RDrawing M N es) drawn) ->
        (erased (List (RPaint M)) ks) (erased (RProper M ks es) proper))
      (let-match erased (round es drawn) (MkRounding _ _ ns xs en coh dn))
      (let ((erased ks) (erased pr)) (t ns dn))
      (pullback M es ns xs en coh ks pr))
    (values L thm))
  (MkFourColorR K thms))
