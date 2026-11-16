(def-fns _ $ (many xelab : (subterm many (XTree) t) (many (List (XEntry)) log) -> (many (XOutcome) r))
  (match many t _
    ((XGen) (XDone 1 log))
    ((XNode l r)
      (let-match many (notail $ xelab l log) (XDone a log1) (else o o))
      (let-match many (notail $ xelab r log1) (XDone b log2) (else o o))
      (XDone (nat-add a b) log2))
    ((XExpand s)
      (let-match many log (Cons _ e rest) ((Nil _) (XNeed s)))
      (let-match many e (MkXEntry _ out))
      (tail $ xelab out rest))))

(MkUnit)
