(def-fns _ $ (many deep : (subterm many (Nat) n) -> (many (Nat) r))
  (match many n _ ((Zero) 0) ((Succ k) (Succ $ notail $ deep k))))
(def-fns _ $ (many m-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((many z)) (deep 1000))
  (values mw $ Nil _))
(let ((many m)) (MkMacro _ m-fn))
(m)
(compile-warn "end")
