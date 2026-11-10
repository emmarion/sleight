; `resolve` answers `RSettledSorry` for a tainted `Settled` entry, and makes no handle on it; a tainted
; `Hypothetical` entry answers `RHypothetical`, as it would untainted, and an untainted entry of the same unit
; resolves as it would without the `sorry`.
(def-fns _ $ (many peek-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let-match many args (Cons _ a _) ((Nil _) (values mw (Nil _))))
  (let-match many a (RawSymbol _ s) (else (values mw (Nil _))))
  (let ((unique mw1) (many r)) (resolve mw s))
  (let ((many t)) $ match many r (((String) _))
    ((RSettled _ _ _ _) "settled")
    ((RHypothetical) "hypothetical")
    ((RUnbound) "unbound")
    ((RSettledSorry) "tainted"))
  (let ((unique mw2) (many o)) (intern-string mw1 t))
  (values mw2 $ Cons _ (RawSettled here _ _ _ o) $ Nil _))
(let ((many peek)) (MkMacro _ peek-fn))
(let ((many t)) (sorry (((Nat) q))))
(let ((many u)) (Succ t))
(let ((many k)) 5)
(def-fns _ $ (many body : (many (Nat) n) -> (many (String) a) (many (String) b))
  (let ((many m)) (sorry (((Nat) q))))
  (let ((many _j)) (nat-add n m))
  (values (peek m) (peek n)))
(let ((many a) (many b)) (body k))
(MkPair _ _ (MkPair _ _ (peek t) (peek u)) $ MkPair _ _ (MkPair _ _ (peek k) (peek nope)) $ MkPair _ _ a b)
; expect: (MkPair _ _ (MkPair _ _ "tainted" "tainted") $ MkPair _ _ (MkPair _ _ "settled" "unbound") $ MkPair _ _ "hypothetical" "hypothetical")
; warns: tests/sorry_resolve.sl:17:17: warning: this unit uses `sorry` 2 times, first here; nothing that depends on it runs
