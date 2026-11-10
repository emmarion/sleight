; After a run-position `let-match` on a tainted scrutinee, what the elaborator reads of the run-position facts
; is the table as it stood before it. `T` is forced to `(Nat)` and then `K` to `(Level)`, and neither fact is
; read: `settled-eq` still tells `T` from `(Nat)`, `unary` still expands, and `w`, whose type `K` would be
; erased by kind, draws no warning for being declared `many`. An entry bound after the fact is tainted.
(let ((erased NatT)) (Nat))
(def-fns _ $ (many kind-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let-match many args (Cons _ a _) ((Nil _) (values mw (Nil _))))
  (let-match many a (RawSymbol _ s) (else (values mw (Nil _))))
  (let ((unique mw1) (many r)) (resolve mw s))
  (let ((unique mw2) (many t)) $ match many r (((MacroWorld) _ at mw1) ((String) _))
    ((RSettled _ _ _ h)
      (let ((unique mw3) (many e)) (settled-eq _ _ _ _ _ _ mw1 (settled-type _ _ _ h) (settled-of erased NatT)))
      (values mw3 $ match many e (((String) _)) ((ESome _ _) "a Nat") ((ENone _) "not a Nat")))
    ((RSettledSorry) (values mw1 "tainted"))
    (else (values mw1 "not settled")))
  (let ((unique mw3) (many o)) (intern-string mw2 t))
  (values mw3 $ Cons _ (RawList here $ Cons _ (RawSettled here _ _ _ (settled-of many compile-warn)) $ Cons _ (RawSettled here _ _ _ o) $ Nil _) $ Nil _))
(let ((many kind)) (MkMacro _ kind-fn))
(def-fns _ $ (many conv : (erased Type A) (many A a) -> (erased Type T) (many T v))
  (values A a))
(let ((erased T) (many v)) (conv (String) "abc"))
(let ((erased K) (many _u)) (conv (Nat) 1))
(kind v)
(let ((erased e)) (sorry (((Eq Type T (Nat)) q))))
(let-match erased e (Refl _ _))
(kind v)
(let ((erased e2)) (sorry (((Eq Type K (Level)) q))))
(let-match erased e2 (Refl _ _))
(def-fns _ $ (many id-k : (many K w) -> (many K r))
  w)
(unary 5 3)
(let ((erased 5 is _five)) (Succ (Succ 3)))
(let ((many five)) 5)
(kind five)
7
; expect: sorry
; warns: tests/sorry_frozen.sl:24:1: warning: not a Nat
; warns: tests/sorry_frozen.sl:24:1: note: in the expansion of `kind` here
; warns: tests/sorry_frozen.sl:27:1: warning: not a Nat
; warns: tests/sorry_frozen.sl:27:1: note: in the expansion of `kind` here
; warns: tests/sorry_frozen.sl:35:1: warning: tainted
; warns: tests/sorry_frozen.sl:35:1: note: in the expansion of `kind` here
; warns: tests/sorry_frozen.sl:25:19: warning: this unit uses `sorry` 2 times, first here; nothing that depends on it runs
