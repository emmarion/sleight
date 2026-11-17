(def-fns _ $ (many even : (subterm many (Nat) n) -> (many (Bool) b))
  (let-match many n (Succ m) ((Zero) (BTrue)))
  (let-match many m (Succ k) ((Zero) (BFalse)))
  (tail $ even k))
(def-fns _ $ (many toy-compile : (many (String) src) -> (many (Bool) accepts))
  (let ((many n) (erased _)) (str-length src))
  (even n))
(def-fns _ $ (many diag-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let-match many here (MkPos file _ _) (else (macro-fail mw here "no position")))
  (let ((unique mw1) (many r)) (read-file mw here file))
  (let-match many r (Ok _ text) ((Fail _ m) (macro-fail mw1 here m)))
  (match many (toy-compile text) _
    ((BTrue) (macro-fail mw1 here "toy-compile accepts this source, so it is rejected"))
    ((BFalse) (values mw1 $ Nil _))))
(let ((many diag)) (MkMacro _ diag-fn))
(def-fns _ $ (many run-q : -> (many (Bool) b))
  (toy-compile "(def-fns _ $ (many even : (subterm many (Nat) n) -> (many (Bool) b))
  (let-match many n (Succ m) ((Zero) (BTrue)))
  (let-match many m (Succ k) ((Zero) (BFalse)))
  (tail $ even k))
(def-fns _ $ (many toy-compile : (many (String) src) -> (many (Bool) accepts))
  (let ((many n) (erased _)) (str-length src))
  (even n))
(def-fns _ $ (many diag-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let-match many here (MkPos file _ _) (else (macro-fail mw here \"no position\")))
  (let ((unique mw1) (many r)) (read-file mw here file))
  (let-match many r (Ok _ text) ((Fail _ m) (macro-fail mw1 here m)))
  (match many (toy-compile text) _
    ((BTrue) (macro-fail mw1 here \"toy-compile accepts this source, so it is rejected\"))
    ((BFalse) (values mw1 $ Nil _))))
(let ((many diag)) (MkMacro _ diag-fn))
(diag)
\"accepted, though toy-compile rejects this source\"
;
"))
run-q
