; A literal's entries are outside every scope, so a tainted scope does not taint them: `42` is first met in the
; branch of a match on a tainted scrutinee, through a macro, and is an untainted `42` afterwards.
(def-fns _ $ (many lit-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many h)) (intern-nat mw (nat-add 40 2)))
  (values mw1 $ Cons _ (RawSettled here _ _ _ h) $ Nil _))
(let ((many lit)) (MkMacro _ lit-fn))
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) m))
  (let ((many t)) (sorry (((Nat) x))))
  (let ((many _u)) (match many t (((Nat) r)) ((Zero) (lit)) ((Succ _p) n)))
  n)
(f 1)
;! file "sorry/literal.sl"
42
; expect: 1
; expect: 42
; warns: tests/sorry_literal.sl:9:19: warning: this unit uses `sorry` once, here; nothing that depends on it runs
