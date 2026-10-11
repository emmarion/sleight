; expect: (MkPair _ _ 7 8)
(def-fns _ $ (many pass : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw args))
(let ((many splice)) (MkMacro _ pass))
(def-fns _ $ (many sum : (splice (many (Nat) a) (many (Nat) b)) -> (many (Nat) c))
  (let ((many s) (erased p)) (splice (let ((erased q)) (splice (Refl (Nat) a))) (add a b)))
  (match many a _
    ((Zero) (splice b))
    ((Succ _) (splice (let ((many t)) s) t))))
(def-fns _ $ (many seven : (many (Nat) n) -> (many (Nat) m)) 8)
(def-fns _ $ (many pick : (many (Fn (level-of seven) (many (Nat) n) -> (many (Nat) m)) splice) -> (many (Nat) r)) (splice 7))
(MkPair _ _ (sum 3 4) (pick seven))
; warns: tests/macro_body.sl:12:27: warning: declaration of `splice` shadows a previous binder
; warns: tests/macro_body.sl:5:7: note: shadowed binder is here
