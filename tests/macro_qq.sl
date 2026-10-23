; needs: ../std/macro
(def-macro (pair-of args)
  (let-match many args (Cons _ a rest) ((Nil _) (qq (Nil (Nat)))))
  (qq (Cons (Nat) (~ a) $ Cons (Nat) 7 $ Nil (Nat)) (~@ rest)))

(def-macro (listed args)
  (qq (Cons (Nat) 1 $ Cons (Nat) (~@ args) $ Nil (Nat))))

(def-fns _ $ (many hygiene : (many (Nat) Cons) -> (many (List (Nat)) r))
  (listed Cons))

(def-fns _ $ (many all3 : (many (Bool) a) (many (Bool) b) (many (Bool) c) -> (many (Bool) r))
  (and a b c))

(def-fns _ $ (many any3 : (many (Bool) a) (many (Bool) b) (many (Bool) c) -> (many (Bool) r))
  (or a b c))

(def-fns _ $ (many bools : (many (Bool) t) (many (Bool) f) -> (many (List (Bool)) r))
  (Cons _ (all3 t t f) $ Cons _ (all3 t t t) $ Cons _ (any3 f f f) $ Cons _ (any3 f t f)
    $ Cons _ (and) $ Cons _ (or) $ Cons _ (and f) $ Cons _ (or t f) $ Nil _))

(MkPair _ _ (pair-of 3) $ MkPair _ _ (hygiene 2) $ bools (BTrue) (BFalse))
; expect: (MkPair _ _ (Cons _ 3 $ Cons _ 7 $ Nil _) $ MkPair _ _ (Cons _ 1 $ Cons _ 2 $ Nil _) $ Cons _ (BFalse) $ Cons _ (BTrue) $ Cons _ (BFalse) $ Cons _ (BTrue) $ Cons _ (BTrue) $ Cons _ (BFalse) $ Cons _ (BFalse) $ Cons _ (BTrue) $ Nil _)
; warns: tests/macro_qq.sl:9:30: warning: declaration of `Cons` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
