; expect: (MkPair _ _ 0 7)
(def-fns _ $ (many monus : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (let-match many (lt-dec a b) (No _ _ _ _ le-q) ((Yes _ _ _ _ _) 0))
  (let ((erased q)) (le-lt-succ _ _ le-q))
  (let ((many c) (erased _)) (sub a b q))
  c)

(MkPair _ _ (monus 3 10) (monus 10 3))
