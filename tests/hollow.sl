; expect: (Cons _ (MkBox $ MkTok _) $ Cons _ (MkBox $ MkTok _) $ Cons _ (MkBox $ MkTok _) $ Cons _ (MkBox $ MkTok _) $ Nil _)
(def-adts $ (Tok : -> Type) enum
  (many MkTok : (erased (Nat) n) -> (Tok)))

(def-adts $ (Mark : -> Type) union
  (many MA : -> (Mark))
  (many MB : (erased (Nat) n) -> (Mark)))

(def-adts $ (Box : -> Type) enum
  (many MkBox : (many (Tok) t) -> (Box)))

(def-fns _ $ (many at tok : (erased (Nat) n) -> (many (Tok) t at vacant-slot))
  (MkTok n))

(def-fns _ $ (many at retok : (many (Mark) m) -> (many (Tok) t at vacant-slot))
  (match many m (at (((Tok) t at vacant-slot)))
    ((MA) (MkTok 0))
    ((MB n) (MkTok n))))

(def-fns _ $ (many built : (erased (Nat) n) -> (many (Tok) t at vacant-slot))
  (let ((unique c)) (cell-alloc MkTok))
  (share (c n)))

(def-fns _ $ (many boxed : (erased (Nat) n) -> (many (Box) b))
  (let ((unique c)) (cell-alloc MkBox))
  (let ((many t)) (MkTok n))
  (share (at unique (c t))))

(Cons _ (boxed 1) $ Cons _ (MkBox $ built 2) $ Cons _ (MkBox $ tok 3) $ Cons _ (MkBox $ retok $ MB 4) $ Nil _)
