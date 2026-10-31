(def-adts $ (Pc : -> Type)
  enum
  (many PcPre : (many (List (Sub)) pre) -> (Pc))
  (many PcNil : -> (Pc)))

(def-adts $ (Hc : -> Type)
  enum
  (many HC1 : (many (Nat) i) (many (Z) b) -> (Hc))
  (many HC2 : (many (Nat) i j) (many (Z) b) -> (Hc)))

(def-fns _ $ (many iter-rot : (subterm many (Nat) k) (many (Nat) n) (many (List (Sub)) p) -> (many (List (Sub)) q))
  (let-match many k (Succ k1) ((Zero) p))
  (tail $ iter-rot k1 n (rot _ n p)))

(def-fns _ $ (many symmetrize : (subterm many (List (List (Sub))) rs) -> (many (List (List (Sub))) r))
  (let-match many rs (Cons _ p rest) ((Nil _) rs))
  (let ((many p1)) (iter-rot 5 (monus (size _ p) 1) (mirror-part p)))
  (let ((many psr)) (Cons _ p $ notail $ symmetrize rest))
  (bif _ (rel-sub (cmp-part p p1)) psr (Cons _ p1 psr)))

(def-fns _ $ (many incr-nth : (many (List (Nat)) v) (subterm many (Nat) i) -> (many (List (Nat)) w))
  (match many v _
    ((Nil _) (match many i _ ((Zero) (Cons _ 1 $ Nil _)) ((Succ i1) (Cons _ 0 $ notail $ incr-nth (Nil _) i1))))
    ((Cons _ x v1) (match many i _ ((Zero) (Cons _ (Succ x) v1)) ((Succ i1) (Cons _ x $ notail $ incr-nth v1 i1))))))

(def-fns _ $ (many tally : (subterm many (List (Hc)) hc) -> (many (List (Nat)) v))
  (let-match many hc (Cons _ h rest) ((Nil _) (Nil _)))
  (let ((many v)) (notail $ tally rest))
  (let-match many h (HC2 i j _) ((HC1 i _) (incr-nth v i)))
  (incr-nth (incr-nth v i) j))

(def-fns _ $ (many nth-nat : (subterm many (Nat) i) (many (List (Nat)) xs) -> (many (Nat) x))
  (let-match many xs (Cons _ x rest) ((Nil _) 0))
  (let-match many i (Succ i1) ((Zero) x))
  (tail $ nth-nat i1 rest))
