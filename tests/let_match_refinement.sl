; expect: (Cons _ 5 $ Cons _ 3 $ Nil _)
; Fields and forced facts bind outward, including constructor subterms.
(def-adts $ (LMVec : (Type A) ((Nat) n) -> Type) enum
  (many LMNil : (erased Type A) -> (LMVec A (Zero)))
  (many LMCons : (erased Type A) (erased (Nat) n) (many A x)
    (many (LMVec A n) rest) -> (LMVec A (Succ n))))
(def-fns _ $ (many lm-head : (erased Type A) (erased (Nat) n)
    (many (LMVec A (Succ n)) xs) -> (many A x))
  (let-match many xs (LMCons B k x rest))
  x)
(def-fns _ $ (erased lm-lt : (erased (Nat) n m) (erased (Lt (Succ n) (Succ m)) p) ->
    (erased (Lt n m) q))
  (let-match erased p (LtS a b q))
  q)
(def-fns _ $ (many lm-length : (subterm many (List (Nat)) xs) -> (many (Nat) n))
  (let-match many xs (Cons a x rest)
    ((Nil a) (Zero)))
  (let-match many xs (Cons b y ys))
  (Succ (notail $ lm-length ys)))
(def-fns _ $ (many refinement-main : -> (many (Nat) n))
  (let ((erased p)) (lm-lt (Zero) (Succ (Zero)) (LtS (Zero) (Succ (Zero)) (LtZ (Zero)))))
  (lm-head (Nat) (Zero) (LMCons (Nat) (Zero) 5 (LMNil (Nat)))))
(def-fns _ $ (many length-main : -> (many (Nat) n))
  (lm-length (Cons _ 1 (Cons _ 2 (Cons _ 3 (Nil _))))))

(def-fns _ $ (many refinement-tests : -> (many (List (Nat)) results))
  (Cons _ (refinement-main) (Cons _ (length-main) (Nil _))))
refinement-tests
