; needs: ../std/macro wide_lib
; expect: (MkPair _ _ (Cons _ 5 $ Cons _ 3 $ Cons _ 6 $ Cons _ 7 $ Cons _ 100 $ Cons _ 0 $ Cons _ 6 $ Cons _ 6 $ Cons _ 7 $ Cons _ 1 $ Cons _ 6 $ Cons _ 6 $ Nil _) $ Cons _ (C245 1 2 3) $ Cons _ (C124 1 2) $ Cons _ (Z1) $ Cons _ (C245 1 2 3) $ Nil _)
; An enum with more than 246 constructors that have fields, past OCaml's block tags: built, matched in
; each mode, embedded and printed.
(def-adts $ (Big : -> Type)
  enum
  (many Z0 : -> (Big))
  (wide ctors Big C 247 3 (Nat))
  (many Z1 : -> (Big)))

(def-fns _ $ (many total : (many (Big) b) -> (many (Nat) r))
  (match many b _
    ((C0 x) x)
    ((C124 x y) (nat-add x y))
    ((C245 x y z) (nat-add x $ nat-add y z))
    ((C246 x) x)
    ((Z1) 100)
    (else 0)))

(def-fns _ $ (many total-unique : (unique (Big) b) -> (many (Nat) r))
  (match unique b _ ((C245 x y z) (nat-add x $ nat-add y z)) (else 0)))

(def-fns _ $ (many twice : (many (Big) b) -> (many (Nat) r))
  (let-match many b (C124 x y) (else 0))
  (match many b _ ((C124 u v) (nat-add (nat-add u v) $ nat-add x y))))

(def-fns _ $ (many last-or-one : (many (Big) b) -> (many (Nat) r))
  (let-match many b (C246 x) (else 1))
  x)

(def-fns _ $ (erased erased-total : (many (Big) b) -> (many (Nat) r))
  (match erased b _ ((C0 x) x) (else 0)))

(let ((many v)) (C245 1 2 3))
(comptime-match many v (C245 a b c))
(let ((many vs)) (Cons _ v $ Cons _ (C124 1 2) $ Cons _ (Z1) $ Cons _ v $ Nil _))

(def-fns _ $ (many main : -> (many (Pair (List (Nat)) (List (Big))) r))
  (let ((erased _)) (erased-total v))
  (MkPair _ _
    (Cons _ (total (C0 5)) $ Cons _ (total (C124 1 2)) $ Cons _ (total v) $ Cons _ (total (C246 7))
      $ Cons _ (total (Z1)) $ Cons _ (total (Z0)) $ Cons _ (total-unique (C245 1 2 3)) $ Cons _ (twice (C124 1 2))
      $ Cons _ (last-or-one (C246 7)) $ Cons _ (last-or-one (C3 9)) $ Cons _ (nat-add a $ nat-add b c)
      $ Cons _ (total-unique (C245 3 2 1)) $ Nil _)
    vs))

main
