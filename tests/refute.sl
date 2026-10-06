; expect: (Cons _ 0 $ Nil _)

(def-lvl X)

(def-fns X $ (many absurd lt-zero-empty : (erased (Nat) a) (many (Lt a (Zero)) p) -> (many (Nat) n))
  (match erased p _))

(def-fns X $ (many absurd lt-zero-value : (erased (Nat) a) (many (Lt a (Zero)) p) -> (many (Nat) n))
  p)

(def-fns X $ (many absurd lt-one-nested : (erased (Nat) a) (many (Lt (Succ a) (Succ (Zero))) p) -> (many (Nat) n))
  (match erased p _
    (absurd LtZ)
    (absurd (LtS x y q) (match erased q _ (absurd LtZ) (absurd LtS)))))

(def-fns X $ (many absurd lt-one-let-match : (erased (Nat) a) (many (Lt (Succ a) (Succ (Zero))) p) -> (many (Nat) n))
  (let-match erased p (LtS x y q))
  q)

(def-fns X $ (many absurd lt-one-annotated : (erased (Nat) a) (many (Lt (Succ a) (Succ (Zero))) p) -> (many (Nat) n))
  (match erased p (((Lt a (Zero)) r))
    (absurd LtZ)
    ((LtS x y q) q)))

(def-fns X $ (many absurd held : (erased (TyCtor -> Type) T)
    (erased (ValCtor -> (T)) C)
    (erased (ValCtor -> (T)) D)
    (erased (Matchable enum T (many C) (many D)) m)
    (erased (Eq (T) (C) (D)) p) -> (many (Nat) n))
  (match erased p _ (absurd (Refl A x) (open-absurd m _))))

(def-fns X $ (many sub1 : (many (Nat) a) (many (Nat) b) (erased (Lt b (Succ a)) le) -> (many (Nat) c))
  (let-match many b (Succ b1)
    ((Zero) a))
  (match many a _
    (absurd (Zero) (let-match erased le (LtS x y l1)) l1)
    ((Succ a1) a1)))

(Cons (Nat) (sub1 (Succ (Zero)) (Succ (Zero)) (LtS (Zero) (Succ (Zero)) (LtZ (Zero)))) $ Nil (Nat))
