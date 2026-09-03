; expect: (Zero)
; Lt a b and Subterm (Nat) a (Nat) b each derive the other as erased functions, so on Nat the subterm
; order is the strict order. lt-sub recurses on b through le-split, which splits Lt a (Succ b1) into
; a = b1 or Lt a b1; sub-lt decides a < b and refutes the other case through loop, whose self-call
; the reflexive proof itself licenses, so the checker accepts Subterm x x as refuting.

(def-adts $ Eq : ((Nat) a) ((Nat) b) -> Type
  enum
  (many Refl : (erased (Nat) x) -> (Eq x x)))

(def-adts $ Or : (Type A) (Type B) -> Type
  enum
  (many Left : (erased Type A) (erased Type B) (erased A x) -> (Or A B))
  (many Right : (erased Type A) (erased Type B) (erased B y) -> (Or A B)))

(def-lvl L)
(let (erased nl) (prove-predates nat-lvl L))

(def-fns L $ erased absurd explode : (erased Type A) (erased (False) f) -> (erased A a)
  f)

(def-fns L $ erased loop : (subterm erased (Nat) x) (erased (Subterm (Nat) x (Nat) x) q) -> (erased (False) f)
  (loop (subterm q) x q))

(def-fns L $ erased le-split : (subterm erased (Nat) b1) (erased (Nat) a) (erased (Lt a (Succ b1)) p) ->
    (erased (Or (Eq a b1) (Lt a b1)) r)
  (match erased p _
    ((LtZ b2)
      (match erased b1 _
        ((Zero) (Left (Eq a b1) (Lt a b1) (Refl a)))
        ((Succ b3) (Right (Eq a b1) (Lt a b1) (LtZ b3)))))
    ((LtS a1 b2 p1)
      (match erased b1 _
        ((Zero) (match erased p1 _ (absurd LtZ) (absurd LtS)))
        ((Succ b3)
          (match erased (le-split (subterm _) b3 a1 p1) _
            ((Left A B e) (match erased e _ ((Refl z) (Left (Eq a b1) (Lt a b1) (Refl a)))))
            ((Right A B l) (Right (Eq a b1) (Lt a b1) (LtS a1 b3 l)))))))))

(def-fns L $ erased lt-sub : (subterm erased (Nat) b) (erased (Nat) a) (erased (Lt a b) p) ->
    (erased (Subterm (Nat) a (Nat) b) q)
  (match erased b _
    ((Zero) (match erased p _ (absurd LtZ) (absurd LtS)))
    ((Succ b1)
      (match erased (le-split (subterm (prove-subterm b1 b)) b1 a p) _
        ((Left A B e) (match erased e _ ((Refl z) (prove-subterm a b))))
        ((Right A B l) (subterm-trans (lt-sub (subterm _) b1 a l) (prove-subterm b1 b)))))))

(def-lvl M)
(let (erased nm) (prove-predates nat-lvl M))
(let (erased lm) (prove-predates L M))

(def-fns M $ erased sub-lt : (erased (Nat) a) (erased (Nat) b) (erased (Subterm (Nat) a (Nat) b) q) ->
    (erased (Lt a b) l)
  (match erased (lt-dec (predates nm) a b) _
    ((Yes x y p) p)
    ((No x y r)
      (match erased (le-split (predates lm) a b r) _
        ((Left A B e)
          (match erased e _
            ((Refl z) (explode (predates lm) (Lt a b) (loop (predates lm) a q)))))
        ((Right A B l)
          (explode (predates lm) (Lt a b)
            (loop (predates lm) a (subterm-trans q (lt-sub (predates lm) a b l)))))))))

(Zero)
