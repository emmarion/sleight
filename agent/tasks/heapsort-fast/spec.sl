(let ((many spec-s60) (erased spec-s60m)) (mul (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))) ten))
(let-match erased (mul-fn _ _ _ _ spec-s60m sixty-mul) (Refl _ _))
(let ((many spec-s62) (erased spec-s62a)) (add spec-s60 (Succ (Succ (Zero)))))
(let-match erased (add-fn _ _ _ _ spec-s62a sixty-two-add) (Refl _ _))
(let ((many u62m) (erased spec-u62m-pow2) (erased _)) (pow2 spec-s62))
(let-match erased (pow2-fn _ _ _ spec-u62m-pow2 u62-modulus-pow2) (Refl _ _))

(def-adts
  ((Le : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many MkLe : (erased (Nat) a) (erased (Nat) b) (erased (Lt a (Succ b)) p) -> (Le a b))))

(def-adts
  ((AllTo : (Type A) ((TyCtor (A x) (A y) -> Type) R) ((List A) xs) (A m) -> Type)
    enum
    (many AllToNil : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased A m)
        -> (AllTo A R (Nil A) m))
    (many AllToCons : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased A x)
        (erased (List A) xs) (erased A m) (erased (R x m) p) (erased (AllTo A R xs m) rest)
        -> (AllTo A R (Cons A x xs) m))))

(def-adts
  ((Ascending : (Type A) ((TyCtor (A x) (A y) -> Type) R) ((List A) xs) -> Type)
    enum
    (many AscNil : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) -> (Ascending A R (Nil A)))
    (many AscOne : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased A x)
        -> (Ascending A R (Cons A x (Nil A))))
    (many AscCons : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R) (erased A x) (erased A y)
        (erased (List A) rest) (erased (R x y) le) (erased (Ascending A R (Cons A y rest)) a)
        -> (Ascending A R (Cons A x (Cons A y rest))))))

(def-adts
  ((Permutation : (Type A) ((List A) xs) ((List A) ys) -> Type)
    enum
    (many PNil : (erased Type A) -> (Permutation A (Nil A) (Nil A)))
    (many PSkip : (erased Type A) (erased A x) (erased (List A) xs) (erased (List A) ys)
        (erased (Permutation A xs ys) p)
        -> (Permutation A (Cons A x xs) (Cons A x ys)))
    (many PSwap : (erased Type A) (erased A x) (erased A y) (erased (List A) l)
        -> (Permutation A (Cons A x (Cons A y l)) (Cons A y (Cons A x l))))
    (many PTrans : (erased Type A) (erased (List A) xs) (erased (List A) ys) (erased (List A) zs)
        (erased (Permutation A xs ys) p) (erased (Permutation A ys zs) q)
        -> (Permutation A xs zs))))

(def-adts
  ((SortedPerm : (Type A) ((TyCtor (A x) (A y) -> Type) R) ((List A) xs) ((List A) ys) -> Type)
    enum
    (many MkSortedPerm : (erased Type A) (erased (TyCtor (A x) (A y) -> Type) R)
        (erased (List A) xs) (erased (List A) ys)
        (erased (Ascending A R ys) sorted) (erased (Permutation A xs ys) perm)
        -> (SortedPerm A R xs ys))))

(def-adts
  ((Copies : (Type A) ((List A) xs) ((List (Copy A)) cs) -> Type)
    enum
    (many CopiesNil : (erased Type A) -> (Copies A (Nil A) (Nil (Copy A))))
    (many CopiesCons : (erased Type A) (erased A x) (erased (List A) xs) (erased (List (Copy A)) cs)
        (erased (Copies A xs cs) rest) -> (Copies A (Cons A x xs) (Cons (Copy A) (MkCopy A x) cs)))))
