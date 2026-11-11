(def-adts $ (Mem : ((List (Ty)) g) ((Ty) a) -> Type)
  enum
  (many Here : (erased (List (Ty)) g) (erased (Ty) a) -> (Mem (Cons (Ty) a g) a))
  (many There : (erased (List (Ty)) g) (erased (Ty) a b) (many (Mem g a) m) -> (Mem (Cons (Ty) b g) a)))

(def-adts $ (Term : ((List (Ty)) g) ((Ty) a) -> Type)
  enum
  (many Var : (erased (List (Ty)) g) (erased (Ty) a) (many (Mem g a) m) -> (Term g a))
  (many Lam : (erased (List (Ty)) g) (erased (Ty) a b) (many (Term (Cons (Ty) a g) b) body) -> (Term g (Arr a b)))
  (many App : (erased (List (Ty)) g) (erased (Ty) a b) (many (Term g (Arr a b)) fun) (many (Term g a) arg) -> (Term g b)))

(def-adts $ (Insert : ((Ty) b) ((List (Ty)) g) ((List (Ty)) h) -> Type)
  enum
  (many InsertHere : (erased (Ty) b) (erased (List (Ty)) g) -> (Insert b g (Cons (Ty) b g)))
  (many InsertThere : (erased (Ty) b c) (erased (List (Ty)) g h) (erased (Insert b g h) i) -> (Insert b (Cons (Ty) c g) (Cons (Ty) c h))))

(def-adts $ (Hole : ((Ty) b) ((List (Ty)) g h) ((Insert b g h) i) ((Mem h b) m) -> Type)
  enum
  (many HoleHere : (erased (Ty) b) (erased (List (Ty)) g) -> (Hole b g (Cons (Ty) b g) (InsertHere b g) (Here g b)))
  (many HoleThere : (erased (Ty) b c) (erased (List (Ty)) g h) (erased (Insert b g h) i) (erased (Mem h b) m) (erased (Hole b g h i m) p)
     -> (Hole b (Cons (Ty) c g) (Cons (Ty) c h) (InsertThere b c g h i) (There h b c m))))

(def-adts $ (VarShift : ((Ty) b) ((List (Ty)) g h) ((Insert b g h) i) ((Ty) a) ((Mem g a) m) ((Mem h a) n) -> Type)
  enum
  (many VarShiftHere : (erased (Ty) b) (erased (List (Ty)) g) (erased (Ty) a) (erased (Mem g a) m)
     -> (VarShift b g (Cons (Ty) b g) (InsertHere b g) a m (There g a b m)))
  (many VarShiftTop : (erased (Ty) b c) (erased (List (Ty)) g h) (erased (Insert b g h) i)
     -> (VarShift b (Cons (Ty) c g) (Cons (Ty) c h) (InsertThere b c g h i) c (Here g c) (Here h c)))
  (many VarShiftDown : (erased (Ty) b c) (erased (List (Ty)) g h) (erased (Insert b g h) i) (erased (Ty) a) (erased (Mem g a) m) (erased (Mem h a) n)
     (erased (VarShift b g h i a m n) p)
     -> (VarShift b (Cons (Ty) c g) (Cons (Ty) c h) (InsertThere b c g h i) a (There g a c m) (There h a c n))))

(def-adts $ (Weaken : ((Ty) b) ((List (Ty)) g h) ((Insert b g h) i) ((Ty) a) ((Term g a) t) ((Term h a) u) -> Type)
  enum
  (many WeakenVar : (erased (Ty) b) (erased (List (Ty)) g h) (erased (Insert b g h) i) (erased (Ty) a) (erased (Mem g a) m) (erased (Mem h a) n)
     (erased (VarShift b g h i a m n) p)
     -> (Weaken b g h i a (Var g a m) (Var h a n)))
  (many WeakenLam : (erased (Ty) b) (erased (List (Ty)) g h) (erased (Insert b g h) i) (erased (Ty) c a)
     (erased (Term (Cons (Ty) c g) a) t) (erased (Term (Cons (Ty) c h) a) u) (erased (Weaken b (Cons (Ty) c g) (Cons (Ty) c h) (InsertThere b c g h i) a t u) p)
     -> (Weaken b g h i (Arr c a) (Lam g c a t) (Lam h c a u)))
  (many WeakenApp : (erased (Ty) b) (erased (List (Ty)) g h) (erased (Insert b g h) i) (erased (Ty) c a)
     (erased (Term g (Arr c a)) f) (erased (Term h (Arr c a)) f2) (erased (Term g c) x) (erased (Term h c) x2)
     (erased (Weaken b g h i (Arr c a) f f2) p) (erased (Weaken b g h i c x x2) q)
     -> (Weaken b g h i a (App g c a f x) (App h c a f2 x2))))

(def-adts $ (Subst : ((Ty) b) ((List (Ty)) g h) ((Insert b g h) i) ((Term g b) u) ((Ty) a) ((Term h a) t) ((Term g a) r) -> Type)
  enum
  (many SubstHit : (erased (Ty) b) (erased (List (Ty)) g h) (erased (Insert b g h) i) (erased (Term g b) u) (erased (Mem h b) m)
     (erased (Hole b g h i m) p)
     -> (Subst b g h i u b (Var h b m) u))
  (many SubstMiss : (erased (Ty) b) (erased (List (Ty)) g h) (erased (Insert b g h) i) (erased (Term g b) u) (erased (Ty) a)
     (erased (Mem g a) m) (erased (Mem h a) n) (erased (VarShift b g h i a m n) p)
     -> (Subst b g h i u a (Var h a n) (Var g a m)))
  (many SubstLam : (erased (Ty) b) (erased (List (Ty)) g h) (erased (Insert b g h) i) (erased (Term g b) u) (erased (Ty) c a)
     (erased (Term (Cons (Ty) c g) b) u1) (erased (Term (Cons (Ty) c h) a) t) (erased (Term (Cons (Ty) c g) a) r)
     (erased (Weaken c g (Cons (Ty) c g) (InsertHere c g) b u u1) w)
     (erased (Subst b (Cons (Ty) c g) (Cons (Ty) c h) (InsertThere b c g h i) u1 a t r) p)
     -> (Subst b g h i u (Arr c a) (Lam h c a t) (Lam g c a r)))
  (many SubstApp : (erased (Ty) b) (erased (List (Ty)) g h) (erased (Insert b g h) i) (erased (Term g b) u) (erased (Ty) c a)
     (erased (Term h (Arr c a)) f) (erased (Term g (Arr c a)) f2) (erased (Term h c) x) (erased (Term g c) x2)
     (erased (Subst b g h i u (Arr c a) f f2) p) (erased (Subst b g h i u c x x2) q)
     -> (Subst b g h i u a (App h c a f x) (App g c a f2 x2))))

(def-adts $ (OneStep : ((List (Ty)) g) ((Ty) a) ((Term g a) t) ((Term g a) u) -> Type)
  enum
  (many StepBeta : (erased (List (Ty)) g) (erased (Ty) a b) (erased (Term (Cons (Ty) a g) b) body) (erased (Term g a) u) (erased (Term g b) r)
     (erased (Subst a g (Cons (Ty) a g) (InsertHere a g) u b body r) p)
     -> (OneStep g b (App g a b (Lam g a b body) u) r))
  (many StepLam : (erased (List (Ty)) g) (erased (Ty) a b) (erased (Term (Cons (Ty) a g) b) t u)
     (erased (OneStep (Cons (Ty) a g) b t u) p)
     -> (OneStep g (Arr a b) (Lam g a b t) (Lam g a b u)))
  (many StepFun : (erased (List (Ty)) g) (erased (Ty) a b) (erased (Term g (Arr a b)) f f2) (erased (Term g a) x)
     (erased (OneStep g (Arr a b) f f2) p)
     -> (OneStep g b (App g a b f x) (App g a b f2 x)))
  (many StepArg : (erased (List (Ty)) g) (erased (Ty) a b) (erased (Term g (Arr a b)) f) (erased (Term g a) x x2)
     (erased (OneStep g a x x2) p)
     -> (OneStep g b (App g a b f x) (App g a b f x2))))

(def-adts $ (Reduction : ((List (Ty)) g) ((Ty) a) ((Nat) k) ((Term g a) t) ((Term g a) u) -> Type)
  enum
  (many Done : (erased (List (Ty)) g) (erased (Ty) a) (erased (Term g a) t) -> (Reduction g a (Zero) t t))
  (many Then : (erased (List (Ty)) g) (erased (Ty) a) (erased (Nat) k) (erased (Term g a) t v u)
     (erased (OneStep g a t v) p) (erased (Reduction g a k v u) q)
     -> (Reduction g a (Succ k) t u)))

(def-adts $ (Bounded : ((List (Ty)) g) ((Ty) a) ((Term g a) t) ((Nat) n) -> Type)
  enum
  (many MkBounded : (erased (List (Ty)) g) (erased (Ty) a) (erased (Term g a) t) (erased (Nat) n) (erased (Level) L)
     (erased (Fn L (erased (Nat) k) (erased (Term g a) u) (erased (Reduction g a k t u) r) -> (erased (NatLe k n) le)) bound)
     -> (Bounded g a t n)))

(def-adts $ (BoundedReductions : -> Type)
  enum
  (many MkBoundedReductions : (erased (Level) L)
     (erased (Fn L (erased (List (Ty)) g) (erased (Ty) a) (erased (Term g a) t) -> (erased (Nat) n) (erased (Bounded g a t n) b)) sn)
     -> (BoundedReductions)))

(goal erased (BoundedReductions))
