(def-adts $ (Term : -> Type)
  enum
  (many Var : (many (Nat) i) -> (Term))
  (many Lam : (many (Term) body) -> (Term))
  (many App : (many (Term) fun) (many (Term) arg) -> (Term)))

(def-adts $ (Skip : ((Nat) k) ((Nat) i) ((Nat) j) -> Type)
  enum
  (many SkipZ : (erased (Nat) i) -> (Skip (Zero) i (Succ i)))
  (many SkipLo : (erased (Nat) k) -> (Skip (Succ k) (Zero) (Zero)))
  (many SkipHi : (erased (Nat) k i j) (erased (Skip k i j) p) -> (Skip (Succ k) (Succ i) (Succ j))))

(def-adts $ (Shift : ((Nat) k) ((Term) t) ((Term) u) -> Type)
  enum
  (many ShVar : (erased (Nat) k i j) (erased (Skip k i j) p) -> (Shift k (Var i) (Var j)))
  (many ShLam : (erased (Nat) k) (erased (Term) b c) (erased (Shift (Succ k) b c) p) -> (Shift k (Lam b) (Lam c)))
  (many ShApp : (erased (Nat) k) (erased (Term) f g a b) (erased (Shift k f g) p) (erased (Shift k a b) q)
     -> (Shift k (App f a) (App g b))))

(def-adts $ (Sub : ((Nat) k) ((Term) u) ((Term) t) ((Term) r) -> Type)
  enum
  (many SubHit : (erased (Nat) k) (erased (Term) u) -> (Sub k u (Var k) u))
  (many SubMiss : (erased (Nat) k) (erased (Term) u) (erased (Nat) i j) (erased (Skip k i j) p) -> (Sub k u (Var j) (Var i)))
  (many SubLam : (erased (Nat) k) (erased (Term) u u1 b c) (erased (Shift (Zero) u u1) s) (erased (Sub (Succ k) u1 b c) p)
     -> (Sub k u (Lam b) (Lam c)))
  (many SubApp : (erased (Nat) k) (erased (Term) u f g a b) (erased (Sub k u f g) p) (erased (Sub k u a b) q)
     -> (Sub k u (App f a) (App g b))))

(def-adts $ (Step : ((Term) t) ((Term) u) -> Type)
  enum
  (many StBeta : (erased (Term) b u r) (erased (Sub (Zero) u b r) p) -> (Step (App (Lam b) u) r))
  (many StLam : (erased (Term) b c) (erased (Step b c) p) -> (Step (Lam b) (Lam c)))
  (many StAppL : (erased (Term) f g a) (erased (Step f g) p) -> (Step (App f a) (App g a)))
  (many StAppR : (erased (Term) f a b) (erased (Step a b) p) -> (Step (App f a) (App f b))))

(def-adts $ (Typed : ((List (Ty)) g) ((Term) t) ((Ty) a) -> Type)
  enum
  (many TyVar : (erased (List (Ty)) g) (erased (Nat) i) (erased (Ty) a) (erased (Nth (Ty) g i a) p) -> (Typed g (Var i) a))
  (many TyLam : (erased (List (Ty)) g) (erased (Term) b) (erased (Ty) a c) (erased (Typed (Cons (Ty) a g) b c) p)
     -> (Typed g (Lam b) (Arr a c)))
  (many TyApp : (erased (List (Ty)) g) (erased (Term) f x) (erased (Ty) a c) (erased (Typed g f (Arr a c)) p) (erased (Typed g x a) q)
     -> (Typed g (App f x) c)))
