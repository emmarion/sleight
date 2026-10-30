(def-adts $ (Rg : -> Type)
  enum
  (many MkRg : (many (Nat) lo hi) -> (Rg)))

(def-adts $ (Rel : -> Type)
  enum
  (many PDis : -> (Rel))
  (many PStr : -> (Rel))
  (many PSub : -> (Rel)))

(def-adts $ (Sub : -> Type)
  enum
  (many MkSub : (many (Rg) spoke hat) (many (List (Rg)) fans) -> (Sub)))

(def-adts $ (Loc : -> Type)
  enum
  (many LSpoke : -> (Loc))
  (many LHat : -> (Loc))
  (many LFan : (many (Nat) k) -> (Loc)))

(def-adts $ (Z : -> Type)
  enum
  (many MkZ : (many (Nat) pos neg) -> (Z)))

(let ((many r59)) (MkRg 5 9))

(def-fns _ $ (many leb : (many (Nat) a b) -> (many (Bool) c))
  (negb (nat-ltb b a)))

(def-fns _ $ (many nat-max : (many (Nat) a b) -> (many (Nat) c))
  (bif _ (nat-ltb a b) b a))

(def-fns _ $ (many nat-min : (many (Nat) a b) -> (many (Nat) c))
  (bif _ (nat-ltb a b) a b))

(def-fns _ $ (many rg-lo : (many (Rg) r) -> (many (Nat) n))
  (let-match many r (MkRg a _))
  a)

(def-fns _ $ (many rg-hi : (many (Rg) r) -> (many (Nat) n))
  (let-match many r (MkRg _ b))
  b)

(def-fns _ $ (many mem-rg : (many (Rg) r) (many (Nat) n) -> (many (Bool) b))
  (let-match many r (MkRg a c))
  (and (leb a n) (or (nat-eqb c 9) (leb n c))))

(def-fns _ $ (many cmp-rg : (many (Rg) r q) -> (many (Rel) c))
  (let-match many r (MkRg a b))
  (let-match many q (MkRg c d))
  (let-match many (and (leb c a) (leb b d)) (BFalse) ((BTrue) (PSub)))
  (bif _ (or (nat-ltb b c) (nat-ltb d a)) (PDis) (PStr)))

(def-fns _ $ (many meet-rel : (many (Rel) a b) -> (many (Rel) c))
  (let-match many a (PStr) ((PDis) a) ((PSub) b))
  (match many b _ ((PSub) a) (else b)))

(def-fns _ $ (many rel-sub : (many (Rel) a) -> (many (Bool) b))
  (match many a _ ((PSub) (BTrue)) (else (BFalse))))

(def-fns _ $ (many meet-rg : (many (Rg) r q) -> (many (Rg) m))
  (let-match many r (MkRg a b))
  (let-match many q (MkRg c d))
  (MkRg (nat-max a c) (nat-min b d)))

(def-fns _ $ (many prange-lo : (many (Nat) k) -> (many (Rg) r))
  (bif _ (andb (nat-ltb 4 k) (nat-ltb k 9)) (MkRg 5 k) r59))

(def-fns _ $ (many prange-hi : (many (Nat) k) -> (many (Rg) r))
  (bif _ (andb (nat-ltb 4 k) (nat-ltb k 9)) (MkRg (Succ k) 9) r59))

(def-fns _ $ (many good-rsplit : (many (Nat) k) (many (Rg) r) -> (many (Bool) b))
  (match many (cmp-rg r (prange-lo k)) _ ((PStr) (BTrue)) (else (BFalse))))

(def-fns _ $ (many split-range : (many (Nat) k) (many (Bool) lo) (many (Rg) r) -> (many (Rg) s))
  (meet-rg (bif _ lo (prange-lo k) (prange-hi k)) r))

(def-fns _ $ (many nth-rg : (subterm many (Nat) i) (many (List (Rg)) xs) -> (many (Rg) r))
  (let-match many xs (Cons _ x rest) ((Nil _) r59))
  (let-match many i (Succ i1) ((Zero) x))
  (tail $ nth-rg i1 rest))

(def-fns _ $ (many set-nth-rg : (subterm many (Nat) i) (many (Rg) y) (many (List (Rg)) xs) -> (many (List (Rg)) ys))
  (let-match many xs (Cons _ x rest) ((Nil _) xs))
  (let-match many i (Succ i1) ((Zero) (Cons _ y rest)))
  (Cons _ x $ notail $ set-nth-rg i1 y rest))

(def-fns _ $ (many pc : (many (Rg) s h) -> (many (Sub) x))
  (MkSub s h (Nil _)))

(def-fns _ $ (many pf : (many (Rg) h) (many (List (Rg)) fs) -> (many (Sub) x))
  (let ((many n)) (nat-add 5 (size _ fs)))
  (MkSub (MkRg n n) h fs))

(def-fns _ $ (many get-spoke : (many (List (Sub)) p) -> (many (Rg) r))
  (let-match many p (Cons _ x _) ((Nil _) r59))
  (let-match many x (MkSub s _ _))
  s)

(def-fns _ $ (many next-hat : (many (Rg) h0) (many (List (Sub)) p) -> (many (Rg) r))
  (let-match many p (Cons _ x _) ((Nil _) h0))
  (let-match many x (MkSub _ h _))
  h)

(def-fns _ $ (many get-hat : (many (List (Sub)) p) -> (many (Rg) r))
  (next-hat r59 p))

(def-fns _ $ (many get-fans : (many (List (Sub)) p) -> (many (List (Rg)) fs))
  (let-match many p (Cons _ x _) ((Nil _) (Nil _)))
  (let-match many x (MkSub _ _ fs))
  fs)

(def-fns _ $ (many fan-r : (many (Nat) k) (many (List (Sub)) p) -> (many (Rg) r))
  (nth-rg k (get-fans p)))

(def-fns _ $ (many fan-l : (many (Nat) k) (many (List (Sub)) p) -> (many (Rg) r))
  (nth-rg k (rev-onto _ (get-fans p) (Nil _))))

(def-fns _ $ (many pcons- : (many (Nat) n) -> (many (List (Sub)) p))
  (nseq _ n (pc r59 r59)))

(def-fns _ $ (many mirror-rec : (many (Rg) h0) (many (List (Sub)) rp) (subterm many (List (Sub)) p) -> (many (List (Sub)) r))
  (let-match many p (Cons _ x p1) ((Nil _) rp))
  (let-match many x (MkSub s _ fs))
  (tail $ mirror-rec h0 (Cons _ (MkSub s (next-hat h0 p1) (rev-onto _ fs (Nil _))) rp) p1))

(def-fns _ $ (many mirror-part : (many (List (Sub)) p) -> (many (List (Sub)) r))
  (mirror-rec (get-hat p) (Nil _) p))

(def-fns _ $ (many cmp-fans : (subterm many (List (Rg)) fp) (many (List (Rg)) fq) -> (many (Rel) c))
  (let-match many fq (Cons _ g gs) ((Nil _) (PSub)))
  (let-match many fp (Cons _ f fs) ((Nil _) (PStr)))
  (meet-rel (cmp-rg f g) (notail $ cmp-fans fs gs)))

(def-fns _ $ (many cmp-part : (subterm many (List (Sub)) p) (many (List (Sub)) q) -> (many (Rel) c))
  (let-match many q (Cons _ y q1) ((Nil _) (PSub)))
  (let-match many p (Cons _ x p1) ((Nil _) (PStr)))
  (let-match many x (MkSub s h fp))
  (let-match many y (MkSub s2 h2 fq))
  (meet-rel (cmp-rg s s2) $ meet-rel (cmp-rg h h2) $ meet-rel (cmp-fans fp fq) (notail $ cmp-part p1 q1)))

(def-fns _ $ (many meet-fans : (subterm many (List (Rg)) fp) (many (List (Rg)) fq) -> (many (List (Rg)) r))
  (let-match many fp (Cons _ f fs) ((Nil _) fq))
  (let-match many fq (Cons _ g gs) ((Nil _) fp))
  (Cons _ (meet-rg f g) $ notail $ meet-fans fs gs))

(def-fns _ $ (many meet-part : (many (List (Sub)) p) (subterm many (List (Sub)) q) -> (many (List (Sub)) r))
  (let-match many q (Cons _ y q1) ((Nil _) p))
  (let-match many p (Cons _ x p1) ((Nil _) p))
  (let-match many x (MkSub s h fp))
  (let-match many y (MkSub s2 h2 fq))
  (let ((many fpe) (many fqe)) (values (nilp _ fp) (nilp _ fq)))
  (match many (and (negb fpe) (negb fqe) (negb (nat-eqb (size _ fp) (size _ fq)))) _
    ((BTrue) p)
    ((BFalse) (Cons _ (MkSub (bif _ fpe (bif _ fqe (meet-rg s s2) s2) s) (meet-rg h h2) (meet-fans fp fq)) $ notail $ meet-part p1 q1))))

(def-fns _ $ (many expand-fans : (many (Sub) x) -> (many (List (Rg)) fs))
  (let-match many x (MkSub s _ fs))
  (let-match many fs (Nil _) (else fs))
  (let-match many s (MkRg a b))
  (bif _ (andb (nat-eqb a b) (leb b 8)) (nseq _ (monus b 5) r59) fs))

(def-fns _ $ (many loc-range : (many (Bool) ex) (many (Loc) i) (many (Sub) x) -> (many (Maybe (Rg)) r))
  (let-match many x (MkSub s h fs))
  (let-match many i (LFan k) ((LSpoke) (bif _ (nilp _ fs) (Some _ s) (None _))) ((LHat) (Some _ h)))
  (let ((many gs)) (bif _ ex (expand-fans x) fs))
  (bif _ (nat-ltb k (size _ gs)) (Some _ (nth-rg k gs)) (None _)))

(def-fns _ $ (many loc-set : (many (Loc) i) (many (Sub) x) (many (Rg) r) -> (many (Sub) y))
  (let-match many x (MkSub s h fs))
  (match many i _
    ((LSpoke) (MkSub r h fs))
    ((LHat) (MkSub s r fs))
    ((LFan k) (MkSub s h (set-nth-rg k r (expand-fans x))))))

(def-fns _ $ (many good-split : (many (Loc) i) (many (Nat) j k) (many (List (Sub)) p) -> (many (Bool) b))
  (let-match many (drop _ j p) (Cons _ x _) ((Nil _) (BFalse)))
  (let-match many (loc-range (BTrue) i x) (Some _ r) ((None _) (BFalse)))
  (good-rsplit k r))

(def-fns _ $ (many split-part : (many (Loc) i) (many (Nat) j k) (many (Bool) lo) (many (List (Sub)) p) -> (many (List (Sub)) q))
  (let-match many (drop _ j p) (Cons _ x rest) ((Nil _) p))
  (let-match many (loc-range (BTrue) i x) (Some _ r) ((None _) p))
  (cat _ (take _ j p) (Cons _ (loc-set i x (split-range k lo r)) rest)))

(def-fns _ $ (many z-add : (many (Z) a b) -> (many (Z) c))
  (let-match many a (MkZ ap an))
  (let-match many b (MkZ bp bn))
  (MkZ (nat-add ap bp) (nat-add an bn)))

(def-fns _ $ (many z-nat : (many (Z) a) -> (many (Bool) ok) (many (Nat) n))
  (let-match many a (MkZ ap an))
  (values (leb an ap) (monus ap an)))
