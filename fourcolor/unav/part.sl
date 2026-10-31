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

(def-fns _ $ (many rg-hi : (many (Rg) r) -> (many (Nat) n))
  (let-match many r (MkRg _ b))
  b)

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

(def-fns _ $ (many prange-lo : (many (Nat) k) -> (many (Rg) r))
  (bif _ (andb (nat-ltb 4 k) (nat-ltb k 9)) (MkRg 5 k) r59))

(def-fns _ $ (many good-rsplit : (many (Nat) k) (many (Rg) r) -> (many (Bool) b))
  (match many (cmp-rg r (prange-lo k)) _ ((PStr) (BTrue)) (else (BFalse))))

(def-fns _ $ (many nth-rg : (subterm many (Nat) i) (many (List (Rg)) xs) -> (many (Rg) r))
  (let-match many xs (Cons _ x rest) ((Nil _) r59))
  (let-match many i (Succ i1) ((Zero) x))
  (tail $ nth-rg i1 rest))

(def-fns _ $ (many pc : (many (Rg) s h) -> (many (Sub) x))
  (MkSub s h (Nil _)))

(def-fns _ $ (many pf : (many (Rg) h) (many (List (Rg)) fs) -> (many (Sub) x))
  (let ((many n)) (nat-add 5 (size _ fs)))
  (MkSub (MkRg n n) h fs))

(def-fns _ $ (many next-hat : (many (Rg) h0) (many (List (Sub)) p) -> (many (Rg) r))
  (let-match many p (Cons _ x _) ((Nil _) h0))
  (let-match many x (MkSub _ h _))
  h)

(def-fns _ $ (many get-hat : (many (List (Sub)) p) -> (many (Rg) r))
  (next-hat r59 p))

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

(def-fns _ $ (many good-split : (many (Loc) i) (many (Nat) j k) (many (List (Sub)) p) -> (many (Bool) b))
  (let-match many (drop _ j p) (Cons _ x _) ((Nil _) (BFalse)))
  (let-match many (loc-range (BTrue) i x) (Some _ r) ((None _) (BFalse)))
  (good-rsplit k r))
