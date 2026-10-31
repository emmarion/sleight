(def-adts $ (Or : (Type A) (Type B) -> Type)
  enum
  (many InL : (erased Type A B) (erased A a) -> (Or A B))
  (many InR : (erased Type A B) (erased B b) -> (Or A B)))

(def-adts $ (PermC :((Perm) g) ((Col) c) ((Col) d) -> Type)
  enum
  (many PC0 : (erased (Perm) g) -> (PermC g (C0) (C0)))
  (many PC1 : (erased (Col) p1 p2 p3) -> (PermC (MkPerm p1 p2 p3) (C1) p1))
  (many PC2 : (erased (Col) p1 p2 p3) -> (PermC (MkPerm p1 p2 p3) (C2) p2))
  (many PC3 : (erased (Col) p1 p2 p3) -> (PermC (MkPerm p1 p2 p3) (C3) p3)))

(def-adts $ (PermT : ((Perm) g) ((List (Col)) et) ((List (Col)) et2) -> Type)
  enum
  (many PTNil : (erased (Perm) g) -> (PermT g (Nil (Col)) (Nil (Col))))
  (many PTCons : (erased (Perm) g) (erased (Col) c d) (erased (List (Col)) et et2) (erased (PermC g c d) p)
      (erased (PermT g et et2) q) -> (PermT g (Cons (Col) c et) (Cons (Col) d et2))))

(def-adts $ (IsPerm : ((Perm) g) -> Type)
  enum
  (many IP123 : -> (IsPerm (MkPerm (C1) (C2) (C3))))
  (many IP132 : -> (IsPerm (MkPerm (C1) (C3) (C2))))
  (many IP213 : -> (IsPerm (MkPerm (C2) (C1) (C3))))
  (many IP231 : -> (IsPerm (MkPerm (C2) (C3) (C1))))
  (many IP312 : -> (IsPerm (MkPerm (C3) (C1) (C2))))
  (many IP321 : -> (IsPerm (MkPerm (C3) (C2) (C1)))))

; b says whether Color2 occurs before Color3 in l (true when neither occurs).
(def-adts $ (EvenTail : ((List (Col)) l) ((Bool) b) -> Type)
  enum
  (many ETNil : -> (EvenTail (Nil (Col)) (BTrue)))
  (many ET0 : (erased (List (Col)) l) (erased (Bool) b) (erased (EvenTail l b) p) -> (EvenTail (Cons (Col) (C0) l) b))
  (many ET1 : (erased (List (Col)) l) (erased (Bool) b) (erased (EvenTail l b) p) -> (EvenTail (Cons (Col) (C1) l) b))
  (many ET2 : (erased (List (Col)) l) -> (EvenTail (Cons (Col) (C2) l) (BTrue)))
  (many ET3 : (erased (List (Col)) l) -> (EvenTail (Cons (Col) (C3) l) (BFalse))))

; The tail, normalised by the head's edge rotation, is an even tail.
(def-adts $ (EvenT : ((List (Col)) et) ((Bool) b) -> Type)
  enum
  (many EvNil : -> (EvenT (Nil (Col)) (BTrue)))
  (many Ev0 : (erased (List (Col)) l) -> (EvenT (Cons (Col) (C0) l) (BTrue)))
  (many Ev1 : (erased (List (Col)) l) (erased (Bool) b) (erased (EvenTail l b) p) -> (EvenT (Cons (Col) (C1) l) b))
  (many Ev2 : (erased (List (Col)) l l2) (erased (Bool) b) (erased (PermT p312 l l2) q) (erased (EvenTail l2 b) p)
      -> (EvenT (Cons (Col) (C2) l) b))
  (many Ev3 : (erased (List (Col)) l l2) (erased (Bool) b) (erased (PermT p231 l l2) q) (erased (EvenTail l2 b) p)
      -> (EvenT (Cons (Col) (C3) l) b)))

; et2 is et itself if it is even, otherwise et with Color2 and Color3 swapped.
(def-adts $ (ETrace : ((List (Col)) et) ((List (Col)) et2) -> Type)
  enum
  (many ETrEven : (erased (List (Col)) et) (erased (EvenT et (BTrue)) p) -> (ETrace et et))
  (many ETrOdd : (erased (List (Col)) et et2) (erased (EvenT et (BFalse)) p) (erased (PermT p132 et et2) q) -> (ETrace et et2)))

(def-adts $ (Not : ((Bool) a) ((Bool) b) -> Type)
  enum
  (many NotT : -> (Not (BTrue) (BFalse)))
  (many NotF : -> (Not (BFalse) (BTrue))))

; One symbol of a partial chromogram matching one trace color, from open-chord stack bs to bs2.
(def-adts $ (Sym : ((Gsym) s) ((Bstack) bs) ((Col) e) ((Bstack) bs2) -> Type)
  enum
  (many SSkip : (erased (Bstack) bs) -> (Sym (GSkip) bs (C1) bs))
  (many SPush2 : (erased (Bstack) bs) -> (Sym (GPush) bs (C2) (BP0 bs)))
  (many SPush3 : (erased (Bstack) bs) -> (Sym (GPush) bs (C3) (BP1 bs)))
  (many SPop02 : (erased (Bstack) bs) -> (Sym (GPop0) (BP0 bs) (C2) bs))
  (many SPop12 : (erased (Bstack) bs) -> (Sym (GPop1) (BP1 bs) (C2) bs))
  (many SPop03 : (erased (Bstack) bs) -> (Sym (GPop0) (BP1 bs) (C3) bs))
  (many SPop13 : (erased (Bstack) bs) -> (Sym (GPop1) (BP0 bs) (C3) bs)))

(def-adts $ (MatchPG : ((Bstack) bs) ((List (Col)) et) ((List (Gsym)) w) -> Type)
  enum
  (many MPNil : (erased (Bstack) bs) -> (MatchPG bs (Nil (Col)) (Nil (Gsym))))
  (many MPCons : (erased (Bstack) bs bs2) (erased (Col) e) (erased (Gsym) s) (erased (List (Col)) et) (erased (List (Gsym)) w)
      (erased (Sym s bs e bs2) p) (erased (MatchPG bs2 et w) q) -> (MatchPG bs (Cons (Col) e et) (Cons (Gsym) s w))))

; The completion of w, from d open chords and parity b, is balanced.
(def-adts $ (GBal : ((Nat) d) ((Bool) b) ((List (Gsym)) w) -> Type)
  enum
  (many GBEnd0 : -> (GBal (Zero) (BTrue) (Nil (Gsym))))
  (many GBEnd1 : (erased (Bool) b) -> (GBal (Succ (Zero)) b (Nil (Gsym))))
  (many GBPush : (erased (Nat) d) (erased (Bool) b) (erased (List (Gsym)) w) (erased (GBal (Succ d) b w) p)
      -> (GBal d b (Cons (Gsym) (GPush) w)))
  (many GBSkip : (erased (Nat) d) (erased (Bool) b c) (erased (List (Gsym)) w) (erased (Not b c) n) (erased (GBal d c w) p)
      -> (GBal d b (Cons (Gsym) (GSkip) w)))
  (many GBPop0 : (erased (Nat) d) (erased (Bool) b) (erased (List (Gsym)) w) (erased (GBal d b w) p)
      -> (GBal (Succ d) b (Cons (Gsym) (GPop0) w)))
  (many GBPop1 : (erased (Nat) d) (erased (Bool) b c) (erased (List (Gsym)) w) (erased (Not b c) n) (erased (GBal d c w) p)
      -> (GBal (Succ d) b (Cons (Gsym) (GPop1) w))))

; A partial chromogram of n symbols whose completion is balanced.
(def-adts $ (InitG : ((Nat) n) ((List (Gsym)) w) -> Type)
  enum
  (many MkInitG : (erased (Nat) n) (erased (List (Gsym)) w) (erased (Length (Gsym) w n) l) (erased (GBal (Zero) (BFalse) w) b)
      -> (InitG n w)))

(def-adts $ (Third : ((Col) a) ((Col) b) ((Col) c) -> Type)
  enum
  (many T123 : -> (Third (C1) (C2) (C3)))
  (many T132 : -> (Third (C1) (C3) (C2)))
  (many T213 : -> (Third (C2) (C1) (C3)))
  (many T231 : -> (Third (C2) (C3) (C1)))
  (many T312 : -> (Third (C3) (C1) (C2)))
  (many T321 : -> (Third (C3) (C2) (C1))))

(def-adts $ (AddC : ((Col) a) ((Col) b) ((Col) c) -> Type)
  enum
  (many AZL : (erased (Col) b) -> (AddC (C0) b b))
  (many AZR : (erased (Col) a) -> (AddC a (C0) a))
  (many ASame : (erased (Col) a) -> (AddC a a (C0)))
  (many AThird : (erased (Col) a b c) (erased (Third a b c) t) -> (AddC a b c)))

(let ((erased AddK)) AddC)

; ct is et followed by s plus the sum of et.
(def-adts $ (Ctr : ((Col) s) ((List (Col)) et) ((List (Col)) ct) -> Type)
  enum
  (many CtrNil : (erased (Col) s) -> (Ctr s (Nil (Col)) (Cons (Col) s (Nil (Col)))))
  (many CtrCons : (erased (Col) s e s2) (erased (List (Col)) et ct) (erased (AddC s e s2) a) (erased (Ctr s2 et ct) c)
      -> (Ctr s (Cons (Col) e et) (Cons (Col) e ct))))
