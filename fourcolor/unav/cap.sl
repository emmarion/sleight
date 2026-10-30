; dscore_cap1 of discharge.v: a dart of arity 12 or more with positive dscore has an obligation of the dbound1 checks of
; arities 5 to 8 fitting exactly somewhere, when every rule has fewer than 9 subparts. Load after conv.sl.

(unary 11 10)

(def-fns _ $ (erased mul-dbl : (erased (Nat) k x y) (erased (Mul k 5 x) m5) (erased (Mul k 10 y) m10) -> (erased (Add x x y) r))
  (mul-distr 5 5 10 k x x y (add5 5) (mul-comm k 5 x m5) (mul-comm k 5 x m5) (mul-comm k 10 y m10)))

; A positive dscore 60 + sp > 10 a + sn with sp <= 5 a needs a < 12.
(def-fns _ $ (erased absurd cap-arith : (erased (Nat) a c60 t t5 sp sn pos neg) (erased (Mul 6 10 c60) m60) (erased (Mul a 10 t) mt)
    (erased (Add c60 sp pos) ap) (erased (Add t sn neg) an) (erased (Lt neg pos) lt) (erased (Mul a 5 t5) m5) (erased (Lt sp (Succ t5)) lst)
    (erased (Lt 11 a) l11) -> (erased (False) r))
  (let ((erased x) (erased ax)) (lt-diff 11 a l11))
  (let-match erased (add-comm 11 (Succ x) a ax) (AddSucc _ _ a1 xa))
  (let ((erased ad)) (AddSucc 11 x a1 (add-comm x 11 a1 xa)))
  (let ((erased t12) (erased m12)) (mul 12 5))
  (let ((erased mx) (erased mmx)) (mul x 5))
  (let ((erased e1)) (mul-distr 12 x a 5 t12 mx t5 ad m12 mmx m5))
  (let ((erased x6) (erased m6)) (mul 6 5))
  (let-match erased (add-fn x6 x6 t12 c60 (mul-distr 6 6 12 5 x6 x6 t12 (AddSucc 5 6 11 (add5 6)) m6 m6 m12) (mul-dbl 6 x6 c60 m6 m60)) (Refl _ _))
  (let ((erased q) (erased aq)) (add c60 t5))
  (let ((erased l1)) (add-le-r c60 sp pos t5 q ap aq lst))
  (let ((erased l2)) (add-mono-le t5 c60 t5 q t (add-le-left c60 mx t5 e1) (add-comm c60 t5 q aq) (mul-dbl a t5 t m5 mt)))
  (lt-le-absurd neg pos lt (le-tr pos q neg l1 (le-tr q t neg l2 (add-le-left t sn neg an)))))

(def-adts $ (Small : ((List (List (Sub))) rs) -> Type)
  enum
  (many SmNil : -> (Small (Nil (List (Sub)))))
  (many SmCons : (erased (List (Sub)) r) (erased (List (List (Sub))) rs) (erased (Nat) l) (erased (Length (Sub) r l) pl) (erased (Lt l 9) lt)
      (erased (Small rs) rest) -> (Small (Cons (List (Sub)) r rs))))

(def-fns _ $ (many small-c : (subterm many (List (List (Sub))) rs) -> (many (Bool) ok) (erased (IfT ok (Small rs)) w))
  (let-match many rs (Cons _ r rs1) ((Nil _) (values (BTrue) (IfY _ (SmNil)))))
  (let ((many l) (erased pl)) (list-count _ r))
  (let-match many (lt-test l 9) (LtYes _ _ lt) ((LtNo _ _) (values (BFalse) (IfF _))))
  (let ((many ok) (erased w)) (tail $ small-c rs1))
  (values ok (match erased w _ ((IfY _ s) (IfY _ (SmCons r rs1 l pl lt s))) ((IfF _) (IfF _)))))

(def-fns _ $ (erased of-size-big : (erased (Nat) m) (erased (List (List (Sub))) rs) (erased (Lt 8 m) l8) (subterm erased (Small rs) sm)
    -> (erased (OfSize m rs (Nil (List (Sub)))) r))
  (let-match erased sm (SmCons r rs1 l pl lt rest) ((SmNil) (OSNil m)))
  (OSOut m l r rs1 (Nil _) pl (ApLt _ _ l m (lt-le-trans l 9 m lt (LtS 8 m l8))) (of-size-big m rs1 l8 rest)))

(let ((many sub59)) (MkSub (MkRg 5 9) (MkRg 5 9) (Nil (Rg))))

; The dbound1 checks of arities m to hi - 1 with bound 5, each from the obligations of the one before, from acc to cobl.
(def-adts $ (CapL : ((List (List (Sub))) drs acc cobl) ((Nat) m hi) -> Type)
  enum
  (many CLNil : (erased (List (List (Sub))) drs acc) (erased (Nat) m) -> (CapL drs acc acc m m))
  (many CLCons : (erased (List (List (Sub))) drs acc out cobl rs) (erased (Nat) m hi) (erased (List (Sub)) p) (erased (OfSize m drs rs) sz)
      (erased (Repeat (Sub) m sub59 p) rp) (erased (Db1 p rs 5 acc out) db) (erased (CapL drs out cobl (Succ m) hi) rest) -> (CapL drs acc cobl m hi)))

(def-fns _ $ (many cap-c : (many (List (List (Sub))) drs acc) (many (Nat) m hi) (subterm many (Nat) fuel)
    -> (many (Bool) ok) (many (List (List (Sub))) cobl) (erased (IfT ok (CapL drs acc cobl m hi)) w))
  (let-match many (nat-eq m hi) (Unequal _ _ _ _ _) ((Equal _ _ _) (values (BTrue) acc (IfY _ (CLNil drs acc m)))))
  (let-match many fuel (Succ f1) ((Zero) (values (BFalse) acc (IfF _))))
  (let ((many rs) (erased sz)) (of-size-c m drs))
  (let ((many p) (erased rp)) (nseq-c _ m sub59))
  (let ((many ok1) (many out) (erased w1)) (check-dbound1-c p rs 5 acc))
  (let-match many ok1 (BTrue) ((BFalse) (values (BFalse) acc (IfF _))))
  (let-match erased w1 (IfY _ db))
  (let ((many ok) (many cobl) (erased w)) (tail $ cap-c drs out (Succ m) hi f1))
  (values ok cobl (match erased w _ ((IfY _ c) (IfY _ (CLCons drs acc out cobl rs m hi p sz rp db c))) ((IfF _) (IfF _)))))

(def-fns _ $ (erased cap-ext : (erased (List (List (Sub))) drs acc cobl) (erased (Nat) m hi) (subterm erased (CapL drs acc cobl m hi) c)
    -> (erased (Ext acc cobl) e))
  (let-match erased c (CLCons _ _ out _ rs _ _ p _ _ db rest) ((CLNil _ _ _) (ExtRefl acc)))
  (ext-trans acc out cobl (db1-ext p rs 5 acc out db) (cap-ext drs out cobl (Succ m) hi rest)))

(def-fns _ $ (erased cap-look : (erased (List (List (Sub))) drs acc cobl) (erased (Nat) a m hi) (subterm erased (CapL drs acc cobl m hi) c)
    (erased (Lt m (Succ a)) lo) (erased (Lt a hi) up) -> (erased (List (List (Sub))) rs acc1 out) (erased (List (Sub)) p) (erased (OfSize a drs rs) sz)
    (erased (Repeat (Sub) a sub59 p) rp) (erased (Db1 p rs 5 acc1 out) db) (erased (Ext out cobl) e))
  (let-match erased c (CLCons _ _ out _ rs _ _ p sz rp db rest) (absurd (CLNil _ _ _) (lt-le-absurd a m up lo)))
  (match erased (nat-eq a m) _
    ((Equal _ _ _) (values rs acc out p sz rp db (cap-ext drs out cobl (Succ m) hi rest)))
    ((Unequal _ _ _ _ ap)
      (match erased ap _
        (absurd (ApLt _ _ _ _ l) (lt-le-absurd a m l lo))
        ((ApGt _ _ _ _ l) (cap-look drs out cobl a (Succ m) hi rest (LtS m a l) up))))))

(def-fns _ $ (erased rep-fit : (erased (Nat) d y k) (erased (List (Nat)) e n f ks) (erased (List (Sec)) os) (erased (List (Sub)) p) (erased (Geo d e n f ks) g)
    (subterm erased (ObsAt e f ks y k os) ob) (erased (Repeat (Sub) k sub59 p) rp) -> (erased (Pw (Sec) (Sub) FitSec os p) fo) (erased (Length (Sub) p k) l))
  (let-match erased ob (OACons _ _ _ _ y1 k1 o os1 so _ ob1) ((OANil _ _ _ _) (let-match erased rp (RepeatNil _ _)) (values (PwNil _ _ FitSec os) (LengthNil _))))
  (let-match erased rp (RepeatCons _ _ _ p1 rp1))
  (let-match erased so (MkSecAt _ _ _ _ z a _ u h _ _ fs _ pa _ _ ph _ _ _))
  (let ((erased fo) (erased l)) (rep-fit d y1 k1 e n f ks os1 p1 g ob1 rp1))
  (values (PwCons _ _ FitSec o sub59 os1 p1 (MkFitSec a h fs (MkRg 5 9) (MkRg 5 9) (Nil _) (pent d z a e n f ks g pa) (pent d u h e n f ks g ph) (PwNil _ _ InRg fs)) fo)
    (LengthCons _ sub59 p1 k1 l)))

; Every dart fits the part with k sectors 5..9 exactly.
(def-fns _ $ (erased root-exact : (erased (Nat) d y k) (erased (List (Nat)) e n f ks) (erased (List (Sec)) os) (erased (List (Sub)) p) (erased (Geo d e n f ks) g)
    (erased (ObsAt e f ks y k os) ob) (erased (Repeat (Sub) k sub59 p) rp) -> (erased (Exact os p) x))
  (let ((erased fo) (erased l)) (rep-fit d y k e n f ks os p g ob rp))
  (MkExact os p k fo (obs-len e f ks y k os ob) l))
