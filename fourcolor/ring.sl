(def-fns _ $ (erased add-assoc : (erased (Nat) a b c ab abc) (subterm erased (Add a b ab) p) (erased (Add ab c abc) q) ->
    (erased (Nat) bc) (erased (Add b c bc) r) (erased (Add a bc abc) s))
  (let-match erased p (AddSucc a1 _ ab1 p1) ((AddZero _) (values abc q (AddZero abc))))
  (let-match erased q (AddSucc _ _ abc1 q1))
  (let ((erased bc) (erased r) (erased s)) (add-assoc a1 b c ab1 abc1 p1 q1))
  (values bc r (AddSucc a1 bc abc1 s)))

(def-fns _ $ (erased add-right-comm : (erased (Nat) x c xc d r) (subterm erased (Add x c xc) p) (erased (Add xc d r) q) ->
    (erased (Nat) t) (erased (Add x d t) s) (erased (Add t c r) u))
  (let-match erased p (AddSucc x1 _ xc1 p1) ((AddZero _) (values d (AddZero d) (add-comm c d r q))))
  (let-match erased q (AddSucc _ _ r1 q1))
  (let ((erased t) (erased s) (erased u)) (add-right-comm x1 c xc1 d r1 p1 q1))
  (values (Succ t) (AddSucc x1 d t s) (AddSucc t c r1 u)))

(def-fns _ $ (erased mul-zero-right : (subterm erased (Nat) a) -> (erased (Mul a (Zero) (Zero)) p))
  (let-match erased a (Succ a1) ((Zero) (MulZero (Zero))))
  (MulSucc a1 (Zero) (Zero) (Zero) (mul-zero-right a1) (AddZero (Zero))))

(def-fns _ $ (erased mul-succ-right : (erased (Nat) a b c d) (subterm erased (Mul a b c) m) (erased (Add c a d) q) ->
    (erased (Mul a (Succ b) d) r))
  (let-match erased m (MulSucc a1 _ c1 _ m1 p) ((MulZero _) (let-match erased q (AddZero _)) (MulZero (Succ b))))
  (let ((erased d1) (erased e) (erased q1)) (add-succ-right-inv c a1 d q))
  (let ((erased t) (erased s) (erased u)) (add-right-comm c1 b c a1 d1 p q1))
  (let-match erased e (Refl _ _))
  (MulSucc a1 (Succ b) t d (mul-succ-right a1 b c1 t m1 s) (add-succ-right t b d1 u)))

(def-fns _ $ (erased mul-comm : (erased (Nat) a b c) (subterm erased (Mul a b c) m) -> (erased (Mul b a c) r))
  (let-match erased m (MulSucc a1 _ c1 _ m1 p) ((MulZero _) (mul-zero-right b)))
  (mul-succ-right b a1 c1 c (mul-comm a1 b c1 m1) p))

(def-fns _ $ (erased mul-distr : (erased (Nat) a b s c ac bc sc) (subterm erased (Add a b s) p)
    (erased (Mul a c ac) ma) (erased (Mul b c bc) mb) (erased (Mul s c sc) ms) -> (erased (Add ac bc sc) r))
  (let-match erased p (AddSucc a1 _ s1 p1)
    ((AddZero _) (let-match erased ma (MulZero _)) (let-match erased (mul-fn b c bc sc mb ms) (Refl _ _)) (AddZero bc)))
  (let-match erased ma (MulSucc _ _ x _ ma1 qa))
  (let-match erased ms (MulSucc _ _ y _ ms1 qs))
  (let ((erased t) (erased u) (erased v)) (add-right-comm x bc y c sc (mul-distr a1 b s1 c x bc y p1 ma1 mb ms1) qs))
  (let-match erased (add-fn x c t ac u qa) (Refl _ _))
  v)

(def-fns _ $ (erased mul-assoc : (erased (Nat) a b c ab abc bc) (subterm erased (Mul a b ab) m)
    (erased (Mul ab c abc) n) (erased (Mul b c bc) o) -> (erased (Mul a bc abc) r))
  (let-match erased m (MulSucc a1 _ x _ m1 p) ((MulZero _) (let-match erased n (MulZero _)) (MulZero bc)))
  (let ((erased xc) (erased mx)) (mul x c))
  (MulSucc a1 bc xc abc (mul-assoc a1 b c x xc bc m1 mx o) (mul-distr x b ab c xc bc abc p mx o n)))

(let ((many i0)) (Zero))
(let ((many i1)) (Succ i0))
(let ((many i2)) (Succ i1))
(let ((many i3)) (Succ i2))
(def-fns _
  ((erased unary-1 : -> (erased (Eq (Nat) 1 (Succ (Zero))) e))
    (unary 1)
    (Refl _ 1))
  ((erased unary-2 : -> (erased (Eq (Nat) 2 (Succ (Succ (Zero)))) e))
    (unary 2)
    (Refl _ 2))
  ((erased unary-2-1 : -> (erased (Eq (Nat) 2 (Succ 1)) e))
    (unary 2 1)
    (Refl _ 2))
  ((erased unary-3 : -> (erased (Eq (Nat) 3 (Succ (Succ (Succ (Zero))))) e))
    (unary 3)
    (Refl _ 3))
  ((erased unary-3-2 : -> (erased (Eq (Nat) 3 (Succ 2)) e))
    (unary 3 2)
    (Refl _ 3))
  ((erased unary-4 : -> (erased (Eq (Nat) 4 (Succ (Succ (Succ (Succ (Zero)))))) e))
    (unary 4)
    (Refl _ 4))
  ((erased unary-5 : -> (erased (Eq (Nat) 5 (Succ (Succ (Succ (Succ (Succ (Zero))))))) e))
    (unary 5)
    (Refl _ 5))
  ((erased unary-5-4 : -> (erased (Eq (Nat) 5 (Succ 4)) e))
    (unary 5 4)
    (Refl _ 5))
  ((erased unary-6 : -> (erased (Eq (Nat) 6 (Succ (Succ (Succ (Succ (Succ (Succ (Zero)))))))) e))
    (unary 6)
    (Refl _ 6))
  ((erased unary-6-5 : -> (erased (Eq (Nat) 6 (Succ 5)) e))
    (unary 6 5)
    (Refl _ 6))
  ((erased unary-7-6 : -> (erased (Eq (Nat) 7 (Succ 6)) e))
    (unary 7 6)
    (Refl _ 7))
  ((erased unary-8 : -> (erased (Eq (Nat) 8 (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero)))))))))) e))
    (unary 8)
    (Refl _ 8))
  ((erased unary-8-7 : -> (erased (Eq (Nat) 8 (Succ 7)) e))
    (unary 8 7)
    (Refl _ 8))
  ((erased unary-9-8 : -> (erased (Eq (Nat) 9 (Succ 8)) e))
    (unary 9 8)
    (Refl _ 9))
  ((erased unary-10-9 : -> (erased (Eq (Nat) 10 (Succ 9)) e))
    (unary 10 9)
    (Refl _ 10))
  ((erased unary-11-10 : -> (erased (Eq (Nat) 11 (Succ 10)) e))
    (unary 11 10)
    (Refl _ 11))
  ((erased unary-12 : -> (erased (Eq (Nat) 12 (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero)))))))))))))) e))
    (unary 12)
    (Refl _ 12))
  ((erased unary-12-10 : -> (erased (Eq (Nat) 12 (Succ (Succ 10))) e))
    (unary 12 10)
    (Refl _ 12))
  ((erased lit-lt-1-4 : -> (erased (Lt 1 4) p))
    (prove-literal-lt 1 4))
  ((erased lit-lt-4-8 : -> (erased (Lt 4 8) p))
    (prove-literal-lt 4 8))
  ((erased lit-lt-5-9 : -> (erased (Lt 5 9) p))
    (prove-literal-lt 5 9))
  ((erased lit-lt-6-9 : -> (erased (Lt 6 9) p))
    (prove-literal-lt 6 9))
  ((erased lit-lt-7-9 : -> (erased (Lt 7 9) p))
    (prove-literal-lt 7 9))
  ((erased lit-lt-8-9 : -> (erased (Lt 8 9) p))
    (prove-literal-lt 8 9)))


(let ((erased Mono)) (List (Nat)))
(let ((erased Poly)) (List Mono))

(def-adts $ (Layer : (Type A) -> Type)
  enum
  (many Factors : -> (Layer (Nat)))
  (many Terms : -> (Layer Mono)))

(def-adts $ (Op : (Type A) ((Layer A) l) ((Nat) a) ((Nat) b) ((Nat) c) -> Type)
  enum
  (many OpMul : (erased (Nat) a b c) (erased (Mul a b c) p) -> (Op (Nat) (Factors) a b c))
  (many OpAdd : (erased (Nat) a b c) (erased (Add a b c) p) -> (Op Mono (Terms) a b c)))

(def-adts $ (Neutral : (Type A) ((Layer A) l) ((Nat) u) -> Type)
  enum
  (many NeutralMul : -> (Neutral (Nat) (Factors) (Succ (Zero))))
  (many NeutralAdd : -> (Neutral Mono (Terms) (Zero))))

(def-adts
  ((Val : ((List (Nat)) env) (Type A) ((Layer A) l) (A x) ((Nat) n) -> Type)
    enum
    (many ValVar : (erased (List (Nat)) env) (erased (Nat) i n) (erased (Nth (Nat) env i n) p) -> (Val env (Nat) (Factors) i n))
    (many ValMono : (erased (List (Nat)) env) (erased Mono m) (erased (Nat) n) (erased (Fold env (Nat) (Factors) m n) p)
       -> (Val env Mono (Terms) m n)))
  ((Fold : ((List (Nat)) env) (Type A) ((Layer A) l) ((List A) xs) ((Nat) n) -> Type)
    enum
    (many FoldNil : (erased (List (Nat)) env) (erased Type A) (erased (Layer A) l) (erased (Nat) u) (erased (Neutral A l u) p)
       -> (Fold env A l (Nil A) u))
    (many FoldCons : (erased (List (Nat)) env) (erased Type A) (erased (Layer A) l) (erased A x) (erased (List A) xs) (erased (Nat) a b n)
       (erased (Val env A l x a) v) (erased (Fold env A l xs b) f) (erased (Op A l a b n) o) -> (Fold env A l (Cons A x xs) n))))

(def-fns _ $ (erased op-total : (erased Type A) (erased (Layer A) l) (erased (Nat) a b) -> (erased (Nat) c) (erased (Op A l a b c) o))
  (match erased l _
    ((Factors) (let ((erased c) (erased p)) (mul a b)) (values c (OpMul a b c p)))
    ((Terms) (let ((erased c) (erased p)) (add a b)) (values c (OpAdd a b c p)))))

(def-fns _ $ (erased op-fn : (erased Type A) (erased (Layer A) l) (erased (Nat) a b c d) (erased (Op A l a b c) o) (erased (Op A l a b d) o2) ->
    (erased (Eq (Nat) c d) e))
  (match erased o _
    ((OpMul _ _ _ p) (let-match erased o2 (OpMul _ _ _ q)) (mul-fn a b c d p q))
    ((OpAdd _ _ _ p) (let-match erased o2 (OpAdd _ _ _ q)) (add-fn a b c d p q))))

(def-fns _ $ (erased op-comm : (erased Type A) (erased (Layer A) l) (erased (Nat) a b c) (erased (Op A l a b c) o) -> (erased (Op A l b a c) r))
  (match erased o _
    ((OpMul _ _ _ p) (OpMul b a c (mul-comm a b c p)))
    ((OpAdd _ _ _ p) (OpAdd b a c (add-comm a b c p)))))

(def-fns _ $ (erased op-assoc : (erased Type A) (erased (Layer A) l) (erased (Nat) a b c ab abc) (erased (Op A l a b ab) o) (erased (Op A l ab c abc) o2) ->
    (erased (Nat) bc) (erased (Op A l b c bc) r) (erased (Op A l a bc abc) s))
  (match erased o _
    ((OpMul _ _ _ p)
      (let-match erased o2 (OpMul _ _ _ q))
      (let ((erased bc) (erased m)) (mul b c))
      (values bc (OpMul b c bc m) (OpMul a bc abc (mul-assoc a b c ab abc bc p q m))))
    ((OpAdd _ _ _ p)
      (let-match erased o2 (OpAdd _ _ _ q))
      (let ((erased bc) (erased r) (erased s)) (add-assoc a b c ab abc p q))
      (values bc (OpAdd b c bc r) (OpAdd a bc abc s)))))

(def-fns _ $ (erased op-assoc-rev : (erased Type A) (erased (Layer A) l) (erased (Nat) a b c bc abc) (erased (Op A l b c bc) o) (erased (Op A l a bc abc) o2) ->
    (erased (Nat) ab) (erased (Op A l a b ab) r) (erased (Op A l ab c abc) s))
  (let ((erased ab) (erased r)) (op-total A l a b))
  (let ((erased x) (erased s)) (op-total A l ab c))
  (let ((erased bc1) (erased o3) (erased o4)) (op-assoc A l a b c ab x r s))
  (let-match erased (op-fn A l b c bc bc1 o o3) (Refl _ _))
  (let-match erased (op-fn A l a bc abc x o2 o4) (Refl _ _))
  (values ab r s))

(def-fns _ $ (erased op-swap : (erased Type A) (erased (Layer A) l) (erased (Nat) y t b a c d)
    (erased (Op A l y t b) o1) (erased (Op A l a b c) o2) (erased (Op A l a t d) o3) -> (erased (Op A l y d c) r))
  (let ((erased ay) (erased o4) (erased o5)) (op-assoc-rev A l a y t b c o1 o2))
  (let ((erased w) (erased o6) (erased o7)) (op-assoc A l y a t ay c (op-comm A l a y ay o4) o5))
  (let-match erased (op-fn A l a t w d o6 o3) (Refl _ _))
  o7)

(def-adts $ (Expr : -> Type)
  enum
  (many EVar : (many (Nat) i) -> (Expr))
  (many ENum : (many (Nat) k) -> (Expr))
  (many EAdd : (many (Expr) a) (many (Expr) b) -> (Expr))
  (many EMul : (many (Expr) a) (many (Expr) b) -> (Expr)))

(def-adts $ (Eval : ((List (Nat)) env) ((Expr) e) ((Nat) n) -> Type)
  enum
  (many EvVar : (erased (List (Nat)) env) (erased (Nat) i n) (erased (Nth (Nat) env i n) p) -> (Eval env (EVar i) n))
  (many EvNum : (erased (List (Nat)) env) (erased (Nat) k) -> (Eval env (ENum k) k))
  (many EvAdd : (erased (List (Nat)) env) (erased (Expr) a b) (erased (Nat) x y n)
     (erased (Eval env a x) ea) (erased (Eval env b y) eb) (erased (Add x y n) p) -> (Eval env (EAdd a b) n))
  (many EvMul : (erased (List (Nat)) env) (erased (Expr) a b) (erased (Nat) x y n)
     (erased (Eval env a x) ea) (erased (Eval env b y) eb) (erased (Mul x y n) p) -> (Eval env (EMul a b) n)))

(def-adts $ (Insert : (Type A) (A x) ((List A) ys) ((List A) zs) -> Type)
  enum
  (many InsHere : (erased Type A) (erased A x) (erased (List A) ys) -> (Insert A x ys (Cons A x ys)))
  (many InsThere : (erased Type A) (erased A x y) (erased (List A) ys zs) (erased (Insert A x ys zs) p)
     -> (Insert A x (Cons A y ys) (Cons A y zs))))

(def-adts $ (InsAll : (Type A) ((List A) xs) ((List A) ys) ((List A) zs) -> Type)
  enum
  (many IANil : (erased Type A) (erased (List A) ys) -> (InsAll A (Nil A) ys ys))
  (many IACons : (erased Type A) (erased A x) (erased (List A) xs ys ws zs) (erased (InsAll A xs ys ws) p) (erased (Insert A x ws zs) q)
     -> (InsAll A (Cons A x xs) ys zs)))

(def-adts $ (Scale : (Mono m) (Poly q) (Poly s) -> Type)
  enum
  (many ScNil : (erased Mono m) -> (Scale m (Nil Mono) (Nil Mono)))
  (many ScCons : (erased Mono m n mn) (erased Poly q s) (erased (InsAll (Nat) m n mn) p) (erased (Scale m q s) r)
     -> (Scale m (Cons Mono n q) (Cons Mono mn s))))

(def-adts $ (PMul : (Poly p) (Poly q) (Poly r) -> Type)
  enum
  (many PMNil : (erased Poly q) -> (PMul (Nil Mono) q (Nil Mono)))
  (many PMCons : (erased Mono m) (erased Poly p q s r t) (erased (Scale m q s) a) (erased (PMul p q r) b) (erased (InsAll Mono s r t) c)
     -> (PMul (Cons Mono m p) q t)))

(def-adts $ (Norm : ((Expr) e) (Poly p) -> Type)
  enum
  (many NVar : (erased (Nat) i) -> (Norm (EVar i) (Cons Mono (Cons (Nat) i (Nil (Nat))) (Nil Mono))))
  (many NNum : (erased (Nat) k) (erased Poly p) (erased (Repeat Mono k (Nil (Nat)) p) r) -> (Norm (ENum k) p))
  (many NAdd : (erased (Expr) a b) (erased Poly pa pb p) (erased (Norm a pa) na) (erased (Norm b pb) nb) (erased (InsAll Mono pa pb p) r)
     -> (Norm (EAdd a b) p))
  (many NMul : (erased (Expr) a b) (erased Poly pa pb p) (erased (Norm a pa) na) (erased (Norm b pb) nb) (erased (PMul pa pb p) r)
     -> (Norm (EMul a b) p)))

(def-adts $ (RingEq : ((Expr) e1) ((Expr) e2) -> Type)
  enum
  (many MkRingEq : (erased (Expr) e1 e2) (erased Poly p) (erased (Norm e1 p) n1) (erased (Norm e2 p) n2) -> (RingEq e1 e2)))

(def-adts $ (Order : (Type A) (A x) (A y) -> Type)
  enum
  (many Before : (erased Type A) (erased A x y) -> (Order A x y))
  (many Same : (erased Type A) (erased A x) -> (Order A x x))
  (many After : (erased Type A) (erased A x y) -> (Order A x y)))

(def-fns _ $ (many nat-order : (many (Nat) x) (many (Nat) y) -> (many (Order (Nat) x y) o))
  (match many (nat-cmp x y) _
    ((CLt _ _ _ _ _) (Before _ x y))
    ((CEq _ _ _) (Same _ x))
    ((CGt _ _ _ _ _) (After _ x y))))

(def-fns _ $ (many lex : (erased Type A) (many (Layer A) l) (subterm many (List A) xs) (many (List A) ys) -> (many (Order (List A) xs ys) o))
  (let-match many xs (Cons _ x xs1)
    ((Nil _) (match many ys _ ((Nil _) (Same _ xs)) ((Cons _ _ _) (Before _ xs ys)))))
  (let-match many ys (Cons _ y ys1) ((Nil _) (After _ xs ys)))
  (let-match many (match many l (((Order A x y) o)) ((Factors) (nat-order x y)) ((Terms) (notail $ lex _ (Factors) x y))) (Same _ _)
    ((Before _ _ _) (Before _ xs ys)) ((After _ _ _) (After _ xs ys)))
  (let-match many (notail $ lex _ l xs1 ys1) (Same _ _) ((Before _ _ _) (Before _ xs ys)) ((After _ _ _) (After _ xs ys)))
  (Same _ xs))

(def-fns _ $ (many after : (erased Type A) (many (Layer A) l) (many A x) (many A y) -> (many (Bool) b))
  (let ((many o)) (match many l (((Order A x y) o)) ((Factors) (nat-order x y)) ((Terms) (lex _ (Factors) x y))))
  (match many o _ ((After _ _ _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many insert : (erased Type A) (many (Layer A) l) (many A x) (subterm many (List A) ys) ->
    (many (List A) zs) (erased (Insert A x ys zs) p))
  (let-match many ys (Cons _ y ys1) ((Nil _) (values (Cons _ x ys) (InsHere _ x ys))))
  (let-match many (after _ l x y) (BTrue) ((BFalse) (values (Cons _ x ys) (InsHere _ x ys))))
  (let ((many zs1) (erased p)) (notail $ insert _ l x ys1))
  (values (Cons _ y zs1) (InsThere _ x y ys1 zs1 p)))

(def-fns _ $ (many insall : (erased Type A) (many (Layer A) l) (subterm many (List A) xs) (many (List A) ys) ->
    (many (List A) zs) (erased (InsAll A xs ys zs) p))
  (let-match many xs (Cons _ x xs1) ((Nil _) (values ys (IANil _ ys))))
  (let ((many ws) (erased p)) (notail $ insall _ l xs1 ys))
  (let ((many zs) (erased q)) (insert _ l x ws))
  (values zs (IACons _ x xs1 ys ws zs p q)))

(def-fns _ $ (many scale : (many Mono m) (subterm many Poly q) -> (many Poly s) (erased (Scale m q s) r))
  (let-match many q (Cons _ n q1) ((Nil _) (values (Nil Mono) (ScNil m))))
  (let ((many mn) (erased p)) (insall _ (Factors) m n))
  (let ((many s) (erased r)) (notail $ scale m q1))
  (values (Cons _ mn s) (ScCons m n mn q1 s p r)))

(def-fns _ $ (many pmul : (subterm many Poly p) (many Poly q) -> (many Poly t) (erased (PMul p q t) r))
  (let-match many p (Cons _ m p1) ((Nil _) (values (Nil Mono) (PMNil q))))
  (let ((many s) (erased a)) (scale m q))
  (let ((many r) (erased b)) (notail $ pmul p1 q))
  (let ((many t) (erased c)) (insall _ (Terms) s r))
  (values t (PMCons m p1 q s r t a b c)))

(def-fns _ $ (many repeat : (erased Type A) (subterm many (Nat) k) (many A x) -> (many (List A) xs) (erased (Repeat A k x xs) r))
  (let-match many k (Succ k1) ((Zero) (values (Nil A) (RepeatNil A x))))
  (let ((many xs) (erased r)) (notail $ repeat A k1 x))
  (values (Cons A x xs) (RepeatCons A k1 x xs r)))

(def-fns _ $ (many norm : (subterm many (Expr) e) -> (many Poly p) (erased (Norm e p) n))
  (match many e _
    ((EVar i) (values (Cons Mono (Cons (Nat) i (Nil (Nat))) (Nil Mono)) (NVar i)))
    ((ENum k)
      (let ((many p) (erased r)) (repeat Mono k (Nil (Nat))))
      (values p (NNum k p r)))
    ((EAdd a b)
      (let ((many pa) (erased na)) (notail $ norm a))
      (let ((many pb) (erased nb)) (notail $ norm b))
      (let ((many p) (erased r)) (insall _ (Terms) pa pb))
      (values p (NAdd a b pa pb p na nb r)))
    ((EMul a b)
      (let ((many pa) (erased na)) (notail $ norm a))
      (let ((many pb) (erased nb)) (notail $ norm b))
      (let ((many p) (erased r)) (pmul pa pb))
      (values p (NMul a b pa pb p na nb r)))))

(def-fns _ $ (many ring-check : (many (Expr) e1) (many (Expr) e2) -> (many (Maybe (RingEq e1 e2)) r))
  (let ((many p1) (erased n1)) (norm e1))
  (let ((many p2) (erased n2)) (norm e2))
  (match many (lex _ (Terms) p1 p2) _
    ((Same _ _) (Some _ (MkRingEq e1 e2 p1 n1 n2)))
    (else (None _))))

(def-fns _ $ (erased neutral-op : (erased Type A) (erased (Layer A) l) (erased (Nat) u b c) (erased (Neutral A l u) p) (erased (Op A l u b c) o) ->
    (erased (Eq (Nat) c b) e))
  (match erased p _
    ((NeutralMul)
      (let-match erased o (OpMul _ _ _ m))
      (let-match erased m (MulSucc _ _ _ _ m0 q))
      (let-match erased m0 (MulZero _))
      (let-match erased q (AddZero _))
      (Refl _ c))
    ((NeutralAdd) (let-match erased o (OpAdd _ _ _ q)) (let-match erased q (AddZero _)) (Refl _ c))))

(def-fns _ $ (erased fold-single : (erased (List (Nat)) env) (erased Type A) (erased (Layer A) l) (erased A x) (erased (Nat) n)
    (erased (Val env A l x n) v) -> (erased (Fold env A l (Cons A x (Nil A)) n) f))
  (match erased l _
    ((Factors) (FoldCons env A l x (Nil A) n (Succ (Zero)) n v (FoldNil env A l _ (NeutralMul))
      (OpMul n (Succ (Zero)) n (mul-comm _ _ _ (MulSucc (Zero) n (Zero) n (MulZero n) (AddZero n))))))
    ((Terms) (FoldCons env A l x (Nil A) n (Zero) n v (FoldNil env A l _ (NeutralAdd)) (OpAdd n (Zero) n (add-zero-right n))))))

(def-fns _ $ (erased insert-sound : (erased (List (Nat)) env) (erased Type A) (erased (Layer A) l) (erased A x) (erased (List A) ys zs) (erased (Nat) a b c)
    (subterm erased (Insert A x ys zs) p) (erased (Val env A l x a) v) (erased (Fold env A l ys b) f) (erased (Op A l a b c) o) ->
    (erased (Fold env A l zs c) g))
  (let-match erased p (InsThere _ _ y ys1 zs1 p1) ((InsHere _ _ _) (FoldCons env A l x ys a b c v f o)))
  (let-match erased f (FoldCons _ _ _ _ _ vy bt _ fy ft oy))
  (let ((erased d) (erased od)) (op-total A l a bt))
  (FoldCons env A l y zs1 vy d c fy (insert-sound env A l x ys1 zs1 a bt d p1 v ft od) (op-swap A l vy bt b a c d oy o od)))

(def-fns _ $ (erased insall-sound : (erased (List (Nat)) env) (erased Type A) (erased (Layer A) l) (erased (List A) xs ys zs) (erased (Nat) a b c)
    (subterm erased (InsAll A xs ys zs) p) (erased (Fold env A l xs a) f) (erased (Fold env A l ys b) g) (erased (Op A l a b c) o) ->
    (erased (Fold env A l zs c) h))
  (let-match erased p (IACons _ x xs1 _ ws _ p1 q)
    ((IANil _ _) (let-match erased f (FoldNil _ _ _ _ u)) (let-match erased (neutral-op A l a b c u o) (Refl _ _)) g))
  (let-match erased f (FoldCons _ _ _ _ _ vx a1 _ fx f1 ox))
  (let ((erased w) (erased ow) (erased oc)) (op-assoc A l vx a1 b a c ox o))
  (insert-sound env A l x ws zs vx w c q fx (insall-sound env A l xs1 ys ws a1 b w p1 f1 g ow) oc))

(def-fns _ $ (erased mul-distl : (erased (Nat) a b s c ca cb cs) (erased (Add a b s) p)
    (erased (Mul c a ca) ma) (erased (Mul c b cb) mb) (erased (Mul c s cs) ms) -> (erased (Add ca cb cs) r))
  (mul-distr a b s c ca cb cs p (mul-comm _ _ _ ma) (mul-comm _ _ _ mb) (mul-comm _ _ _ ms)))

(def-fns _ $ (erased scale-sound : (erased (List (Nat)) env) (erased Mono m) (erased Poly q s) (erased (Nat) vm y z)
    (subterm erased (Scale m q s) p) (erased (Fold env (Nat) (Factors) m vm) fm) (erased (Fold env Mono (Terms) q y) fq) (erased (Mul vm y z) mz)
    -> (erased (Fold env Mono (Terms) s z) g))
  (let-match erased p (ScCons _ n mn q1 s1 ip r)
    ((ScNil _)
      (let-match erased fq (FoldNil _ _ _ _ u))
      (let-match erased u (NeutralAdd))
      (let-match erased (mul-fn _ _ _ _ mz (mul-zero-right vm)) (Refl _ _))
      (FoldNil env Mono (Terms) _ (NeutralAdd))))
  (let-match erased fq (FoldCons _ _ _ _ _ vn y1 _ vfn fq1 on))
  (let-match erased vfn (ValMono _ _ _ fn))
  (let-match erased on (OpAdd _ _ _ an))
  (let ((erased t) (erased mt)) (mul vm vn))
  (let ((erased z1) (erased mz1)) (mul vm y1))
  (FoldCons env Mono (Terms) mn s1 t z1 z
    (ValMono env mn t (insall-sound env (Nat) (Factors) m n mn vm vn t ip fm fn (OpMul vm vn t mt)))
    (scale-sound env m q1 s1 vm y1 z1 r fm fq1 mz1)
    (OpAdd t z1 z (mul-distl vn y1 y vm t z1 z an mt mz1 mz))))

(def-fns _ $ (erased pmul-sound : (erased (List (Nat)) env) (erased Poly p q r) (erased (Nat) x y n)
    (subterm erased (PMul p q r) pm) (erased (Fold env Mono (Terms) p x) fp) (erased (Fold env Mono (Terms) q y) fq) (erased (Mul x y n) mn)
    -> (erased (Fold env Mono (Terms) r n) g))
  (let-match erased pm (PMCons m p1 _ s r1 _ sc pm1 ia)
    ((PMNil _)
      (let-match erased fp (FoldNil _ _ _ _ u))
      (let-match erased u (NeutralAdd))
      (let-match erased mn (MulZero _))
      (FoldNil env Mono (Terms) _ (NeutralAdd))))
  (let-match erased fp (FoldCons _ _ _ _ _ vm x1 _ vfm fp1 om))
  (let-match erased vfm (ValMono _ _ _ fm))
  (let-match erased om (OpAdd _ _ _ am))
  (let ((erased z) (erased mz)) (mul vm y))
  (let ((erased w) (erased mw)) (mul x1 y))
  (insall-sound env Mono (Terms) s r1 r z w n ia (scale-sound env m q s vm y z sc fm fq mz) (pmul-sound env p1 q r1 x1 y w pm1 fp1 fq mw)
    (OpAdd z w n (mul-distr vm x1 x y z w n am mz mw mn))))

(def-fns _ $ (erased repeat-sound : (erased (List (Nat)) env) (erased (Nat) k) (erased Poly p) (subterm erased (Repeat Mono k (Nil (Nat)) p) r) ->
    (erased (Fold env Mono (Terms) p k) f))
  (let-match erased r (RepeatCons _ k1 _ p1 r1) ((RepeatNil _ _) (FoldNil env Mono (Terms) _ (NeutralAdd))))
  (FoldCons env Mono (Terms) (Nil (Nat)) p1 (Succ (Zero)) k1 k (ValMono env (Nil (Nat)) _ (FoldNil env (Nat) (Factors) _ (NeutralMul)))
    (repeat-sound env k1 p1 r1) (OpAdd _ _ _ (AddSucc (Zero) k1 k1 (AddZero k1)))))

(def-fns _ $ (erased eval-norm : (erased (List (Nat)) env) (erased (Expr) e) (erased Poly p) (erased (Nat) n) (subterm erased (Norm e p) nm)
    (erased (Eval env e n) ev) -> (erased (Fold env Mono (Terms) p n) f))
  (match erased nm _
    ((NVar i)
      (let-match erased ev (EvVar _ _ _ q))
      (fold-single env Mono (Terms) _ n (ValMono env _ n (fold-single env (Nat) (Factors) i n (ValVar env i n q)))))
    ((NNum k _ r) (let-match erased ev (EvNum _ _)) (repeat-sound env k p r))
    ((NAdd a b pa pb _ na nb r)
      (let-match erased ev (EvAdd _ _ _ x y _ ea eb q))
      (insall-sound env Mono (Terms) pa pb p x y n r (eval-norm env a pa x na ea) (eval-norm env b pb y nb eb) (OpAdd x y n q)))
    ((NMul a b pa pb _ na nb r)
      (let-match erased ev (EvMul _ _ _ x y _ ea eb q))
      (pmul-sound env pa pb p x y n r (eval-norm env a pa x na ea) (eval-norm env b pb y nb eb) q))))

(def-fns _
  ((erased val-fn : (erased (List (Nat)) env) (erased Type A) (erased (Layer A) l) (erased A x) (erased (Nat) a b)
      (subterm erased (Val env A l x a) v) (erased (Val env A l x b) w) -> (erased (Eq (Nat) a b) e))
    (match erased v _
      ((ValVar _ i _ p) (let-match erased w (ValVar _ _ _ q)) (nth-fn (Nat) env i a b p q))
      ((ValMono _ m _ p) (let-match erased w (ValMono _ _ _ q)) (fold-fn env (Nat) (Factors) m a b p q))))
  ((erased fold-fn : (erased (List (Nat)) env) (erased Type A) (erased (Layer A) l) (erased (List A) xs) (erased (Nat) a b)
      (subterm erased (Fold env A l xs a) f) (erased (Fold env A l xs b) g) -> (erased (Eq (Nat) a b) e))
    (match erased f _
      ((FoldNil _ _ _ _ u)
        (let-match erased g (FoldNil _ _ _ _ u2))
        (match erased u _
          ((NeutralMul) (let-match erased u2 (NeutralMul)) (Refl _ a))
          ((NeutralAdd) (let-match erased u2 (NeutralAdd)) (Refl _ a))))
      ((FoldCons _ _ _ x xs1 a1 b1 _ v f1 o)
        (let-match erased g (FoldCons _ _ _ _ _ a2 b2 _ v2 f2 o2))
        (let-match erased (val-fn env A l x a1 a2 v v2) (Refl _ _))
        (let-match erased (fold-fn env A l xs1 b1 b2 f1 f2) (Refl _ _))
        (op-fn A l a1 b1 a b o o2)))))

(def-fns _ $ (erased ring-sound : (erased (List (Nat)) env) (erased (Expr) e1 e2) (erased (Nat) n1 n2) (erased (RingEq e1 e2) r)
    (erased (Eval env e1 n1) v1) (erased (Eval env e2 n2) v2) -> (erased (Eq (Nat) n1 n2) e))
  (let-match erased r (MkRingEq _ _ p m1 m2))
  (fold-fn env Mono (Terms) p n1 n2 (eval-norm env e1 p n1 m1 v1) (eval-norm env e2 p n2 m2 v2)))

(def-fns _ $ (erased eval-fn : (erased (List (Nat)) env) (erased (Expr) e) (erased (Nat) n1 n2)
    (erased (Eval env e n1) v1) (erased (Eval env e n2) v2) -> (erased (Eq (Nat) n1 n2) r))
  (let ((erased p) (erased m)) (norm e))
  (ring-sound env e e n1 n2 (MkRingEq e e p m m) v1 v2))

(def-fns _ $ (erased ev-add : (erased (List (Nat)) env) (erased (Expr) a b) (erased (Nat) x y) (erased (Eval env a x) ea) (erased (Eval env b y) eb) ->
    (erased (Nat) n) (erased (Add x y n) p) (erased (Eval env (EAdd a b) n) e))
  (let ((erased n) (erased p)) (add x y))
  (values n p (EvAdd env a b x y n ea eb p)))

(def-fns _ $ (erased ev-mul : (erased (List (Nat)) env) (erased (Expr) a b) (erased (Nat) x y) (erased (Eval env a x) ea) (erased (Eval env b y) eb) ->
    (erased (Nat) n) (erased (Mul x y n) p) (erased (Eval env (EMul a b) n) e))
  (let ((erased n) (erased p)) (mul x y))
  (values n p (EvMul env a b x y n ea eb p)))

(def-fns _ $ (erased add-mono-lt : (erased (Nat) a b c x y) (subterm erased (Lt a b) l) (erased (Add a c x) p) (erased (Add b c y) q) ->
    (erased (Lt x y) r))
  (let-match erased l (LtS a1 b1 l1)
    ((LtZ b1) (let-match erased p (AddZero _)) (let-match erased q (AddSucc _ _ y1 q1)) (add-le-right b1 c y1 q1)))
  (let-match erased p (AddSucc _ _ x1 p1))
  (let-match erased q (AddSucc _ _ y1 q1))
  (LtS x1 y1 (add-mono-lt a1 b1 c x1 y1 l1 p1 q1)))

(def-fns _ $ (erased add-mono-le : (erased (Nat) b c d y z) (erased (Lt c (Succ d)) l) (subterm erased (Add b c y) p) (erased (Add b d z) q) ->
    (erased (Lt y (Succ z)) r))
  (let-match erased p (AddSucc b1 _ y1 p1) ((AddZero _) (let-match erased q (AddZero _)) l))
  (let-match erased q (AddSucc _ _ z1 q1))
  (LtS y1 (Succ z1) (add-mono-le b1 c d y1 z1 l p1 q1)))

(def-fns _ $ (erased add-lt : (erased (Nat) a b c d x y) (erased (Lt a b) l) (erased (Lt c (Succ d)) k) (erased (Add a c x) p) (erased (Add b d y) q) ->
    (erased (Lt x y) r))
  (let ((erased w) (erased o)) (add b c))
  (lt-le-trans x w y (add-mono-lt a b c x w l p o) (add-mono-le b c d w y k o q)))

(def-fns _ $ (erased add-cancel-lt : (erased (Nat) a b c d x) (erased (Add a b x) p) (erased (Add c d x) q) (erased (Lt b d) l) -> (erased (Lt c a) r))
  (match erased (lt-dec c a) _
    ((Yes _ _ _ _ r) r)
    (absurd (No _ _ _ _ le) (lt-irrefl x (add-lt b d a c x x l (le-lt-succ a c le) (add-comm a b x p) (add-comm c d x q))))))

(def-fns _ $ (erased lt-diff : (erased (Nat) b a) (subterm erased (Lt b a) l) -> (erased (Nat) x) (erased (Add b (Succ x) a) p))
  (let-match erased l (LtS b1 a1 l1) ((LtZ a1) (values a1 (AddZero a))))
  (let ((erased x) (erased p)) (lt-diff b1 a1 l1))
  (values x (AddSucc b1 (Succ x) a1 p)))
