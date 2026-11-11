(def-adts $ (LexPos : ((Nat) n) ((Nat) p) ((List (Nat)) a) ((List (Nat)) b) -> Type)
  enum
  (many LPHead : (erased (Nat) n) (erased (Nat) h2) (erased (Nat) h) (erased (Lt h2 h) lt)
     (erased (List (Nat)) t2) (erased (List (Nat)) t) -> (LexPos (Succ n) (Zero) (Cons (Nat) h2 t2) (Cons (Nat) h t)))
  (many LPTail : (erased (Nat) n) (erased (Nat) p) (erased (Nat) h) (erased (List (Nat)) t2) (erased (List (Nat)) t)
     (erased (LexPos n p t2 t) lp) -> (LexPos (Succ n) (Succ p) (Cons (Nat) h t2) (Cons (Nat) h t))))

; S : the state type, indexed by its measure v; R : the result type; n : the measure's length.
(def-adts $ (Step : ((TyCtor ((List (Nat)) v) -> Type) S) (Type R) ((Nat) n) ((List (Nat)) v) -> Type)
  enum
  (many Done : (erased (TyCtor ((List (Nat)) v) -> Type) S) (erased Type R) (erased (Nat) n) (erased (List (Nat)) v)
     (many R r) -> (Step S R n v))
  (many Next : (erased (TyCtor ((List (Nat)) v) -> Type) S) (erased Type R) (erased (Nat) n) (erased (List (Nat)) v)
     (erased (List (Nat)) v2) (many (S v2) s) (many (Nat) p) (erased (LexPos n p v2 v) lp)
     (erased (Length (Nat) v2 n) ln) -> (Step S R n v)))

; q : the position the run is at; an exit decreased the measure at a position p before it.
(def-adts $ (Out : ((TyCtor ((List (Nat)) v) -> Type) S) (Type R) ((Nat) n) ((Nat) q) ((List (Nat)) v) -> Type)
  enum
  (many OutDone : (erased (TyCtor ((List (Nat)) v) -> Type) S) (erased Type R) (erased (Nat) n) (erased (Nat) q)
     (erased (List (Nat)) v) (many R r) -> (Out S R n q v))
  (many OutExit : (erased (TyCtor ((List (Nat)) v) -> Type) S) (erased Type R) (erased (Nat) n) (erased (Nat) q)
     (erased (List (Nat)) v) (erased (List (Nat)) v2) (many (S v2) s) (many (Nat) p) (erased (Lt p q) pq)
     (erased (LexPos n p v2 v) lp) (erased (Length (Nat) v2 n) ln) -> (Out S R n q v)))

(def-fns _ $ (erased lexpos-lt : (erased (Nat) n p) (erased (List (Nat)) a b) (subterm erased (LexPos n p a b) lp) ->
    (erased (Lt p n) l))
  (match erased lp _
    ((LPHead n1 _ _ _ _ _) (LtZ n1))
    ((LPTail n1 p1 _ t2 t l1) (LtS p1 n1 (lexpos-lt n1 p1 t2 t l1)))))

(def-fns _ $ (erased lexpos-at : (erased (Nat) n p) (erased (List (Nat)) a b) (subterm erased (LexPos n p a b) lp)
    (erased (Nat) h) (erased (Nth (Nat) b p h) nb) -> (erased (Nat) h2) (erased (Nth (Nat) a p h2) na) (erased (Lt h2 h) l))
  (match erased lp _
    ((LPHead _ h2 _ l t2 _)
      (let-match erased nb (NthHere _ _ _))
      (values h2 (NthHere (Nat) h2 t2) l))
    ((LPTail n1 p1 x t2 t l1)
      (let-match erased nb (NthThere _ _ _ _ _ nb1))
      (let ((erased h2) (erased na) (erased l)) (lexpos-at n1 p1 t2 t l1 h nb1))
      (values h2 (NthThere (Nat) x t2 p1 h2 na) l))))

(def-fns _ $ (erased lexpos-compose : (erased (Nat) n p q) (erased (List (Nat)) a b c)
    (subterm erased (LexPos n p c b) l1) (erased (LexPos n q b a) l2) (erased (Lt p q) pq) -> (erased (LexPos n p c a) l))
  (match erased l1 _
    ((LPHead n1 h2 _ lt t2 _)
      (let-match erased l2 (LPTail _ _ _ _ t _) (absurd (LPHead _ _ _ _ _ _) pq))
      (LPHead n1 h2 _ lt t2 t))
    ((LPTail n1 p1 x t2 t l3)
      (let-match erased l2 (LPTail _ q1 _ _ t0 l4) (absurd (LPHead _ _ _ _ _ _) pq))
      (let-match erased pq (LtS _ _ pq1))
      (LPTail n1 p1 x t2 t0 (lexpos-compose n1 p1 q1 t0 t t2 l3 l4 pq1)))))

; The factory: M is the level of the step functions the runner accepts.
(def-fns _ $ (many lex-factory : (erased (Level) M) ->
    (erased (Level) L)
    (many (Fn L (erased (TyCtor ((List (Nat)) v) -> Type) S) (erased Type R) (many (Nat) k)
              (many (Fn M (erased (List (Nat)) v) (many (S v) s) -> (many (Step S R (Succ k) v) o)) step)
              (erased (List (Nat)) v) (erased (Length (Nat) v (Succ k)) ln) (many (S v) s) -> (many R r)) run))
  (def-fns _ $ (many go : (erased (TyCtor ((List (Nat)) v) -> Type) S) (erased Type R) (erased (Nat) n)
      (many (Fn M (erased (List (Nat)) v) (many (S v) s) -> (many (Step S R n v) o)) step)
      (subterm many (Nat) k) (subterm erased (Nat) h) (many (Nat) q) (erased (Add k (Succ q) n) a)
      (erased (List (Nat)) v) (erased (Length (Nat) v n) ln) (erased (Nth (Nat) v q h) nh) (many (S v) s) ->
      (many (Out S R n q v) o))
    (let ((many inner))
      (match many k (((Out S R n (Succ q) v) o))
        ((Zero)
          (let-match erased a (AddZero _))
          (match many (step v s) _
            ((Done _ _ _ _ r) (OutDone S R n (Succ q) v r))
            ((Next _ _ _ _ v2 s2 p lp ln2) (OutExit S R n (Succ q) v v2 s2 p (lexpos-lt n p v2 v lp) lp ln2))))
        ((Succ k1)
          (let-match erased a (AddSucc _ _ c a1))
          (let ((erased h1) (erased nh1)) (nth-exists (Nat) v n (Succ q) ln (add-le-right k1 (Succ q) c a1)))
          (notail $ go S R n step k1 h1 (Succ q) (add-succ-right k1 (Succ q) c a1) v ln nh1 s))))
    (let-match many inner (OutExit _ _ _ _ _ v2 s2 p pq lp ln2) ((OutDone _ _ _ _ _ r) (OutDone S R n q v r)))
    (let-match many (nat-cmp p q) (CEq _ _ _)
      ((CLt _ _ _ _ l) (OutExit S R n q v v2 s2 p l lp ln2))
      (absurd (CGt _ _ _ _ l) (lt-asym q p l pq)))
    (let ((erased h2) (erased nh2) (erased l)) (lexpos-at n q v2 v lp h nh))
    (let-match many (notail $ go S R n step k (subterm (lt-subterm h2 h l)) h2 q a v2 ln2 nh2 s2)
      (OutExit _ _ _ _ _ v3 s3 p3 pq3 lp3 ln3)
      ((OutDone _ _ _ _ _ r) (OutDone S R n q v r)))
    (OutExit S R n q v v3 s3 p3 pq3 (lexpos-compose n p3 q v v2 v3 lp3 lp pq3) ln3))
  (def-fns _ $ (many run : (erased (TyCtor ((List (Nat)) v) -> Type) S) (erased Type R) (many (Nat) k)
      (many (Fn M (erased (List (Nat)) v) (many (S v) s) -> (many (Step S R (Succ k) v) o)) step)
      (erased (List (Nat)) v) (erased (Length (Nat) v (Succ k)) ln) (many (S v) s) -> (many R r))
    (let ((erased h0) (erased nh0)) (nth-exists (Nat) v (Succ k) (Zero) ln (LtZ k)))
    (let-match many (go S R (Succ k) step k h0 (Zero) (add-succ-right k (Zero) k (add-zero-right k)) v ln nh0 s)
      (OutDone _ _ _ _ _ r)
      (absurd (OutExit _ _ _ _ _ _ _ _ pq _ _) pq))
    r)
  (values (level-of run) run))

(def-fns _ $ (many list-len : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n) (erased (Length A xs n) l))
  (let-match many xs (Cons _ y ys) ((Nil _) (values (Zero) (LengthNil A))))
  (let ((many n) (erased l)) (notail $ list-len A ys))
  (values (Succ n) (LengthCons A y ys n l)))
