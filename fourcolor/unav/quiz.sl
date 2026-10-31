(def-adts $ (Qn : -> Type)
  enum
  (many Qask0 : -> (Qn))
  (many Qask1 : (many (Nat) qa) -> (Qn))
  (many QaskL : (many (Nat) qa) (many (Qn) q) -> (Qn))
  (many QaskR : (many (Nat) qa) (many (Qn) q) -> (Qn))
  (many QaskLR : (many (Nat) qa) (many (Qn) ql qr) -> (Qn))
  (many QaskLL : (many (Nat) qa) (many (Qn) q) -> (Qn))
  (many QaskRR : (many (Nat) qa) (many (Qn) q) -> (Qn)))

(def-adts $ (Quiz : -> Type)
  enum
  (many MkQuiz : (many (Qn) q0 q1) -> (Quiz)))

(def-adts $ (Qzt : -> Type)
  enum
  (many QztNil : -> (Qzt))
  (many QztLeaf : (many (Qn) q1 q2 q3) (many (Qzt) t) -> (Qzt))
  (many QztNode : (many (Qzt) t5 t6 t7 t8) -> (Qzt))
  (many QztHub : (many (Qzt) t58 t9 t10 t11) -> (Qzt)))

(def-adts $ (Rq : -> Type)
  enum
  (many MkRq : (many (Bool) k) (many (Nat) a) (many (Qn) q) -> (Rq)))

(let ((many noquiz)) (MkQuiz (Qask0) (Qask0)))

(def-fns _ $ (many small-qarity : (many (Nat) a) -> (many (Nat) qa))
  (match many (andb (nat-ltb 2 a) (nat-ltb a 7)) _
    ((BTrue) (Succ $ Succ a))
    ((BFalse) (bif _ (nat-eqb a 7) 10 9))))

(def-fns _ $ (many large-qarity : (many (Nat) a) -> (many (Nat) qa))
  (bif _ (andb (nat-ltb 6 a) (nat-ltb a 10)) (Succ $ Succ a) (small-qarity a)))

(def-fns _ $ (many bad-small : (many (Nat) qa) -> (many (Bool) b))
  (nat-ltb 8 qa))

(def-fns _ $ (many bad-ring : (many (Nat) a) -> (many (Bool) b))
  (orb (nat-eqb a 0) (nat-ltb 4 a)))

(def-fns _ $ (many is-q0 : (many (Qn) q) -> (many (Bool) b))
  (match many q _ ((Qask0) (BTrue)) (else (BFalse))))

(def-fns _ $ (many cfquiz-Y : (many (Rq) rq1 rq2) -> (many (Bool) ok) (many (Qn) q))
  (let-match many rq1 (MkRq _ _ q1))
  (let-match many rq2 (MkRq k2 a2 q2))
  (match many k2 _
    ((BTrue)
      (let ((many qa2)) (small-qarity a2))
      (let-match many (bad-small qa2) (BFalse) ((BTrue) (values (BFalse) (Qask0))))
      (values (BTrue)
        (match many (is-q0 q1) _
          ((BTrue) (bif _ (is-q0 q2) (Qask1 qa2) (QaskL qa2 q2)))
          ((BFalse) (bif _ (is-q0 q2) (QaskR qa2 q1) (QaskLR qa2 q2 q1))))))
    ((BFalse)
      (let-match many (bad-ring a2) (BFalse) ((BTrue) (values (BFalse) (Qask0))))
      (match many q1 _
        ((Qask0) (match many q2 _ ((Qask0) (values (BTrue) (Qask0))) ((QaskL qa1 q1l) (values (BTrue) (QaskLL qa1 q1l))) (else (values (BFalse) (Qask0)))))
        ((QaskR qa1 q1r) (match many (is-q0 q2) _ ((BTrue) (values (BTrue) (QaskRR qa1 q1r))) ((BFalse) (values (BFalse) (Qask0)))))
        (else (values (BFalse) (Qask0)))))))

(def-fns _ $ (many cfquiz-H : (many (Rq) rq1 rq2) -> (many (Bool) ok) (many (Qn) r1 r2))
  (let-match many rq1 (MkRq k1 _ q1))
  (let-match many rq2 (MkRq k2 a2 q2))
  (match many k2 _
    ((BTrue)
      (let ((many qa2)) (small-qarity (Succ a2)))
      (let-match many (bad-small qa2) (BFalse) ((BTrue) (values (BFalse) (Qask0) (Qask0))))
      (let-match many (is-q0 q1) (BTrue)
        ((BFalse) (match many (is-q0 q2) _ ((BTrue) (values (BTrue) (QaskR qa2 q1) q2)) ((BFalse) (values (BFalse) (Qask0) (Qask0))))))
      (let-match many (is-q0 q2) (BTrue) ((BFalse) (values (BTrue) q1 (QaskL qa2 q2))))
      (match many k1 _ ((BTrue) (values (BTrue) (Qask1 qa2) q2)) ((BFalse) (values (BTrue) q1 (Qask1 qa2)))))
    ((BFalse)
      (let-match many (bad-ring (Succ a2)) (BFalse) ((BTrue) (values (BFalse) (Qask0) (Qask0))))
      (match many (andb (is-q0 q1) (is-q0 q2)) _ ((BTrue) (values (BTrue) q1 q2)) ((BFalse) (values (BFalse) (Qask0) (Qask0)))))))

(def-fns _ $ (many cfquiz-final : (many (Rq) rq1 rq2) -> (many (Quiz) qz))
  (let-match many rq1 (MkRq k1 a1 q1))
  (let-match many rq2 (MkRq k2 a2 q2))
  (let-match many (andb k1 k2) (BTrue) ((BFalse) noquiz))
  (let ((many qa1) (many qa2)) (values (large-qarity (monus a1 1)) (small-qarity (monus a2 1))))
  (bif _ (orb (negb (nat-eqb qa1 (Succ a1))) (bad-small qa2)) noquiz (MkQuiz (QaskR qa1 q2) (QaskR qa2 q1))))

(def-fns _ $ (many cfquiz-rec : (many (List (Rq)) qs) (subterm many (List (Step)) cp) -> (many (Quiz) qz))
  (let-match many qs (Cons _ rq1 qs1) ((Nil _) noquiz))
  (let-match many qs1 (Cons _ rq2 qs2) ((Nil _) noquiz))
  (let-match many cp (Cons _ s cp1) ((Nil _) (cfquiz-final rq1 rq2)))
  (let-match many qs2 (Cons _ rq3 qs3) ((Nil _) noquiz))
  (let-match many rq1 (MkRq k1 a1 _))
  (let-match many rq3 (MkRq k3 a3 q3))
  (match many s _
    ((SR n) (tail $ cfquiz-rec (rotr _ n qs) cp1))
    ((SY)
      (let ((many ok) (many q)) (cfquiz-Y rq1 rq2))
      (let-match many ok (BTrue) ((BFalse) noquiz))
      (tail $ cfquiz-rec (Cons _ (MkRq k1 (Succ a1) q) $ Cons _ (MkRq k3 (Succ a3) q3) qs3) cp1))
    ((SH)
      (let ((many ok) (many r1) (many r2)) (cfquiz-H rq1 rq2))
      (let-match many ok (BTrue) ((BFalse) noquiz))
      (tail $ cfquiz-rec (Cons _ (MkRq k1 (Succ a1) r1) $ Cons _ (MkRq (BTrue) 1 r2) $ Cons _ (MkRq k3 (Succ a3) q3) qs3) cp1))
    (else noquiz)))

(def-fns _ $ (many cpradius2 : (many (List (Step)) cp) (subterm many (Nat) i) -> (many (Bool) b))
  (let-match many i (Succ i1) ((Zero) (BFalse)))
  (let ((many mr1)) (nseq _ (cprsize cp) (BFalse)))
  (let ((many _m) (many mk1)) (cpadj mr1 (ctrmask (Cons _ i1 $ Nil _) 0 (cpksize cp)) cp))
  (let ((many _m2) (many mk2)) (cpadj mr1 mk1 cp))
  (match many (nat-eqb 0 $ count-b (BFalse) mk2) _ ((BTrue) (BTrue)) ((BFalse) (tail $ cpradius2 cp i1))))

(def-fns _ $ (many cfquiz : (many (Config) cf) -> (many (Quiz) qz))
  (let-match many cf (MkConfig _ _ cp))
  (match many (cpradius2 cp (cpksize cp)) _
    ((BTrue) (cfquiz-rec (nseq _ (cprsize cp) (MkRq (BFalse) 0 (Qask0))) cp))
    ((BFalse) noquiz)))
