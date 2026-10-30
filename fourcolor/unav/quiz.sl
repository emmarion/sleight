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

(def-adts $ (Ix : -> Type)
  enum
  (many I0 : -> (Ix))
  (many I1 : -> (Ix))
  (many I2 : -> (Ix))
  (many I3 : -> (Ix))
  (many IX : -> (Ix)))

(def-adts $ (Rq : -> Type)
  enum
  (many MkRq : (many (Bool) k) (many (Nat) a) (many (Qn) q) -> (Rq)))

(def-fns _ $ (many ix-of : (many (Nat) a base) -> (many (Ix) i))
  (let-match many (nat-ltb a base) (BFalse) ((BTrue) (IX)))
  (let ((many d)) (monus a base))
  (let-match many d (Succ d1) ((Zero) (I0)))
  (let-match many d1 (Succ d2) ((Zero) (I1)))
  (let-match many d2 (Succ d3) ((Zero) (I2)))
  (bif _ (nat-eqb d3 0) (I3) (IX)))

(def-fns _ $ (many ix-hub : (many (Nat) a) -> (many (Ix) i))
  (let ((many i)) (ix-of a 8))
  (match many i _ ((IX) (I0)) (else i)))

(def-fns _ $ (many flipq : (subterm many (Qn) q) -> (many (Qn) r))
  (match many q _
    ((QaskL a l) (QaskR a $ notail $ flipq l))
    ((QaskR a r) (QaskL a $ notail $ flipq r))
    ((QaskLR a l r) (QaskLR a (notail $ flipq r) (notail $ flipq l)))
    ((QaskLL a l) (QaskRR a $ notail $ flipq l))
    ((QaskRR a r) (QaskLL a $ notail $ flipq r))
    (else q)))

(def-fns _ $ (many flipqz : (many (Quiz) qz) -> (many (Quiz) r))
  (let-match many qz (MkQuiz a b))
  (let-match many a (QaskR qa0 q01) (else qz))
  (let-match many b (QaskR qa1 q10) (else qz))
  (MkQuiz (QaskR qa0 (flipq q10)) (QaskR qa1 (flipq q01))))

(def-fns _ $ (many qzt-put : (subterm many (List (Nat)) path) (subterm many (Qzt) t) (many (Qn) q1 q2 q3) -> (many (Qzt) r))
  (let-match many path (Cons _ a rest) ((Nil _) (QztLeaf q1 q2 q3 t)))
  (match many t _
    ((QztNode t5 t6 t7 t8)
      (match many (ix-of a 5) _
        ((I0) (QztNode (notail $ qzt-put rest t5 q1 q2 q3) t6 t7 t8))
        ((I1) (QztNode t5 (notail $ qzt-put rest t6 q1 q2 q3) t7 t8))
        ((I2) (QztNode t5 t6 (notail $ qzt-put rest t7 q1 q2 q3) t8))
        ((I3) (QztNode t5 t6 t7 (notail $ qzt-put rest t8 q1 q2 q3)))
        ((IX) t)))
    ((QztHub t58 t9 t10 t11)
      (match many (ix-hub a) _
        ((I0) (QztHub (notail $ qzt-put path t58 q1 q2 q3) t9 t10 t11))
        ((I1) (QztHub t58 (notail $ qzt-put rest t9 q1 q2 q3) t10 t11))
        ((I2) (QztHub t58 t9 (notail $ qzt-put rest t10 q1 q2 q3) t11))
        ((I3) (QztHub t58 t9 t10 (notail $ qzt-put rest t11 q1 q2 q3)))
        ((IX) t)))
    (else t)))

(def-fns _ $ (many qzt-get1 : (many (Nat) a) (subterm many (Qzt) t) -> (many (Qzt) r))
  (match many t _
    ((QztNode t5 t6 t7 t8) (match many (ix-of a 5) _ ((I0) t5) ((I1) t6) ((I2) t7) ((I3) t8) ((IX) (QztNil))))
    ((QztHub t58 t9 t10 t11) (match many (ix-hub a) _ ((I0) (tail $ qzt-get1 a t58)) ((I1) t9) ((I2) t10) ((I3) t11) ((IX) (QztNil))))
    (else (QztNil))))

(def-fns _ $ (many qzt-put3 : (many (Nat) a1 a2 a3) (many (Qn) q1 q2 q3) (many (Qzt) t) -> (many (Qzt) r))
  (qzt-put (Cons _ a1 $ Cons _ a2 $ Cons _ a3 $ Nil _) t q1 q2 q3))

(def-fns _ $ (many qzt-put-rot : (many (Nat) a1 a2 a3) (many (Qn) q1 q2 q3) (many (Qzt) t) -> (many (Qzt) r))
  (match many (nat-ltb 8 a1) _
    ((BTrue) (qzt-put3 a1 a2 a3 q1 q2 q3 t))
    ((BFalse) (qzt-put3 a1 a2 a3 q1 q2 q3 $ qzt-put3 a2 a3 a1 q2 q3 q1 $ qzt-put3 a3 a1 a2 q3 q1 q2 t))))

(def-fns _ $ (many normq : (many (Qn) q) -> (many (Qn) r))
  (match many q _
    ((Qask1 a) (QaskLR a (Qask0) (Qask0)))
    ((QaskL a l) (QaskLR a l (Qask0)))
    ((QaskR a r) (QaskLR a (Qask0) r))
    (else q)))

(def-fns _ $ (many store-qz : (many (Quiz) qz) (many (Qzt) t) -> (many (Qzt) r))
  (let-match many qz (MkQuiz a b))
  (let-match many a (QaskR qa1 q1) (else t))
  (let-match many b (QaskR qa2 q2) (else t))
  (let ((many n1) (many n2)) (values (normq q1) (normq q2)))
  (match many n1 _
    ((QaskLR qa1r q1l q1r)
      (let-match many n2 (QaskLR qa2r q2l q2r) (else (qzt-put-rot qa1 qa2 qa1r q1l q2 q1r t)))
      (match many (nat-ltb qa1r qa2r) _
        ((BTrue) (qzt-put-rot qa1 qa2 qa1r q1l q2 q1r t))
        ((BFalse) (qzt-put-rot qa1 qa2r qa2 q1 q2r q2l t))))
    (else
      (let-match many n2 (QaskLR qa2r q2l q2r) (else t))
      (qzt-put-rot qa1 qa2r qa2 q1 q2r q2l t))))

(def-fns _ $ (many store-cf-qz : (many (Quiz) qz) (many (Bool) sym) (many (Qzt) t) -> (many (Qzt) r))
  (store-qz qz (match many sym _ ((BTrue) t) ((BFalse) (store-qz (flipqz qz) t)))))

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

(def-fns _ $ (many cfquiz-tree-rec : (many (Qzt) qt) (subterm many (List (Config)) cfs) -> (many (Qzt) r))
  (let-match many cfs (Cons _ cf rest) ((Nil _) qt))
  (let-match many cf (MkConfig sym _ _))
  (let ((many qt1)) (store-cf-qz (cfquiz cf) sym qt))
  (match many qt1 _ ((QztHub _ _ _ _) (tail $ cfquiz-tree-rec qt1 rest)) (else (QztNil))))

(def-fns _ $ (many qzt-empty : -> (many (Qzt) t))
  (let ((many n1)) (QztNode (QztNil) (QztNil) (QztNil) (QztNil)))
  (let ((many n2)) (QztNode n1 n1 n1 n1))
  (QztHub (QztNode n2 n2 n2 n2) n2 n2 n2))

(def-fns _ $ (many qzt-size : (subterm many (Qzt) t) -> (many (Nat) n))
  (match many t _
    ((QztLeaf _ _ _ t1) (Succ $ notail $ qzt-size t1))
    ((QztNode a b c d) (nat-add (notail $ qzt-size a) $ nat-add (notail $ qzt-size b) $ nat-add (notail $ qzt-size c) (notail $ qzt-size d)))
    ((QztHub a b c d) (nat-add (notail $ qzt-size a) $ nat-add (notail $ qzt-size b) $ nat-add (notail $ qzt-size c) (notail $ qzt-size d)))
    (else 0)))
