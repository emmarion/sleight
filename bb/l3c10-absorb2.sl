(def-adts
  ((E1 : ((List (Tk)) W) -> Type)
    enum
    (many E1O : -> (E1 (Cons (Tk) (T0) (Nil (Tk)))))
    (many E1C : (erased (Tk) t) (erased (List (Tk)) W) (erased (E1 W) p) -> (E1 (Cons (Tk) t W)))))

(def-adts
  ((D0 : ((List (Nat)) D) -> Type)
    enum
    (many D0O : -> (D0 (Cons (Nat) (Zero) (Nil (Nat)))))
    (many D0C : (erased (Nat) d e) (erased (List (Nat)) D) (erased (D0 (Cons (Nat) e D)) p) -> (D0 (Cons (Nat) d (Cons (Nat) e D))))))

(def-fns _ $ (erased d0-cons : (erased (Nat) d) (erased (List (Nat)) D) (erased (D0 D) q) -> (erased (D0 (Cons (Nat) d D)) r))
  (match erased q _
    ((D0O) (D0C d (Zero) (Nil (Nat)) q))
    ((D0C d1 e D1 _) (D0C d d1 (Cons (Nat) e D1) q))))

(def-fns _ $ (erased dg-d0 : (erased (List (Ps)) w) (erased (List (Nat)) E D) (subterm erased (Dg w E D) g) (erased (D0 E) q) -> (erased (D0 D) r))
  (match erased g _
    ((DgN _) q)
    ((DgC _ h l w1 _ D1 g1 _) (d0-cons h _ (d0-cons l D1 (dg-d0 w1 E D1 g1 q))))))

(def-fns _ $ (erased tpr-e1 : (erased (Nat) m) (erased (List (Tk)) R X) (subterm erased (TpR m R X) p) (erased (E1 R) q) -> (erased (E1 X) r))
  (match erased p _
    ((TpZ _) q)
    ((TpS m1 _ X1 p1) (E1C (Tp) X1 (tpr-e1 m1 R X1 p1 q)))))

(def-fns _ $ (erased enc-e1 : (erased (List (Nat)) D) (erased (List (Tk)) X) (subterm erased (DEnc D X) e) (erased (D0 D) q) -> (erased (E1 X) r))
  (let-match erased e (EnC d D1 X1 _ e1 t) (absurd (EnN) (match erased q _)))
  (match erased q _
    ((D0O) (let-match erased e1 (EnN)) (let-match erased t (DtZ _)) (E1O))
    ((D0C _ _ _ q1)
      (let ((erased r1)) (enc-e1 D1 X1 e1 q1))
      (match erased t _
        ((DtZ _) (E1C (T0) X1 r1))
        ((DtS k _ _ p) (tpr-e1 k _ X p (E1C (T1) X1 r1)))))))

(def-fns _ $ (erased sw-split : (erased (List (Nat)) K K2) (erased (List (Tk)) X W) (subterm erased (Sw K X (SEnd K2)) sw) (erased (Ap3 W X) a) (erased (E1 W) e)
    -> (erased (List (Nat)) K3) (erased (Sw K W (SEnd K3)) s1) (erased (Sw K3 (Cons (Tk) (Tp) $ Cons (Tk) (T1) $ Cons (Tk) (T0) $ Nil (Tk)) (SEnd K2)) s2))
  (match erased sw _
    ((SwEnd _) (match erased a _))
    ((SwT0 _ R _ p)
      (let-match erased a (A3C _ W1 _ a1))
      (match erased e _
        ((E1O) (let-match erased a1 (A3N)) (values (Cons (Nat) n2 K) (SwT0 K (Nil (Tk)) _ (SwEnd _)) p))
        ((E1C _ _ e1)
          (let ((erased K3) (erased s1) (erased s2)) (sw-split (Cons (Nat) n2 K) K2 R W1 p a1 e1))
          (values K3 (SwT0 K W1 _ s1) s2))))
    ((SwT1 _ R _ p)
      (let-match erased a (A3C _ W1 _ a1))
      (let-match erased e (E1C _ _ e1))
      (let ((erased K3) (erased s1) (erased s2)) (sw-split (Cons (Nat) n3 K) K2 R W1 p a1 e1))
      (values K3 (SwT1 K W1 _ s1) s2))
    ((SwP0 _ R _ p)
      (let-match erased a (A3C _ W1 _ a1))
      (let-match erased a1 (A3C _ W2 _ a2))
      (let-match erased e (E1C _ _ e1))
      (match erased e1 _
        ((E1O) (let-match erased a2 (A3N)) (values (Cons (Nat) n3 K) (SwP0 K (Nil (Tk)) _ (SwEnd _)) p))
        ((E1C _ _ e2)
          (let ((erased K3) (erased s1) (erased s2)) (sw-split (Cons (Nat) n3 K) K2 R W2 p a2 e2))
          (values K3 (SwP0 K W2 _ s1) s2))))
    ((SwP1M s0 K1 R _ p)
      (let-match erased a (A3C _ W1 _ a1) (absurd (A3N) (match erased e _)))
      (let-match erased a1 (A3C _ W2 _ a2))
      (let-match erased e (E1C _ _ e1))
      (let-match erased e1 (E1C _ _ e2))
      (let ((erased K3) (erased s1) (erased s2))
        (sw-split (Cons (Nat) n2 $ Cons (Nat) n3 $ Cons (Nat) (Succ s0) K1) K2 R W2 p a2 e2))
      (values K3 (SwP1M s0 K1 W2 _ s1) s2))
    ((SwPPM s0 K1 R _ p)
      (let-match erased a (A3C _ W1 _ a1))
      (let-match erased a1 (A3C _ W2 _ a2) (absurd (A3N) (let-match erased e (E1C _ _ e1)) (match erased e1 _)))
      (let-match erased e (E1C _ _ e1))
      (let-match erased e1 (E1C _ _ e2))
      (let ((erased K3) (erased s1) (erased s2)) (sw-split (Cons (Nat) n3 $ Cons (Nat) (Succ s0) K1) K2 R W2 p a2 e2))
      (values K3 (SwPPM s0 K1 W2 _ s1) s2))))

(def-adts
  ((Cx : ((List (Tk)) W Y) -> Type)
    enum
    (many MkCx : (erased (List (Tk)) W Y) (erased (Nat) s0) (erased (List (Nat)) K1)
       (erased (Sw (Cons (Nat) n3 (Nil (Nat))) W (SEnd (Cons (Nat) n2 (Cons (Nat) s0 K1)))) sw)
       (erased (Wk (Cons (Nat) n3 $ Cons (Nat) n3 $ Cons (Nat) (Succ s0) K1) (Cons (Tk) (T1) (Nil (Tk))) Y) wk) -> (Cx W Y))))

(def-fns _ $ (erased rd-contact : (erased (List (Tk)) X W Y) (erased (Tt) T2) (erased (Ap3 W X) a) (erased (E1 W) e)
    (erased (Rd (Cons (Tk) (Tp) (Cons (Tk) (T1) X)) (Tt1) Y T2 n4) rd) -> (erased (Cx W Y) cx) (erased (Eq (Tt) T2 (Tt1)) et))
  (let-match erased rd (RdE _ W2 _ K K2 _ _ _ sw en wk))
  (let ((erased K3) (erased s1) (erased s2)) (sw-split (Cons (Nat) n3 (Nil (Nat))) K X W sw a e))
  (let-match erased s2 (SwP1M s0 K1 _ _ p))
  (let-match erased p (SwT0 _ _ _ p1))
  (let-match erased p1 (SwEnd _))
  (let-match erased en (EnMP _ _ _ _))
  (values (MkCx W Y s0 K1 s1 wk) (Refl _ T2)))
