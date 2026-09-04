; expect: (Zero)
; A Nat has one bijective base-2 spelling, so two spellings for one Nat are contradictory: a branch
; equating two literals is refuted by a vacuous match on numeral-inj's Eq. The cost is the spellings'
; depth, not the difference between the numbers.

(def-adts
  (Eq : (Type A) (A x) (A y) -> Type
    enum
    (many Refl : (erased Type A) (erased A x) -> (Eq A x x))))

(def-lvl D)

; same double -> same half
(def-fns D $ erased double-inj :
    (erased (Nat) m1) (erased (Nat) m2) (erased (Nat) d)
    (subterm erased (Double m1 d) p) (erased (Double m2 d) q) -> (erased (Eq (Nat) m1 m2) e)
  (match erased p _
    ((D0) (match erased q _ ((D0) (Refl (Nat) m1)) (absurd DS)))
    ((DS a1 b1 pp)
      (match erased q _
        (absurd D0)
        ((DS a2 b2 qq)
          (let (erased sp) (prove-subterm pp p))
          (let (erased ih) (double-inj a1 a2 b1 (subterm sp) pp qq))
          (match erased ih _ ((Refl t r) (Refl (Nat) m1))))))))

; no number is both even and odd: 2a = e+1 and 2b = e is impossible
(def-fns D $ erased double-parity :
    (erased (Nat) a) (erased (Nat) b) (erased (Nat) e)
    (subterm erased (Double a (Succ e)) p) (erased (Double b e) q) -> (erased (False) f)
  (match erased p _
    (absurd D0)
    ((DS a1 b1 pp)
      (match erased q _
        (absurd D0)
        ((DS a2 b2 qq)
          (let (erased sp) (prove-subterm pp p))
          (double-parity a1 a2 b2 (subterm sp) pp qq))))))
(def-lvl NI)
(let (erased dni) (prove-predates D NI))

; the same Nat has only one bijective base-2 spelling
(def-fns NI $ erased numeral-inj :
    (erased (Bin) b1) (erased (Bin) b2) (erased (Nat) n)
    (subterm erased (Numeral b1 n) v1) (erased (Numeral b2 n) v2) -> (erased (Eq (Bin) b1 b2) e)
  (match erased v1 _
    ((NZ) (match erased v2 _ ((NZ) (Refl (Bin) b1)) (absurd N1) (absurd N2)))
    ((N1 c1 m1 d1 w1 dd1)
      (match erased v2 _
        (absurd NZ)
        ((N1 c2 m2 d2 w2 dd2)
          (let (erased em) (double-inj (predates dni) m1 m2 d1 dd1 dd2))
          (match erased em _
            ((Refl t r)
              (let (erased sp) (prove-subterm w1 v1))
              (let (erased ih) (numeral-inj c1 c2 m1 (subterm sp) w1 w2))
              (match erased ih _ ((Refl t2 r2) (Refl (Bin) b1))))))
        (absurd (N2 c2 m2 d2 w2 dd2) (double-parity (predates dni) m1 m2 d2 dd1 dd2))))
    ((N2 c1 m1 d1 w1 dd1)
      (match erased v2 _
        (absurd NZ)
        (absurd (N1 c2 m2 d2 w2 dd2) (double-parity (predates dni) m2 m1 d1 dd2 dd1))
        ((N2 c2 m2 d2 w2 dd2)
          (let (erased em) (double-inj (predates dni) m1 m2 d1 dd1 dd2))
          (match erased em _
            ((Refl t r)
              (let (erased sp) (prove-subterm w1 v1))
              (let (erased ih) (numeral-inj c1 c2 m1 (subterm sp) w1 w2))
              (match erased ih _ ((Refl t2 r2) (Refl (Bin) b1))))))))))

(def-adts (Tag : ((Nat) n) -> Type enum (many TA : -> (Tag 3)) (many TB : -> (Tag 1000))))

(def-lvl Z)
(let (erased niz) (prove-predates NI Z))

(def-fns Z $ many only-a : (many (Tag 3) t) -> (many (Nat) r)
  (match many t (((Nat) r))
    ((TA) (Zero))
    (absurd (TB)
      (match erased
          (numeral-inj (predates niz)
            (B1 (B1 (BZ)))
            (B2 (B1 (B1 (B2 (B1 (B2 (B2 (B2 (B2 (BZ))))))))))
            3 (numeral-of 3) (numeral-of 1000))
          (((False) f))
        (absurd Refl)))))

(only-a (TA))
