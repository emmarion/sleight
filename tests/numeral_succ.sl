; needs: list vec
; expect: (Zero)
; Bijective base-2 successor is structural, carrying only through trailing B2s, so numeral-succ relates
; adjacent literals: 5 is (Succ 4). let-match reads the erased Eq and binds the rewrite outward --
; without it the VNil branch below is not refuted.

(def-adts
  (Eq : (Type A) (A x) (A y) -> Type
    enum
    (many Refl : (erased Type A) (erased A x) -> (Eq A x x))))

(def-lvl D)

; Double is functional: one input, one output
(def-fns D $ erased double-fn :
    (erased (Nat) m) (erased (Nat) d1) (erased (Nat) d2)
    (subterm erased (Double m d1) p) (erased (Double m d2) q) -> (erased (Eq (Nat) d1 d2) e)
  (match erased p _
    ((D0) (match erased q _ ((D0) (Refl (Nat) d1)) (absurd DS)))
    ((DS a1 b1 pp)
      (match erased q _
        (absurd D0)
        ((DS a2 b2 qq)
          (let (erased sp) (prove-subterm pp p))
          (let (erased ih) (double-fn a1 b1 b2 (subterm sp) pp qq))
          (match erased ih _ ((Refl t r) (Refl (Nat) d1))))))))

(def-lvl NF)
(let (erased dnf) (prove-predates D NF))

; Numeral is functional: one spelling, one Nat
(def-fns NF $ erased numeral-fn :
    (erased (Bin) b) (erased (Nat) m1) (erased (Nat) m2)
    (subterm erased (Numeral b m1) v1) (erased (Numeral b m2) v2) -> (erased (Eq (Nat) m1 m2) e)
  (match erased v1 _
    ((NZ) (match erased v2 _ ((NZ) (Refl (Nat) m1)) (absurd N1) (absurd N2)))
    ((N1 c1 x1 d1 w1 dd1)
      (match erased v2 _
        (absurd NZ)
        ((N1 c2 x2 d2 w2 dd2)
          (let (erased sp) (prove-subterm w1 v1))
          (let (erased ih) (numeral-fn c1 x1 x2 (subterm sp) w1 w2))
          (match erased ih _
            ((Refl t r)
              (let (erased ed) (double-fn (predates dnf) x1 d1 d2 dd1 dd2))
              (match erased ed _ ((Refl t2 r2) (Refl (Nat) m1))))))
        (absurd N2)))
    ((N2 c1 x1 d1 w1 dd1)
      (match erased v2 _
        (absurd NZ)
        (absurd N1)
        ((N2 c2 x2 d2 w2 dd2)
          (let (erased sp) (prove-subterm w1 v1))
          (let (erased ih) (numeral-fn c1 x1 x2 (subterm sp) w1 w2))
          (match erased ih _
            ((Refl t r)
              (let (erased ed) (double-fn (predates dnf) x1 d1 d2 dd1 dd2))
              (match erased ed _ ((Refl t2 r2) (Refl (Nat) m1))))))))))
; c spells the successor of b: carry propagates only through trailing B2s
(def-adts
  (BinSucc : ((Bin) b) ((Bin) c) -> Type
    enum
    (many BSZ : -> (BinSucc (BZ) (B1 (BZ))))
    (many BS1 : (erased (Bin) b) -> (BinSucc (B1 b) (B2 b)))
    (many BS2 : (erased (Bin) b) (erased (Bin) c) (erased (BinSucc b c) s) -> (BinSucc (B2 b) (B1 c)))))

(def-lvl NS)
(let (erased dns) (prove-predates D NS))
(let (erased nfns) (prove-predates NF NS))

; the successor spelling names the successor Nat
(def-fns NS $ erased numeral-succ :
    (erased (Bin) b) (erased (Bin) c) (erased (Nat) m) (erased (Nat) n)
    (subterm erased (BinSucc b c) s)
    (erased (Numeral b m) v) (erased (Numeral c n) w) -> (erased (Eq (Nat) n (Succ m)) e)
  (match erased s _
    ((BSZ)
      (match erased v _
        ((NZ)
          (match erased w _
            (absurd NZ)
            ((N1 c1 x1 d1 w1 dd1)
              (match erased w1 _
                ((NZ) (match erased dd1 _ ((D0) (Refl (Nat) n)) (absurd DS)))
                (absurd N1)
                (absurd N2)))
            (absurd N2)))
        (absurd N1)
        (absurd N2)))
    ((BS1 b0)
      (match erased v _
        (absurd NZ)
        ((N1 c1 x1 d1 w1 dd1)
          (match erased w _
            (absurd NZ)
            (absurd N1)
            ((N2 c2 x2 d2 w2 dd2)
              (let (erased ex) (numeral-fn (predates nfns) c1 x1 x2 w1 w2))
              (match erased ex _
                ((Refl t r)
                  (let (erased ed) (double-fn (predates dns) x1 d1 d2 dd1 dd2))
                  (match erased ed _ ((Refl t2 r2) (Refl (Nat) n))))))))
        (absurd N2)))
    ((BS2 b0 c0 s0)
      (match erased v _
        (absurd NZ)
        (absurd N1)
        ((N2 c1 x1 d1 w1 dd1)
          (match erased w _
            (absurd NZ)
            ((N1 c2 x2 d2 w2 dd2)
              (let (erased sp) (prove-subterm s0 s))
              (let (erased ih) (numeral-succ b0 c0 x1 x2 (subterm sp) s0 w1 w2))
              (match erased ih _
                ((Refl t r)
                  (match erased dd2 _
                    (absurd D0)
                    ((DS a2 bb ddx)
                      (let (erased ed) (double-fn (predates dns) x1 d1 bb dd1 ddx))
                      (match erased ed _ ((Refl t2 r2) (Refl (Nat) n))))))))
            (absurd N2)))))))

; 4 spells (B2 (B1 (BZ))), 5 spells (B1 (B2 (BZ))); succ carries through the trailing B2
(let (erased e5)
  (numeral-succ (B2 (B1 (BZ))) (B1 (B2 (BZ))) 4 5
    (BS2 (B1 (BZ)) (B2 (BZ)) (BS1 (BZ)))
    (numeral-of 4) (numeral-of 5)))

(let-match erased e5 (Refl t r))

; 5 is now (Succ 4), so VNil is refuted with no annotation
(def-lvl X)
(def-fns X $ many first : (erased Type A) (many (Vec A 5) v) -> (many A x)
  (match many v ((A r))
    (absurd VNil)
    ((VCons a m x xs) x)))
(Zero)
