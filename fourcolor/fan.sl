; The sweep's state before step t: the map, its darts' labels pl, one representative dart per label in rep, and the
; frontier gs, whose items in order are fl.
(def-adts $ (State : ((Nat) t) ((List (Nat)) e) ((List (Nat)) nd) ((List (Nat)) pl) ((List (Nat)) rep) ((List (Group)) gs)
    ((List (Nat)) fl) -> Type)
  enum
  (many MkState : (erased (Nat) t n d0) (erased (List (Nat)) e nd pl rep s xs0 fl) (erased (List (Group)) gsr)
      (erased (PlaneMap e nd) pm) (erased (Length (Nat) e n) le) (erased (Length (Nat) nd n) ln) (erased (Length (Nat) pl n) lp)
      (erased (Length (Nat) rep t) lr)
      (erased (Darts (Cons (Group) (MkGroup d0 xs0) gsr) s) ds) (erased (Distinct s) dist)
      (erased (Chain e nd s (Cons (Group) (MkGroup d0 xs0) gsr) d0) ch)
      (erased (Respects pl nd pl) rp) (erased (AllLt pl t) al) (erased (GroupLab pl (Cons (Group) (MkGroup d0 xs0) gsr)) gl)
      (erased (GFlat (Cons (Group) (MkGroup d0 xs0) gsr) fl) gf) (erased (Reps nd rep (Zero) pl) rs)
      -> (State t e nd pl rep (Cons (Group) (MkGroup d0 xs0) gsr) fl)))

(def-fns _ $ (erased sub-snoc : (erased (Nat) d) (erased (List (Nat)) m m2 s) (subterm erased (Sub m s) sb) (erased (In d s) p)
    (erased (Snoc (Nat) m d m2) sn) -> (erased (Sub m2 s) r))
  (match erased sb _
    ((SubNil _) (let-match erased sn (SnocNil _ _)) (SubCons d _ s p (SubNil s)))
    ((SubCons x m1 _ q sb1)
      (let-match erased sn (SnocCons _ _ _ _ m3 sn1))
      (SubCons x m3 s q (sub-snoc d m1 m3 s sb1 p sn1)))))

; The head group moves to the end.
(def-fns _ $ (erased state-rot : (erased (Nat) t d0 d1) (erased (List (Nat)) e nd pl rep xs0 xs1 fl) (erased (List (Group)) gsr)
    (erased (State t e nd pl rep (Cons (Group) (MkGroup d0 xs0) $ Cons (Group) (MkGroup d1 xs1) gsr) fl) st) ->
    (erased (List (Group)) gs2) (erased (List (Nat)) fl2) (erased (Snoc (Group) (Cons (Group) (MkGroup d1 xs1) gsr) (MkGroup d0 xs0) gs2) sg)
    (erased (State t e nd pl rep gs2 fl2) st2) (erased (Rot (Nat) fl2 fl) ro))
  (let-match erased st (MkState _ n _ _ _ _ _ s _ _ _ pm le ln lp lr ds dist ch rp al gl gf rs))
  (let-match erased ds (DartsCons _ _ s1 _ ds1))
  (let-match erased dist (DistCons _ _ nd0 dist1))
  (let-match erased ch (ChainCons _ _ _ _ _ _ _ _ _ k0 ch1))
  (let-match erased gl (GLCons _ _ _ u0 _ pu0 a0 gl1))
  (let-match erased gf (GFlatCons _ _ fl1 _ _ p gf1))
  (let ((erased gs1)) (Cons (Group) (MkGroup d1 xs1) gsr))
  (let ((erased gs2) (erased sg)) (snoc-exists _ gs1 (MkGroup d0 xs0)))
  (let ((erased s2) (erased ss)) (snoc-exists _ s1 d0))
  (let ((erased fl2) (erased a2)) (lapp-exists _ fl1 xs0))
  (let ((erased sb)) (sub-snoc d0 s1 s2 s (sub-cons d0 s1 s1 (sub-refl s1)) (InHere d0 s1) ss))
  (let ((erased ch2)) (chain-snoc e nd s xs0 gs1 gs2 d0 d1 ch1 k0 sg))
  (let-match erased sg (SnocCons _ _ _ _ gsr2 _))
  (values gs2 fl2 sg
    (MkState t n d1 e nd pl rep s2 xs1 fl2 gsr2 pm le ln lp lr (darts-snoc gs1 gs2 s1 s2 xs0 d0 ds1 sg ss) (distinct-snoc d0 s1 s2 dist1 nd0 ss)
      (chain-weaken e nd s s2 gs2 d1 ch2 sb) rp al (grouplab-snoc pl xs0 gs1 gs2 d0 u0 gl1 sg pu0 a0) (flat-snoc gs1 gs2 d0 xs0 fl1 fl2 gf1 sg a2) rs)
    (MkRot _ fl2 fl xs0 fl1 p a2)))
