(def-adts $ (Z : -> Type)
  enum
  (many Z0 : -> (Z))
  (many Zpos : (many (Nat) p) -> (Z))
  (many Zneg : (many (Nat) p) -> (Z)))

(def-adts $ (ZView : ((Z) z) ((Nat) p) ((Nat) q) -> Type)
  enum
  (many ZView0 : -> (ZView (Z0) (Zero) (Zero)))
  (many ZViewPos : (erased (Nat) p) -> (ZView (Zpos p) (Succ p) (Zero)))
  (many ZViewNeg : (erased (Nat) p) -> (ZView (Zneg p) (Zero) (Succ p))))

(def-adts $ (ZAdd : ((Z) a) ((Z) b) ((Z) c) -> Type)
  enum
  (many MkZAdd : (erased (Z) a b c) (erased (Nat) pa qa pb qb pc qc l r t)
      (erased (ZView a pa qa) va) (erased (ZView b pb qb) vb) (erased (ZView c pc qc) vc)
      (erased (Add pa pb l) hl) (erased (Add l qc t) hlt) (erased (Add qa qb r) hr) (erased (Add r pc t) hrt)
      -> (ZAdd a b c)))

(def-adts $ (ZMul : ((Z) a) ((Z) b) ((Z) c) -> Type)
  enum
  (many MkZMul : (erased (Z) a b c) (erased (Nat) pa qa pb qb pc qc m1 m2 m3 m4 l r t)
      (erased (ZView a pa qa) va) (erased (ZView b pb qb) vb) (erased (ZView c pc qc) vc)
      (erased (Mul pa pb m1) h1) (erased (Mul qa qb m2) h2) (erased (Mul pa qb m3) h3) (erased (Mul qa pb m4) h4)
      (erased (Add m1 m2 l) hl) (erased (Add l qc t) hlt) (erased (Add m3 m4 r) hr) (erased (Add r pc t) hrt)
      -> (ZMul a b c)))

(def-adts $ (ZLt : ((Z) a) ((Z) b) -> Type)
  enum
  (many MkZLt : (erased (Z) a b) (erased (Nat) pa qa pb qb l r)
      (erased (ZView a pa qa) va) (erased (ZView b pb qb) vb)
      (erased (Add pa qb l) hl) (erased (Add pb qa r) hr) (erased (Lt l r) lt)
      -> (ZLt a b)))

(def-adts $ (ZLe : ((Z) a) ((Z) b) -> Type)
  enum
  (many MkZLe : (erased (Z) a b) (erased (Nat) pa qa pb qb l r)
      (erased (ZView a pa qa) va) (erased (ZView b pb qb) vb)
      (erased (Add pa qb l) hl) (erased (Add pb qa r) hr) (erased (Lt l (Succ r)) le)
      -> (ZLe a b)))

(def-adts $ (ZOpp : ((Z) a) ((Z) b) -> Type)
  enum
  (many ZOpp0 : -> (ZOpp (Z0) (Z0)))
  (many ZOppPos : (erased (Nat) p) -> (ZOpp (Zpos p) (Zneg p)))
  (many ZOppNeg : (erased (Nat) p) -> (ZOpp (Zneg p) (Zpos p))))

(def-adts $ (ZAbs : ((Z) a) ((Z) b) -> Type)
  enum
  (many ZAbs0 : -> (ZAbs (Z0) (Z0)))
  (many ZAbsPos : (erased (Nat) p) -> (ZAbs (Zpos p) (Zpos p)))
  (many ZAbsNeg : (erased (Nat) p) -> (ZAbs (Zneg p) (Zpos p))))

(def-adts $ (ZMax : ((Z) a) ((Z) b) ((Z) c) -> Type)
  enum
  (many ZMaxLeft : (erased (Z) a b) (erased (ZLe b a) le) -> (ZMax a b a))
  (many ZMaxRight : (erased (Z) a b) (erased (ZLt a b) lt) -> (ZMax a b b)))

(def-adts $ (Q : -> Type)
  enum
  (many Qmake : (many (Z) num) (many (Nat) den) -> (Q)))

(def-adts $ (QLt : ((Q) x) ((Q) y) -> Type)
  enum
  (many MkQLt : (erased (Z) nx ny l r) (erased (Nat) dx dy)
      (erased (ZMul nx (Zpos dy) l) hl) (erased (ZMul ny (Zpos dx) r) hr) (erased (ZLt l r) lt)
      -> (QLt (Qmake nx dx) (Qmake ny dy))))

(def-adts $ (QLe : ((Q) x) ((Q) y) -> Type)
  enum
  (many MkQLe : (erased (Z) nx ny l r) (erased (Nat) dx dy)
      (erased (ZMul nx (Zpos dy) l) hl) (erased (ZMul ny (Zpos dx) r) hr) (erased (ZLe l r) le)
      -> (QLe (Qmake nx dx) (Qmake ny dy))))

(def-adts $ (QPlus : ((Q) x) ((Q) y) ((Q) z) -> Type)
  enum
  (many MkQPlus : (erased (Z) nx ny l r n) (erased (Nat) dx dy d)
      (erased (ZMul nx (Zpos dy) l) hl) (erased (ZMul ny (Zpos dx) r) hr) (erased (ZAdd l r n) hn)
      (erased (ZMul (Zpos dx) (Zpos dy) (Zpos d)) hd)
      -> (QPlus (Qmake nx dx) (Qmake ny dy) (Qmake n d))))

(def-adts $ (QMult : ((Q) x) ((Q) y) ((Q) z) -> Type)
  enum
  (many MkQMult : (erased (Z) nx ny n) (erased (Nat) dx dy d)
      (erased (ZMul nx ny n) hn) (erased (ZMul (Zpos dx) (Zpos dy) (Zpos d)) hd)
      -> (QMult (Qmake nx dx) (Qmake ny dy) (Qmake n d))))

(def-adts $ (QOpp : ((Q) x) ((Q) z) -> Type)
  enum
  (many MkQOpp : (erased (Z) nx n) (erased (Nat) dx) (erased (ZOpp nx n) hn)
      -> (QOpp (Qmake nx dx) (Qmake n dx))))

(def-adts $ (QMinus : ((Q) x) ((Q) y) ((Q) z) -> Type)
  enum
  (many MkQMinus : (erased (Q) x y o z) (erased (QOpp y o) ho) (erased (QPlus x o z) hp)
      -> (QMinus x y z)))

(def-adts $ (QAbs : ((Q) x) ((Q) z) -> Type)
  enum
  (many MkQAbs : (erased (Z) nx n) (erased (Nat) dx) (erased (ZAbs nx n) hn)
      -> (QAbs (Qmake nx dx) (Qmake n dx))))

(def-adts $ (QInv : ((Q) x) ((Q) z) -> Type)
  enum
  (many QInv0 : (erased (Nat) dx) -> (QInv (Qmake (Z0) dx) (Qmake (Z0) (Zero))))
  (many QInvPos : (erased (Nat) p dx) -> (QInv (Qmake (Zpos p) dx) (Qmake (Zpos dx) p)))
  (many QInvNeg : (erased (Nat) p dx) -> (QInv (Qmake (Zneg p) dx) (Qmake (Zneg dx) p))))

(def-adts $ (QPowerPos : ((Q) x) ((Nat) p) ((Q) z) -> Type)
  enum
  (many QPowerOne : (erased (Q) x) -> (QPowerPos x (Zero) x))
  (many QPowerSucc : (erased (Q) x y z) (erased (Nat) p) (erased (QPowerPos x p y) hy) (erased (QMult x y z) hz)
      -> (QPowerPos x (Succ p) z)))

(def-adts $ (QPower : ((Q) x) ((Z) k) ((Q) z) -> Type)
  enum
  (many QPower0 : (erased (Q) x) -> (QPower x (Z0) (Qmake (Zpos (Zero)) (Zero))))
  (many QPowerZpos : (erased (Q) x z) (erased (Nat) p) (erased (QPowerPos x p z) hz) -> (QPower x (Zpos p) z))
  (many QPowerZneg : (erased (Q) x y z) (erased (Nat) p) (erased (QPowerPos x p y) hy) (erased (QInv y z) hz)
      -> (QPower x (Zneg p) z)))

(def-adts $ (QRed : ((Q) x) ((Q) z) -> Type)
  enum
  (many MkQRed : (erased (Z) nx n u v un vd s) (erased (Nat) dx d g)
      (erased (ZMul n (Zpos g) nx) hn) (erased (ZMul (Zpos d) (Zpos g) (Zpos dx)) hd)
      (erased (ZMul u n un) hu) (erased (ZMul v (Zpos d) vd) hv) (erased (ZAdd un vd (Zpos (Zero))) hb)
      -> (QRed (Qmake nx dx) (Qmake n d))))

(def-adts $ (Spec : -> Type)
  enum
  (many MkSpec : (erased Type E) (erased E env) (erased (TyCtor (E e) ((Z) n) ((Q) q) -> Type) R) (erased (Z) scale)
      -> (Spec)))

(def-adts $ (SeqAt : ((Spec) s) ((Z) n) ((Q) q) -> Type)
  enum
  (many MkSeqAt : (erased Type E) (erased E env) (erased (TyCtor (E e) ((Z) n) ((Q) q) -> Type) R) (erased (Z) scale n)
      (erased (Q) q) (erased (R env n q) r)
      -> (SeqAt (MkSpec E env R scale) n q)))

(def-adts $ (ScaleOf : ((Spec) s) ((Z) scale) -> Type)
  enum
  (many MkScaleOf : (erased Type E) (erased E env) (erased (TyCtor (E e) ((Z) n) ((Q) q) -> Type) R) (erased (Z) scale)
      -> (ScaleOf (MkSpec E env R scale) scale)))

(def-adts $ (QCauchySeq : ((Level) M) ((Spec) s) -> Type)
  enum
  (many MkQCauchySeq : (erased (Level) M) (erased (Spec) s)
      (erased (Fn M (erased (Z) k p q) (erased (Q) a b) (erased (ZLe p k) hp) (erased (ZLe q k) hq)
          (erased (SeqAt s p a) ha) (erased (SeqAt s q b) hb) ->
          (erased (Q) d e c) (erased (QMinus a b d) hd) (erased (QAbs d e) he)
          (erased (QPower (Qmake (Zpos (Succ (Zero))) (Zero)) k c) hc) (erased (QLt e c) lt)) cauchy)
      -> (QCauchySeq M s)))

(def-adts $ (QBound : ((Level) M) ((Spec) s) -> Type)
  enum
  (many MkQBound : (erased (Level) M) (erased (Spec) s) (erased (Z) scale) (erased (ScaleOf s scale) hs)
      (erased (Fn M (erased (Z) k) (erased (Q) a) (erased (SeqAt s k a) ha) ->
          (erased (Q) e c) (erased (QAbs a e) he)
          (erased (QPower (Qmake (Zpos (Succ (Zero))) (Zero)) scale c) hc) (erased (QLt e c) lt)) bound)
      -> (QBound M s)))

(def-adts $ (CReal : ((Level) M) ((Spec) s) -> Type)
  enum
  (many MkCReal : (erased (Level) M) (erased (Spec) s)
      (many (Fn M (many (Z) n) -> (many (Q) q) (erased (SeqAt s n q) h)) seq)
      (erased (Fn M (erased (Z) n) (erased (Q) a b) (erased (SeqAt s n a) ha) (erased (SeqAt s n b) hb) ->
          (erased (Eq (Q) a b) e)) functional)
      (erased (QCauchySeq M s) cauchy)
      (erased (QBound M s) bound)
      -> (CReal M s)))

(def-adts $ (CRealLt : ((Spec) x) ((Spec) y) -> Type)
  enum
  (many MkCRealLt : (erased (Spec) x y) (erased (Z) n) (erased (Q) a b c d e)
      (erased (SeqAt x n a) ha) (erased (SeqAt y n b) hb) (erased (QMinus b a c) hc)
      (erased (QPower (Qmake (Zpos (Succ (Zero))) (Zero)) n d) hd) (erased (QMult (Qmake (Zpos (Succ (Zero))) (Zero)) d e) he)
      (erased (QLt e c) lt)
      -> (CRealLt x y)))

(def-adts $ (CRealLe : ((Spec) x) ((Spec) y) -> Type)
  enum
  (many MkCRealLe : (erased (Spec) x y) (erased (Level) L)
      (erased (Fn L (erased (CRealLt y x) h) -> (erased (False) f)) le)
      -> (CRealLe x y)))

(def-adts $ (CRealEq : ((Spec) x) ((Spec) y) -> Type)
  enum
  (many MkCRealEq : (erased (Spec) x y) (erased (CRealLe y x) yx) (erased (CRealLe x y) xy)
      -> (CRealEq x y)))

(def-adts $ (CRealAppart : ((Spec) x) ((Spec) y) -> Type)
  enum
  (many AppartLt : (erased (Spec) x y) (erased (CRealLt x y) lt) -> (CRealAppart x y))
  (many AppartGt : (erased (Spec) x y) (erased (CRealLt y x) gt) -> (CRealAppart x y)))

(def-adts $ (SpecPair : -> Type)
  enum
  (many MkSpecPair : (erased (Spec) x y) -> (SpecPair)))

(def-adts $ (CRealPlusSeq : ((SpecPair) e) ((Z) n) ((Q) q) -> Type)
  enum
  (many MkCRealPlusSeq : (erased (Spec) x y) (erased (Z) n m) (erased (Q) a b c r)
      (erased (ZAdd m (Zpos (Zero)) n) hm) (erased (SeqAt x m a) ha) (erased (SeqAt y m b) hb)
      (erased (QPlus a b c) hc) (erased (QRed c r) hr)
      -> (CRealPlusSeq (MkSpecPair x y) n r)))

(def-adts $ (CRealPlus : ((Spec) x) ((Spec) y) ((Spec) z) -> Type)
  enum
  (many MkCRealPlus : (erased (Spec) x y) (erased (Z) sx sy m s)
      (erased (ScaleOf x sx) hx) (erased (ScaleOf y sy) hy) (erased (ZMax sx sy m) hm) (erased (ZAdd m (Zpos (Zero)) s) hs)
      -> (CRealPlus x y (MkSpec (SpecPair) (MkSpecPair x y) CRealPlusSeq s))))

(def-adts $ (CRealOppSeq : ((Spec) e) ((Z) n) ((Q) q) -> Type)
  enum
  (many MkCRealOppSeq : (erased (Spec) x) (erased (Z) n) (erased (Q) a r)
      (erased (SeqAt x n a) ha) (erased (QOpp a r) hr)
      -> (CRealOppSeq x n r)))

(def-adts $ (CRealOpp : ((Spec) x) ((Spec) z) -> Type)
  enum
  (many MkCRealOpp : (erased (Spec) x) (erased (Z) sx) (erased (ScaleOf x sx) hx)
      -> (CRealOpp x (MkSpec (Spec) x CRealOppSeq sx))))

(def-adts $ (CRealMinus : ((Spec) x) ((Spec) y) ((Spec) z) -> Type)
  enum
  (many MkCRealMinus : (erased (Spec) x y o z) (erased (CRealOpp y o) ho) (erased (CRealPlus x o z) hp)
      -> (CRealMinus x y z)))

(def-adts $ (CRealMultSeq : ((SpecPair) e) ((Z) n) ((Q) q) -> Type)
  enum
  (many MkCRealMultSeq : (erased (Spec) x y) (erased (Z) sx sy n mx my tx ty) (erased (Q) a b r)
      (erased (ScaleOf x sx) hsx) (erased (ScaleOf y sy) hsy)
      (erased (ZAdd mx sy tx) htx) (erased (ZAdd tx (Zpos (Zero)) n) hmx)
      (erased (ZAdd my sx ty) hty) (erased (ZAdd ty (Zpos (Zero)) n) hmy)
      (erased (SeqAt x mx a) ha) (erased (SeqAt y my b) hb) (erased (QMult a b r) hr)
      -> (CRealMultSeq (MkSpecPair x y) n r)))

(def-adts $ (CRealMult : ((Spec) x) ((Spec) y) ((Spec) z) -> Type)
  enum
  (many MkCRealMult : (erased (Spec) x y) (erased (Z) sx sy s)
      (erased (ScaleOf x sx) hx) (erased (ScaleOf y sy) hy) (erased (ZAdd sx sy s) hs)
      -> (CRealMult x y (MkSpec (SpecPair) (MkSpecPair x y) CRealMultSeq s))))
