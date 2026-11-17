(def-adts $ (Out : (Type S) ((TyCtor (S s) -> Type) Inv) ((TyCtor (S s) -> Type) Good) (S s) -> Type)
  enum
  (many Done : (erased Type S) (erased (TyCtor (S s) -> Type) Inv) (erased (TyCtor (S s) -> Type) Good) (erased S s)
     (erased (Good s) g) -> (Out S Inv Good s))
  (many Next : (erased Type S) (erased (TyCtor (S s) -> Type) Inv) (erased (TyCtor (S s) -> Type) Good) (erased S s)
     (many S s2) (erased (Inv s2) i2) -> (Out S Inv Good s)))

(def-lvl D)
(def-lvl M)
(def-adts $ (Any : ((Nat) n) -> Type)
  enum
  (many MkAny : (erased (Nat) n) -> (Any n)))
(def-adts $ (IsZero : ((Nat) n) -> Type)
  enum
  (many MkIsZero : -> (IsZero (Zero))))
(def-fns M $ (many countdown : (many (Nat) s) (erased (Any s) i) -> (many (Out (Nat) Any IsZero s) r))
  (match many s _
    ((Zero) (Done _ _ _ _ (MkIsZero)))
    ((Succ n) (Next _ _ _ _ n (MkAny n)))))
(def-lvl P)
(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns D $ (many drive : (erased Type S) (erased (TyCtor (S s) -> Type) Inv) (erased (TyCtor (S s) -> Type) Good)
    (erased (Level) M) (erased (Predates (Level) M P) pm)
    (many (Fn M (many S s) (erased (Inv s) i) -> (many (Out S Inv Good s) r)) step)
    (many S s) (erased (Inv s) i) -> (unique (Program P) next))
  (def-unique P $ (unique k : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) next))
    (let ((many r)) (step (predates pm) s i))
    (match many r _
      ((Done _ _ _ _ g) (values w (Exit P code0)))
      ((Next _ _ _ _ s2 i2) (values w (drive S Inv Good M pm step s2 i2)))))
  (Continue P k))

(let ((erased pm)) (prove-predates M P))
(drive (Nat) Any IsZero M pm countdown 5 (MkAny 5))
