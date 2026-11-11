; R : what a sequence element may return instead of a point, ending the search.
(def-adts $ (Elem : (Type I) ((TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (Type R)
    ((List (List (Coord))) bs) ((Nat) i) -> Type)
  enum
  (many EEsc : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased Type R)
     (erased (List (List (Coord))) bs) (erased (Nat) i) (many R r) -> (Elem I P R bs i))
  (many EPt : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased Type R)
     (erased (List (List (Coord))) bs) (erased (Nat) i) (many I it) (many (List (Nat)) x) (erased (P i it x) px)
     (many (Nat) r) (erased (List (Coord)) b) (erased (Nth (List (Coord)) bs r b) nb) (erased (InBox b x) ib)
     -> (Elem I P R bs i)))

(def-adts $ (Res : (Type I) ((TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (Type R) -> Type)
  enum
  (many RFound : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased Type R)
     (many (Nat) i j) (erased (Lt i j) l) (many I a) (many (List (Nat)) x) (many I c) (many (List (Nat)) y)
     (erased (P i a x) pa) (erased (P j c y) pc) (erased (PLe x y) le) -> (Res I P R))
  (many REsc : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased Type R)
     (many R r) -> (Res I P R)))

; A : the level of the sequences the search accepts.
(def-fns _ $ (many dickson-factory : (erased (Level) A) ->
    (erased (Level) D)
    (many (Fn D (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased Type R)
              (many (Nat) m) (many (List (List (Coord))) bs) (erased (LeafOK bs m (Zero)) ok)
              (many (Fn A (many (Nat) i) -> (many (Elem I P R bs i) e)) g) -> (many (Res I P R) res)) dickson))
  (def-lvl S)
  (let ((erased L) (many run)) (lex-factory S))
  (def-fns _ $ (many dickson : (erased Type I) (erased (TyCtor ((Nat) n) (I it) ((List (Nat)) x) -> Type) P) (erased Type R)
      (many (Nat) m) (many (List (List (Coord))) bs) (erased (LeafOK bs m (Zero)) ok)
      (many (Fn A (many (Nat) i) -> (many (Elem I P R bs i) e)) g) -> (many (Res I P R) res))
    (def-adts $ (St : ((List (Nat)) v) -> Type)
      enum
      (many MkSt : (erased (List (Nat)) v) (many (Nat) nn) (many (Forest I P bs) f) (erased (MF I P m nn bs f v) mf) -> (St v)))
    (def-fns S $ (many step : (erased (List (Nat)) v) (many (St v) st) -> (many (Step St (Res I P R) (Succ m) v) o))
      (let-match many st (MkSt _ nn f mf))
      (let-match many (g nn) (EPt _ _ _ _ _ it x px r b nb ib) ((EEsc _ _ _ _ _ z) (Done St (Res I P R) (Succ m) v (REsc I P R z))))
      (let-match many (insert I P m nn nn (lt-succ nn) it x px bs f r b nb ib v mf) (Inserted _ _ _ _ _ _ _ _ f2 v2 mf2 pos lp)
        ((Found _ _ _ _ _ _ _ _ n2 it2 p2 pp2 l2 le2)
          (Done St (Res I P R) (Succ m) v (RFound I P R n2 nn l2 it2 p2 it x pp2 px le2))))
      (Next St (Res I P R) (Succ m) v v2 (MkSt v2 (Succ nn) f2 mf2) pos lp (mf-length I P m (Succ nn) bs f2 v2 mf2)))
    (let ((many f0) (erased v0) (erased mf0) (erased _)) (mk-leaves I P m (Zero) (Zero) (LtZ (Succ m)) bs ok))
    (run St (Res I P R) m step v0 (mf-length I P m (Zero) bs f0 v0 mf0) (MkSt v0 (Zero) f0 mf0)))
  (values (level-of dickson) dickson))
