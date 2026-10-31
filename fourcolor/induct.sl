(def-adts $ (Mp : -> Type)
  enum
  (many MkMp : (erased (Nat) d) (erased (List (Nat)) e n f) -> (Mp)))

(def-adts $ (MpCols : ((List (Mp)) ms) -> Type)
  enum
  (many MpcNil : -> (MpCols (Nil (Mp))))
  (many MpcCons : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (List (Mp)) ms) (erased (FourColoring e f ks) c) (erased (MpCols ms) rest)
      -> (MpCols (Cons (Mp) (MkMp d e n f) ms))))

; A certificate that (e, f) on d darts has no four-colouring.
(def-adts $ (NoColoring : ((List (Nat)) e f) -> Type)
  enum
  (many MkNoColoring : (erased (Nat) d) (erased (List (Nat)) e f) (erased (NoExt d e f (Nil (Nat)) (Nil (Nat)) (Nil (Nat))) ne)
      (erased (Length (Nat) f d) lf) -> (NoColoring e f)))

(def-fns _ $ (erased no-coloring : (erased (List (Nat)) e f ks) (erased (NoColoring e f) nc) (erased (FourColoring e f ks) c) -> (erased (False) r))
  (let-match erased nc (MkNoColoring d _ _ ne lf))
  (let-match erased c (MkFourColoring _ _ _ _ rf _ _ _))
  (noext-sound d e f (Nil _) (Nil _) (Nil _) ks ks ne (JoinNil ks) (respects-length ks f ks d rf lf) c (RespNil ks)))

(def-adts $ (Decided : ((List (Nat)) e f) -> Type)
  enum
  (many Colors : (erased (List (Nat)) e f ks) (erased (FourColoring e f ks) c) -> (Decided e f))
  (many NoColors : (erased (List (Nat)) e f) (erased (NoColoring e f) nc) -> (Decided e f)))

(def-fns _ $ (erased color-dec : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) -> (erased (Decided e f) r))
  (let ((erased _) (erased _) (erased lf)) (hyper-lengths d e n f h))
  (let-match erased (search-ring d (Zero) e n f (Nil _) (Nil _) h (UnderNil d) (LengthNil _) (LengthNil _))
    (NotFound _ _ _ _ _ _ ne) ((Found _ _ _ _ _ _ ks c _) (Colors e f ks c)))
  (NoColors e f (MkNoColoring d e f ne lf)))

(def-adts $ (Pbpp : ((Nat) d) ((List (Nat)) e n f) -> Type)
  enum
  (many MkPbpp : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) g)
      (erased (Bridgeless d e n f) b) (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (Precubic d n) pc) -> (Pbpp d e n f)))

; Each map of ms is planar, bridgeless, plain and precubic, on fewer than d darts.
(def-adts $ (Smaller : ((Nat) d) ((List (Mp)) ms) -> Type)
  enum
  (many SmallerNil : (erased (Nat) d) -> (Smaller d (Nil (Mp))))
  (many SmallerCons : (erased (Nat) d d2) (erased (List (Nat)) e n f) (erased (List (Mp)) ms) (erased (Pbpp d2 e n f) p) (erased (Lt d2 d) lt)
      (erased (Smaller d ms) rest) -> (Smaller d (Cons (Mp) (MkMp d2 e n f) ms))))

; w, of a type W the reduction chooses, is what glue, at a level K below B, needs to colour the map from
; colourings of ms.
(def-adts $ (ColorFrom : ((Level) B) ((Nat) d) ((List (Nat)) e n f) ((List (Mp)) ms) -> Type)
  enum
  (many MkColorFrom : (erased (Level) B K) (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Mp)) ms)
      (erased (TyCtor ((Nat) dw) ((List (Nat)) ew nw fw) ((List (Mp)) mw) -> Type) W) (erased (W d e n f ms) w)
      (erased (Predates (Level) K B) pk)
      (erased (Fn K (erased (Nat) dg) (erased (List (Nat)) eg ng fg) (erased (List (Mp)) mg) (erased (W dg eg ng fg mg) wg)
          (erased (MpCols mg) cs) -> (erased (List (Nat)) ks) (erased (FourColoring eg fg ks) c)) glue)
      -> (ColorFrom B d e n f ms)))

; The map reduces to the maps ms, each smaller and planar, bridgeless, plain and precubic.
(def-adts $ (Reduces : ((Level) B) ((Nat) d) ((List (Nat)) e n f) -> Type)
  enum
  (many MkReduces : (erased (Level) B) (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Mp)) ms) (erased (Smaller d ms) sm)
      (erased (ColorFrom B d e n f ms) g) -> (Reduces B d e n f)))

(def-fns _ $ (erased reduces-lift : (erased (Level) Lo Hi) (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Reduces Lo d e n f) r)
    (erased (Predates (Level) Lo Hi) p) -> (erased (Reduces Hi d e n f) r2))
  (let-match erased r (MkReduces _ _ _ _ _ ms sm g))
  (let-match erased g (MkColorFrom _ K _ _ _ _ _ W w pk glue))
  (MkReduces Hi d e n f ms sm (MkColorFrom Hi K d e n f ms W w (predates-trans pk p) glue)))

(def-fns _ $ (erased smaller-below : (erased (Nat) d b) (subterm erased (List (Mp)) ms) (erased (Smaller d ms) sm) (erased (Lt d (Succ b)) l)
    -> (erased (Smaller b ms) r))
  (let-match erased sm (SmallerCons _ d2 e n f ms1 p lt sm1) ((SmallerNil _) (SmallerNil b)))
  (SmallerCons b d2 e n f ms1 p (lt-le-trans d2 d b lt l) (smaller-below d b ms1 sm1 l)))

; A is the level of the analysis and B the bound of its reductions.
(def-adts $ (Analysis : -> Type)
  enum
  (many MkAnalysis : (erased (Level) A B)
      (erased (Fn A (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Pbpp d e n f) p) (erased (NoColoring e f) nc) -> (erased (Reduces B d e n f) r))
        analyse)
      -> (Analysis)))

(def-fns _ $ (erased four-color-induct : (erased (Analysis) an) -> (erased (Level) D)
    (erased (Fn D (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Pbpp d e n f) p) -> (erased (List (Nat)) ks) (erased (FourColoring e f ks) c))
      col))
  (let-match erased an (MkAnalysis _ B analyse))
  (def-lvl C)
  (let ((erased pb)) (prove-predates B C))
  (def-fns C $ (erased col-all : (subterm erased (Nat) b) (subterm erased (List (Mp)) ms) (erased (Smaller b ms) sm) -> (erased (MpCols ms) cs))
    (let-match erased sm (SmallerCons _ d e n f ms1 p lt sm1) ((SmallerNil _) (MpcNil)))
    (let-match erased p (MkPbpp _ _ _ _ h _ _ _ _))
    (let ((erased ks) (erased c))
      (match erased (color-dec d e n f h) (((List (Nat)) ks) ((FourColoring e f ks) c))
        ((Colors _ _ ks c) (values ks c))
        ((NoColors _ _ nc)
          (let-match erased (analyse d e n f p nc) (MkReduces _ _ _ _ _ ms2 sm2 g))
          (let-match erased g (MkColorFrom _ _ _ _ _ _ _ _ w pk glue))
          (let-match erased b (Succ b1) (absurd (Zero) lt))
          (glue (predates (predates-trans pk pb)) d e n f ms2 w (col-all b1 ms2 (smaller-below d b1 ms2 sm2 lt))))))
    (MpcCons d e n f ks ms1 c (col-all b ms1 sm1)))
  (def-fns _ $ (erased col : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Pbpp d e n f) p) -> (erased (List (Nat)) ks)
      (erased (FourColoring e f ks) c))
    (let ((erased ms)) (Cons (Mp) (MkMp d e n f) (Nil (Mp))))
    (let-match erased (col-all (Succ d) ms (SmallerCons (Succ d) d e n f (Nil _) p (lt-succ d) (SmallerNil _))) (MpcCons _ _ _ _ ks _ c _))
    (values ks c))
  (values (level-of col) col))
