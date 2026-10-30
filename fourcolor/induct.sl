; four_color_hypermap's induction on the number of darts, with minimality as data: a map the search finds uncolourable is
; reduced (Reduces) to strictly smaller maps, whose four-colourings a function at a fixed level turns into one of the map.
; Load after coloring.sl.

(def-adts $ (SubMap : -> Type)
  enum
  (many MkSubMap : (erased (Nat) d) (erased (List (Nat)) e n f) -> (SubMap)))

; planar_bridgeless_plain_precubic, with genus 0 for planar.
(def-adts $ (Pbpp : ((Nat) d) ((List (Nat)) e n f) -> Type)
  enum
  (many MkPbpp : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) (erased (Genus d e n f (Zero)) g)
      (erased (Bridgeless d e n f) b) (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (Precubic d n) pc) -> (Pbpp d e n f)))

; Each map of ms is planar, bridgeless, plain and precubic, on fewer than d darts.
(def-adts $ (Smaller : ((Nat) d) ((List (SubMap)) ms) -> Type)
  enum
  (many SmNil : (erased (Nat) d) -> (Smaller d (Nil (SubMap))))
  (many SmCons : (erased (Nat) d d2) (erased (List (Nat)) e n f) (erased (List (SubMap)) ms) (erased (Pbpp d2 e n f) p) (erased (Lt d2 d) lt)
      (erased (Smaller d ms) rest) -> (Smaller d (Cons (SubMap) (MkSubMap d2 e n f) ms))))

(def-adts $ (Colorings : ((List (SubMap)) ms) -> Type)
  enum
  (many ColNil : -> (Colorings (Nil (SubMap))))
  (many ColCons : (erased (Nat) d) (erased (List (Nat)) e n f ks) (erased (List (SubMap)) ms) (erased (FourColoring e f ks) c)
      (erased (Colorings ms) rest) -> (Colorings (Cons (SubMap) (MkSubMap d e n f) ms))))

; The map reduces to the maps ms: w, of a type W the reduction chooses, is what glue, a function at a level K below B, needs
; to turn four-colourings of ms into one of the map.
(def-adts $ (Reduces : ((Level) B) ((Nat) d) ((List (Nat)) e n f) -> Type)
  enum
  (many MkReduces : (erased (Level) B K) (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (SubMap)) ms) (erased (Smaller d ms) sm)
      (erased (TyCtor ((Nat) dw) ((List (Nat)) ew nw fw) ((List (SubMap)) mw) -> Type) W) (erased (W d e n f ms) w)
      (erased (Predates (Level) K B) pk)
      (erased (Fn K (erased (Nat) dg) (erased (List (Nat)) eg ng fg) (erased (List (SubMap)) mg) (erased (W dg eg ng fg mg) wg)
          (erased (Colorings mg) cs) -> (erased (List (Nat)) ks) (erased (FourColoring eg fg ks) c)) glue)
      -> (Reduces B d e n f)))

(def-fns _ $ (erased reduces-lift : (erased (Level) Lo Hi) (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Reduces Lo d e n f) r)
    (erased (Predates (Level) Lo Hi) p) -> (erased (Reduces Hi d e n f) r2))
  (let-match erased r (MkReduces _ K _ _ _ _ ms sm W w pk glue))
  (MkReduces Hi K d e n f ms sm W w (predates-trans pk p) glue))

(def-fns _ $ (erased smaller-below : (erased (Nat) d b) (subterm erased (List (SubMap)) ms) (erased (Smaller d ms) sm) (erased (Lt d (Succ b)) l)
    -> (erased (Smaller b ms) r))
  (let-match erased sm (SmCons _ d2 e n f ms1 p lt sm1) ((SmNil _) (SmNil b)))
  (SmCons b d2 e n f ms1 p (lt-le-trans d2 d b lt l) (smaller-below d b ms1 sm1 l)))

; The step of four_color_hypermap left open: every planar bridgeless plain precubic map the search finds uncolourable
; reduces, with the level of the analysis and the bound of its reductions as fields.
(def-adts $ (Analysis : -> Type)
  enum
  (many MkAnalysis : (erased (Level) A B)
      (erased (Fn A (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Pbpp d e n f) p) (erased (NoColoring e f) nc) -> (erased (Reduces B d e n f) r))
        analyse)
      -> (Analysis)))

; With an analysis, every planar bridgeless plain precubic map is four-colourable. col-all colours the maps of a list below
; a bound b, each found by the search or glued from the colourings of the maps of its reduction, below a smaller bound.
(def-fns _ $ (erased four-color-induct : (erased (Analysis) an) -> (erased (Level) D)
    (erased (Fn D (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Pbpp d e n f) p) -> (erased (List (Nat)) ks) (erased (FourColoring e f ks) c))
      col))
  (let-match erased an (MkAnalysis A B analyse))
  (def-lvl C)
  (let ((erased pb)) (prove-predates B C))
  (def-fns C $ (erased col-all : (subterm erased (Nat) b) (subterm erased (List (SubMap)) ms) (erased (Smaller b ms) sm) -> (erased (Colorings ms) cs))
    (let-match erased sm (SmCons _ d e n f ms1 p lt sm1) ((SmNil _) (ColNil)))
    (let-match erased p (MkPbpp _ _ _ _ h _ _ _ _))
    (let ((erased ks) (erased c))
      (match erased (decide-colorable d e n f h) (((List (Nat)) ks) ((FourColoring e f ks) c))
        ((Colorable _ _ ks c) (values ks c))
        ((Uncolorable _ _ nc)
          (let-match erased (analyse d e n f p nc) (MkReduces _ K _ _ _ _ ms2 sm2 W w pk glue))
          (let-match erased b (Succ b1) (absurd (Zero) lt))
          (glue (predates (predates-trans pk pb)) d e n f ms2 w (col-all b1 ms2 (smaller-below d b1 ms2 sm2 lt))))))
    (ColCons d e n f ks ms1 c (col-all b ms1 sm1)))
  (def-fns _ $ (erased col : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Pbpp d e n f) p) -> (erased (List (Nat)) ks)
      (erased (FourColoring e f ks) c))
    (let ((erased ms)) (Cons (SubMap) (MkSubMap d e n f) (Nil (SubMap))))
    (let-match erased (col-all (Succ d) ms (SmCons (Succ d) d e n f (Nil _) p (lt-succ d) (SmNil _))) (ColCons _ _ _ _ ks _ c _))
    (values ks c))
  (values (level-of col) col))
