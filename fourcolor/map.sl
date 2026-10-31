; A map on darts 0..n-1: e and nd are the edge and node permutations, as lists indexed by dart.

(def-adts $ (Snoc : (Type A) ((List A) xs) (A a) ((List A) ys) -> Type)
  enum
  (many SnocNil : (erased Type A) (erased A a) -> (Snoc A (Nil A) a (Cons A a (Nil A))))
  (many SnocCons : (erased Type A) (erased A x a) (erased (List A) xs ys) (erased (Snoc A xs a ys) p)
      -> (Snoc A (Cons A x xs) a (Cons A x ys))))

; b is reached from a by steps of the face permutation, nd after e.
(def-adts $ (FaceReach : ((List (Nat)) e) ((List (Nat)) nd) ((Nat) a) ((Nat) b) -> Type)
  enum
  (many FRHere : (erased (List (Nat)) e nd) (erased (Nat) a) -> (FaceReach e nd a a))
  (many FRStep : (erased (List (Nat)) e nd) (erased (Nat) a b c d)
      (erased (Nth (Nat) e a b) pe) (erased (Nth (Nat) nd b c) pn) (erased (FaceReach e nd c d) r)
      -> (FaceReach e nd a d)))

; ls is the suffix of the labelling lab for the darts whose images are listed by xs; each image has the same label.
(def-adts $ (Respects : ((List (Nat)) lab) ((List (Nat)) xs) ((List (Nat)) ls) -> Type)
  enum
  (many RespNil : (erased (List (Nat)) lab) -> (Respects lab (Nil (Nat)) (Nil (Nat))))
  (many RespCons : (erased (List (Nat)) lab xs ls) (erased (Nat) j l) (erased (Nth (Nat) lab j l) p)
      (erased (Respects lab xs ls) rest) -> (Respects lab (Cons (Nat) j xs) (Cons (Nat) l ls))))

; lab is constant along xs and gives d1 and d2 different labels.
(def-adts $ (Separates : ((List (Nat)) lab) ((List (Nat)) xs) ((Nat) d1) ((Nat) d2) -> Type)
  enum
  (many MkSeparates : (erased (List (Nat)) lab xs) (erased (Nat) d1 d2 l1 l2)
      (erased (Respects lab xs lab) r) (erased (Nth (Nat) lab d1 l1) p1) (erased (Nth (Nat) lab d2 l2) p2)
      (erased (Apart (Nat) Lt l1 l2) differ) -> (Separates lab xs d1 d2)))

; The corner after d1 and the corner after d2 may be joined by an edge without changing the genus:
; they lie on one face, or in different components (a labelling constant along e and nd separates them).
(def-adts $ (Joinable : ((List (Nat)) e) ((List (Nat)) nd) ((Nat) d1) ((Nat) d2) -> Type)
  enum
  (many JoinFace : (erased (List (Nat)) e nd) (erased (Nat) d1 d2 c1 c2)
      (erased (Nth (Nat) nd d1 c1) p1) (erased (Nth (Nat) nd d2 c2) p2) (erased (FaceReach e nd c1 c2) r)
      -> (Joinable e nd d1 d2))
  (many JoinApart : (erased (List (Nat)) e nd lab) (erased (Nat) d1 d2)
      (erased (Separates lab e d1 d2) se) (erased (Separates lab nd d1 d2) sn)
      -> (Joinable e nd d1 d2)))

; Inserts a new dart x after d in the node permutation: nd2 is nd with d sent to x and x sent to d's old image.
(def-adts $ (Insert : ((List (Nat)) nd) ((Nat) d) ((Nat) x) ((List (Nat)) nd2) -> Type)
  enum
  (many MkInsert : (erased (List (Nat)) nd nd1 nd2) (erased (Nat) d x c)
      (erased (Nth (Nat) nd d c) p) (erased (SetNth (Nat) nd d x nd1) s) (erased (Snoc (Nat) nd1 c nd2) q)
      -> (Insert nd d x nd2)))

; e2 is e with the two darts n and n+1 of a new edge appended.
(def-adts $ (EdgeGrow : ((List (Nat)) e) ((Nat) n) ((List (Nat)) e2) -> Type)
  enum
  (many MkEdgeGrow : (erased (List (Nat)) e e1 e2) (erased (Nat) n) (erased (Length (Nat) e n) len)
      (erased (Snoc (Nat) e (Succ n) e1) s1) (erased (Snoc (Nat) e1 n e2) s2) -> (EdgeGrow e n e2)))

; Maps of genus 0 without loops, built one edge at a time. Each edge adds the darts n and n+1.
(def-adts $ (PlaneMap : ((List (Nat)) e) ((List (Nat)) nd) -> Type)
  enum
  (many PMNil : -> (PlaneMap (Nil (Nat)) (Nil (Nat))))
  ; An edge with two new vertices.
  (many PMIsolated : (erased (List (Nat)) e nd e2 nd1 nd2) (erased (Nat) n)
      (erased (PlaneMap e nd) m) (erased (EdgeGrow e n e2) g) (erased (Snoc (Nat) nd n nd1) sn1) (erased (Snoc (Nat) nd1 (Succ n) nd2) sn2)
      -> (PlaneMap e2 nd2))
  ; An edge from the corner after d to a new vertex.
  (many PMPendant : (erased (List (Nat)) e nd e2 nd1 nd2) (erased (Nat) n d)
      (erased (PlaneMap e nd) m) (erased (EdgeGrow e n e2) g) (erased (Lt d n) bd)
      (erased (Insert nd d n nd1) i1) (erased (Snoc (Nat) nd1 (Succ n) nd2) sn2)
      -> (PlaneMap e2 nd2))
  ; An edge from the corner after d1 to the corner after d2, at another vertex: a labelling constant along nd separates them.
  (many PMChord : (erased (List (Nat)) e nd e2 nd1 nd2 vl) (erased (Nat) n d1 d2)
      (erased (PlaneMap e nd) m) (erased (EdgeGrow e n e2) g) (erased (Lt d1 n) b1) (erased (Lt d2 n) b2)
      (erased (Separates vl nd d1 d2) loopless)
      (erased (Joinable e nd d1 d2) j)
      (erased (Insert nd d1 n nd1) i1) (erased (Insert nd1 d2 (Succ n) nd2) i2)
      -> (PlaneMap e2 nd2)))

; cs is the suffix of the colouring ks for the darts whose edge and node images are listed by e and nd:
; each such dart has a colour below 4, shared with its node image and apart from its edge image's.
(def-adts $ (Colored : ((List (Nat)) ks) ((List (Nat)) e) ((List (Nat)) nd) ((List (Nat)) cs) -> Type)
  enum
  (many ColoredNil : (erased (List (Nat)) ks) -> (Colored ks (Nil (Nat)) (Nil (Nat)) (Nil (Nat))))
  (many ColoredCons : (erased (List (Nat)) ks e nd cs) (erased (Nat) a b c c2)
      (erased (Lt c 4) bound) (erased (Nth (Nat) ks b c) node) (erased (Nth (Nat) ks a c2) edge)
      (erased (Apart (Nat) Lt c c2) differ) (erased (Colored ks e nd cs) rest)
      -> (Colored ks (Cons (Nat) a e) (Cons (Nat) b nd) (Cons (Nat) c cs))))
