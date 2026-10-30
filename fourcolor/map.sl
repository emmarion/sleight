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

(def-adts $ (NodeReach : ((List (Nat)) nd) ((Nat) a) ((Nat) b) -> Type)
  enum
  (many NRHere : (erased (List (Nat)) nd) (erased (Nat) a) -> (NodeReach nd a a))
  (many NRStep : (erased (List (Nat)) nd) (erased (Nat) a b c)
      (erased (Nth (Nat) nd a b) pn) (erased (NodeReach nd b c) r) -> (NodeReach nd a c)))

; b is reached from a by steps of e and nd.
(def-adts $ (Conn : ((List (Nat)) e) ((List (Nat)) nd) ((Nat) a) ((Nat) b) -> Type)
  enum
  (many CHere : (erased (List (Nat)) e nd) (erased (Nat) a) -> (Conn e nd a a))
  (many CEdge : (erased (List (Nat)) e nd) (erased (Nat) a b c)
      (erased (Nth (Nat) e a b) p) (erased (Conn e nd b c) r) -> (Conn e nd a c))
  (many CNode : (erased (List (Nat)) e nd) (erased (Nat) a b c)
      (erased (Nth (Nat) nd a b) p) (erased (Conn e nd b c) r) -> (Conn e nd a c)))

; The corner after d1 and the corner after d2 may be joined by an edge without changing the genus:
; they lie on one face, or in different components.
(def-adts $ (Joinable : ((List (Nat)) e) ((List (Nat)) nd) ((Nat) d1) ((Nat) d2) -> Type)
  enum
  (many JoinFace : (erased (List (Nat)) e nd) (erased (Nat) d1 d2 c1 c2)
      (erased (Nth (Nat) nd d1 c1) p1) (erased (Nth (Nat) nd d2 c2) p2) (erased (FaceReach e nd c1 c2) r)
      -> (Joinable e nd d1 d2))
  (many JoinApart : (erased (List (Nat)) e nd) (erased (Nat) d1 d2) (erased (Level) L)
      (erased (Fn L (erased (Conn e nd d1 d2) c) -> (erased (False) f)) apart)
      -> (Joinable e nd d1 d2)))

; Inserts a new dart x after d in the node permutation: nd2 is nd with d sent to x and x sent to d's old image.
(def-adts $ (Insert : ((List (Nat)) nd) ((Nat) d) ((Nat) x) ((List (Nat)) nd2) -> Type)
  enum
  (many MkInsert : (erased (List (Nat)) nd nd1 nd2) (erased (Nat) d x c)
      (erased (Nth (Nat) nd d c) p) (erased (SetNth (Nat) nd d x nd1) s) (erased (Snoc (Nat) nd1 c nd2) q)
      -> (Insert nd d x nd2)))

; Maps of genus 0 without loops, built one edge at a time. Each edge adds the darts n and n+1.
(def-adts $ (PlaneMap : ((List (Nat)) e) ((List (Nat)) nd) -> Type)
  enum
  (many PMNil : -> (PlaneMap (Nil (Nat)) (Nil (Nat))))
  ; An edge with two new vertices.
  (many PMIsolated : (erased (List (Nat)) e nd e1 e2 nd1 nd2) (erased (Nat) n)
      (erased (PlaneMap e nd) m) (erased (Length (Nat) e n) len)
      (erased (Snoc (Nat) e (Succ n) e1) se1) (erased (Snoc (Nat) e1 n e2) se2)
      (erased (Snoc (Nat) nd n nd1) sn1) (erased (Snoc (Nat) nd1 (Succ n) nd2) sn2)
      -> (PlaneMap e2 nd2))
  ; An edge from the corner after d to a new vertex.
  (many PMPendant : (erased (List (Nat)) e nd e1 e2 nd1 nd2) (erased (Nat) n d)
      (erased (PlaneMap e nd) m) (erased (Length (Nat) e n) len) (erased (Lt d n) bd)
      (erased (Snoc (Nat) e (Succ n) e1) se1) (erased (Snoc (Nat) e1 n e2) se2)
      (erased (Insert nd d n nd1) i1) (erased (Snoc (Nat) nd1 (Succ n) nd2) sn2)
      -> (PlaneMap e2 nd2))
  ; An edge from the corner after d1 to the corner after d2, at another vertex.
  (many PMChord : (erased (List (Nat)) e nd e1 e2 nd1 nd2) (erased (Nat) n d1 d2) (erased (Level) L)
      (erased (PlaneMap e nd) m) (erased (Length (Nat) e n) len) (erased (Lt d1 n) b1) (erased (Lt d2 n) b2)
      (erased (Fn L (erased (NodeReach nd d1 d2) r) -> (erased (False) f)) loopless)
      (erased (Joinable e nd d1 d2) j)
      (erased (Snoc (Nat) e (Succ n) e1) se1) (erased (Snoc (Nat) e1 n e2) se2)
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

; Every plane map has a proper vertex colouring with 4 colours.
(def-adts $ (FourColorMap : -> Type)
  enum
  (many MkFourColorMap : (erased (Level) L)
      (erased (Fn L (erased (List (Nat)) e nd) (erased (PlaneMap e nd) m) ->
          (erased (List (Nat)) ks) (erased (Colored ks e nd ks) c)) thm)
      -> (FourColorMap)))
