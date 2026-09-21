; self/base.sl -- foundations for the self-hosted compiler (self/README.md): booleans, orders and
; their decisions, Nat/Char/String helpers over the prelude's externs, Nat identifiers and a trie map over them, a
; trie map keyed by names, list helpers and a rope of output chunks. Everything here is plain SL checked
; by the reference interpreter; nothing is settled design.

(def-adts $ Bool : -> Type
  enum
  (many BTrue : -> (Bool))
  (many BFalse : -> (Bool)))

(def-fns _ $ many not : (many (Bool) b) -> (many (Bool) r)
  (match many b _ ((BTrue) (BFalse)) ((BFalse) (BTrue))))

(def-fns _ $ many and : (many (Bool) a) (many (Bool) b) -> (many (Bool) r)
  (match many a _ ((BTrue) b) ((BFalse) (BFalse))))

(def-fns _ $ many or : (many (Bool) a) (many (Bool) b) -> (many (Bool) r)
  (match many a _ ((BTrue) (BTrue)) ((BFalse) b)))

; ---- Nat

(def-fns _ $ many cmp-is-eq : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b) (many (Cmp T R a b) c) -> (many (Bool) r)
  (match many c _ ((CEq eq-t eq-r eq-x) (BTrue)) (else (BFalse))))

(def-fns _ $ many cmp-index : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b) (many (Cmp T R a b) c) -> (many (Nat) i)
  (match many c _ ((CLt t r x y p) 0) ((CEq t r x) 1) ((CGt t r x y q) 2)))

(def-fns _ $ many cmp-is-lt : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b) (many (Cmp T R a b) c) -> (many (Bool) r)
  (match many c _ ((CLt lt-t lt-r lt-x lt-y lt-p) (BTrue)) (else (BFalse))))

(def-fns _ $ many nat-lt : (many (Nat) a) (many (Nat) b) -> (many (Bool) r)
  (cmp-is-lt _ _ _ _ $ nat-cmp a b))

(def-fns _ $ many nat-eq : (many (Nat) a) (many (Nat) b) -> (many (Bool) r)
  (cmp-is-eq _ _ _ _ $ nat-cmp a b))

(def-fns _ $ many nat-pred : (many (Nat) n) -> (many (Nat) m)
  (match many n _ ((Zero) (Zero)) ((Succ k) k)))

(def-fns _ $ many nat-sub : (many (Nat) a) (many (Nat) b) -> (many (Nat) c)
  (match many (lt-dec b (Succ a)) _
    ((Yes x y le) (let (many c) (erased p) (sub a b le)) c)
    ((No x y q) (Zero))))

(def-fns _ $ many nat-is-zero : (many (Nat) n) -> (many (Bool) r)
  (match many n _ ((Zero) (BTrue)) ((Succ k) (BFalse))))

; ---- Char and String

(def-fns _ $ many char-code : (many (Char) c) -> (many (Nat) n)
  (let-match many c (MkChar u))
  (let-match many u (MkU8 k p))
  k)

; A code the modulus does not bound, which no Char holds, becomes NUL.
(def-fns _ $ many char-of-code : (many (Nat) n) -> (many (Char) c)
  (match many (lt-dec n u8-modulus) _
    ((Yes a b p) (MkChar $ MkU8 n p))
    ((No a b q) #\x00)))

(def-fns _ $ many char-eq : (many (Char) a) (many (Char) b) -> (many (Bool) r)
  (cmp-is-eq _ _ _ _ $ char-cmp a b))

(def-fns _ $ many char-is : (many (Char) c) (many (Nat) code) -> (many (Bool) r)
  (nat-eq (char-code c) code))

; code in [lo, hi]
(def-fns _ $ many char-between : (many (Char) c) (many (Nat) lo) (many (Nat) hi) -> (many (Bool) r)
  (let (many n) $ char-code c)
  (and (not $ nat-lt n lo) $ not $ nat-lt hi n))

(def-fns _ $ many rope-str : (many (Rope) r) -> (many (String) s)
  (let (many s) (erased p) (delegate (flatten r)))
  s)

(def-fns _ $ many str-eq : (many (String) a) (many (String) b) -> (many (Bool) r)
  (cmp-is-eq _ _ _ _ $ str-cmp a b))

(def-fns _ $ many str-is-empty : (many (String) s) -> (many (Bool) r)
  (match many s _ ((SNil) (BTrue)) ((SCons c r) (BFalse))))

(def-fns _ $ many str-cat : (many (String) a) (many (String) b) -> (many (String) c)
  (str-append a b))

(def-fns _ $ many str-cat3 : (many (String) a) (many (String) b) (many (String) c) -> (many (String) d)
  (str-append a $ str-append b c))

(def-fns _ $ many nat-list-eq : (subterm many (List $ Nat) a) (many (List $ Nat) b) -> (many (Bool) r)
  (match many a _
    ((Nil t) (match many b _ ((Nil u) (BTrue)) ((Cons u y rest) (BFalse))))
    ((Cons t x rest) (match many b _ ((Nil u) (BFalse)) ((Cons u y rest2) (and (nat-eq x y) $ nat-list-eq rest rest2))))))

; A shape as the FFI's error messages spell it, its arities separated by spaces.
(def-fns _ $ many spell-nats : (subterm many (List $ Nat) ns) -> (many (String) s)
  (match many ns _
    ((Nil a) "")
    ((Cons a n rest)
      (match many rest _
        ((Nil b) (nat-str n))
        ((Cons b m more) (str-cat3 (nat-str n) " " $ spell-nats rest))))))

(def-fns _ $ many all-digits : (subterm many (String) s) -> (many (Bool) r)
  (match many s _
    ((SNil) (BTrue))
    ((SCons c rest) (and (char-between c 48 57) $ all-digits rest))))

; A numeral or a #\c character literal, which no name may spell (section 28, ASSUMPTIONS 51).
(def-fns _ $ many is-literal-name : (many (String) s) -> (many (Bool) r)
  (match many s _
    ((SNil) (BFalse))
    ((SCons c rest)
      (or (all-digits s)
        $ and (char-is c 35) $ match many rest (((Bool) b)) ((SNil) (BFalse)) ((SCons c2 rest2) (char-is c2 92))))))

; The OCaml spelling of a string literal's body: quote, backslash, newline and tab escaped, other bytes
; outside the printable range as decimal escapes.
(def-fns _ $ many ocaml-escape : (subterm many (String) s) -> (many (Rope) r)
  (match many s _
    ((SNil) (REmpty))
    ((SCons c rest)
      (let (many tail) $ ocaml-escape rest)
      (let (many n) $ char-code c)
      (match many (nat-cmp n 34) (((Rope) r))
        ((CEq eq-t eq-r eq-x) (RCat (RChar #\x5c) $ RCat (RChar #\x22) tail))
        (else
          (match many (nat-cmp n 92) (((Rope) r))
            ((CEq eq-t eq-r eq-x) (RCat (RChar #\x5c) $ RCat (RChar #\x5c) tail))
            (else
              (match many (nat-cmp n 10) (((Rope) r))
                ((CEq eq-t eq-r eq-x) (RCat (RChar #\x5c) $ RCat (RChar #\n) tail))
                (else
                  (match many (nat-cmp n 9) (((Rope) r))
                    ((CEq eq-t eq-r eq-x) (RCat (RChar #\x5c) $ RCat (RChar #\t) tail))
                    (else
                      (match many (or (nat-lt n 32) $ nat-lt 126 n) (((Rope) r))
                        ((BTrue)
                          (let (many d) $ RStr $ nat-str n)
                          (let (many (Rope) d3) (match many (nat-lt n 10) _
                                           ((BTrue) (RCat (RChar #\0) $ RCat (RChar #\0) d))
                                           ((BFalse) (match many (nat-lt n 100) (((Rope) p))
                                                       ((BTrue) (RCat (RChar #\0) d))
                                                       ((BFalse) d)))))
                          (RCat (RChar #\x5c) $ RCat d3 tail))
                        ((BFalse) (RCat (RChar c) tail))))))))))))))

; An SL name as an OCaml identifier fragment: letters and digits kept, anything else an underscore.
(def-fns _ $ many sanitize-rope : (subterm many (String) s) -> (many (Rope) r)
  (match many s _
    ((SNil) (REmpty))
    ((SCons c rest)
      (let (many tail) $ sanitize-rope rest)
      (let (many ok) (or (char-between c 48 57)
                        $ or (char-between c 65 90) $ char-between c 97 122))
      (match many ok (((Rope) r))
        ((BTrue) (RCat (RChar c) tail))
        ((BFalse) (RCat (RChar #\_) tail))))))

(def-fns _ $ many sanitize : (many (String) s) -> (many (String) r)
  (rope-str $ sanitize-rope s))

; ---- IdMap: a persistent trie keyed by the halves of a Nat (the prelude's Half)

(def-fns _ $ erased double-lt : (erased (Nat) m) (erased (Nat) d) (subterm erased (Double m d) dd) -> (erased (Lt m (Succ d)) p)
  (match erased dd _
    ((D0) (LtZ (Zero)))
    ((DS m1 d1 dd1) (LtS m1 (Succ (Succ d1)) (lt-weaken m1 (Succ d1) (double-lt m1 d1 dd1))))))

(def-adts
  (IdMap : (Type V) -> Type
    enum
    (many MEmpty : (erased Type V) -> (IdMap V))
    (many MNode : (erased Type V) (many (Maybe V) here) (many (IdMap V) one) (many (IdMap V) two) -> (IdMap V))))

; A lookup's evidence: the key's halves lead to the value, or to an empty map or an empty slot.
(def-adts
  (MapsTo : (Type V) ((Nat) k) (V v) ((IdMap V) m) -> Type
    enum
    (many MTHere : (erased Type V) (erased V v) (erased (IdMap V) one) (erased (IdMap V) two) -> (MapsTo V (Zero) v $ MNode V (Some V v) one two))
    (many MT1 : (erased Type V) (erased (Nat) k) (erased (Nat) d) (erased (Double k d) dd) (erased V v) (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two) (erased (MapsTo V k v one) p) ->
       (MapsTo V (Succ d) v $ MNode V here one two))
    (many MT2 : (erased Type V) (erased (Nat) k) (erased (Nat) d) (erased (Double k d) dd) (erased V v) (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two) (erased (MapsTo V k v two) p) ->
       (MapsTo V (Succ (Succ d)) v $ MNode V here one two)))
  (Absent : (Type V) ((Nat) k) ((IdMap V) m) -> Type
    enum
    (many ABEmpty : (erased Type V) (erased (Nat) k) -> (Absent V k $ MEmpty V))
    (many ABHere : (erased Type V) (erased (IdMap V) one) (erased (IdMap V) two) -> (Absent V (Zero) $ MNode V (None V) one two))
    (many AB1 : (erased Type V) (erased (Nat) k) (erased (Nat) d) (erased (Double k d) dd) (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two) (erased (Absent V k one) p) ->
       (Absent V (Succ d) $ MNode V here one two))
    (many AB2 : (erased Type V) (erased (Nat) k) (erased (Nat) d) (erased (Double k d) dd) (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two) (erased (Absent V k two) p) ->
       (Absent V (Succ (Succ d)) $ MNode V here one two)))
  (Lookup : (Type V) ((Nat) k) ((IdMap V) m) -> Type
    enum
    (many Hit : (erased Type V) (erased (Nat) k) (erased (IdMap V) m) (many V v) (erased (MapsTo V k v m) p) -> (Lookup V k m))
    (many Miss : (erased Type V) (erased (Nat) k) (erased (IdMap V) m) (erased (Absent V k m) p) -> (Lookup V k m))))

(def-fns _ $ many idmap-get : (erased Type V) (many (Nat) k) (subterm many (IdMap V) m) -> (many (Lookup V k m) r)
  (match many m _
    ((MEmpty a) (Miss _ _ _ $ ABEmpty _ k))
    ((MNode a here one two)
      (match many (nat-halve k) _
        ((HZ) (match many here _ ((None b) (Miss _ _ _ $ ABHere _ one two)) ((Some b v) (Hit _ _ _ v $ MTHere _ v one two))))
        ((H1 k1 d dd)
          (match many (idmap-get _ k1 one) _
            ((Hit t kk mm v p) (Hit _ _ _ v $ MT1 _ k1 d dd v here one two p))
            ((Miss t kk mm p) (Miss _ _ _ $ AB1 _ k1 d dd here one two p))))
        ((H2 k1 d dd)
          (match many (idmap-get _ k1 two) _
            ((Hit t kk mm v p) (Hit _ _ _ v $ MT2 _ k1 d dd v here one two p))
            ((Miss t kk mm p) (Miss _ _ _ $ AB2 _ k1 d dd here one two p))))))))

; A value a map holds is a subterm of it, for a recursion that continues into it.
(def-fns _ $ erased mapsto-subterm : (erased Type V) (erased (Nat) k) (erased V v) (erased (IdMap V) m) (subterm erased (MapsTo V k v m) p) ->
    (erased (Subterm V v (IdMap V) m) s)
  (match erased p _
    ((MTHere t w one two) (prove-subterm v m))
    ((MT1 t k1 d dd w here one two q) (subterm-trans (mapsto-subterm _ _ _ _ q) $ prove-subterm one m))
    ((MT2 t k1 d dd w here one two q) (subterm-trans (mapsto-subterm _ _ _ _ q) $ prove-subterm two m))))

(def-fns _ $ many idmap-set : (erased Type V) (subterm many (Nat) k) (many V v) (many (IdMap V) m) -> (many (IdMap V) r)
  (let (many (Maybe V) here) (many (IdMap V) one) (many (IdMap V) two)
    (match many m _
      ((MEmpty a) (values (None _) (MEmpty _) $ MEmpty _))
      ((MNode a h o t) (values h o t))))
  (match many (nat-halve k) _
    ((HZ) (MNode _ (Some _ v) one two))
    ((H1 k1 d dd) (MNode _ here (idmap-set _ (subterm (lt-subterm k1 k $ double-lt k1 d dd)) k1 v one) two))
    ((H2 k1 d dd) (MNode _ here one $ idmap-set _ (subterm (lt-subterm k1 k $ lt-weaken k1 (Succ d) $ double-lt k1 d dd)) k1 v two))))

(def-fns _ $ many idmap-mem : (erased Type V) (many (Nat) k) (many (IdMap V) m) -> (many (Bool) r)
  (match many (idmap-get _ k m) _ ((Miss t k2 m2 p) (BFalse)) ((Hit t k2 m2 v p) (BTrue))))

; ---- NameMap: a persistent trie keyed by a string's characters

(def-adts
  (NameMap : (Type V) -> Type
    enum
    (many NMNode : (erased Type V) (many (Maybe V) here) (many (List $ NMKid V) kids) -> (NameMap V)))
  (NMKid : (Type V) -> Type
    enum
    (many MkKid : (erased Type V) (many (Char) c) (many (NameMap V) sub) -> (NMKid V))))

; A lookup's evidence: a kid for each character, then the value; or no kid for some character, or an empty slot.
(def-adts
  (KidIs : (Type V) ((Char) c) ((NameMap V) sub) ((List $ NMKid V) kids) -> Type
    enum
    (many KHere : (erased Type V) (erased (Char) c) (erased (NameMap V) sub) (erased (List $ NMKid V) rest) -> (KidIs V c sub $ Cons (NMKid V) (MkKid V c sub) rest))
    (many KThere : (erased Type V) (erased (Char) c) (erased (NameMap V) sub) (erased (NMKid V) k) (erased (List $ NMKid V) rest) (erased (KidIs V c sub rest) p) ->
       (KidIs V c sub $ Cons (NMKid V) k rest)))
  (NoKid : (Type V) ((Char) c) ((List $ NMKid V) kids) -> Type
    enum
    (many NKNil : (erased Type V) (erased (Char) c) -> (NoKid V c $ Nil $ NMKid V))
    (many NKLt : (erased Type V) (erased (Char) c) (erased (Char) d) (erased (NameMap V) sub) (erased (List $ NMKid V) rest) (erased (CharLt c d) lt) (erased (NoKid V c rest) p) ->
       (NoKid V c $ Cons (NMKid V) (MkKid V d sub) rest))
    (many NKGt : (erased Type V) (erased (Char) c) (erased (Char) d) (erased (NameMap V) sub) (erased (List $ NMKid V) rest) (erased (CharLt d c) gt) (erased (NoKid V c rest) p) ->
       (NoKid V c $ Cons (NMKid V) (MkKid V d sub) rest)))
  (KidLookup : (Type V) ((Char) c) ((List $ NMKid V) kids) -> Type
    enum
    (many KHit : (erased Type V) (erased (Char) c) (erased (List $ NMKid V) kids) (many (NameMap V) sub) (erased (KidIs V c sub kids) p) -> (KidLookup V c kids))
    (many KMiss : (erased Type V) (erased (Char) c) (erased (List $ NMKid V) kids) (erased (NoKid V c kids) p) -> (KidLookup V c kids)))
  (NMapsTo : (Type V) ((String) name) (V v) ((NameMap V) m) -> Type
    enum
    (many NMHere : (erased Type V) (erased V v) (erased (List $ NMKid V) kids) -> (NMapsTo V (SNil) v $ NMNode V (Some V v) kids))
    (many NMStep : (erased Type V) (erased (Char) c) (erased (String) rest) (erased V v) (erased (Maybe V) here) (erased (List $ NMKid V) kids) (erased (NameMap V) sub)
                   (erased (KidIs V c sub kids) k) (erased (NMapsTo V rest v sub) p) -> (NMapsTo V (SCons c rest) v $ NMNode V here kids)))
  (NAbsent : (Type V) ((String) name) ((NameMap V) m) -> Type
    enum
    (many NAHere : (erased Type V) (erased (List $ NMKid V) kids) -> (NAbsent V (SNil) $ NMNode V (None V) kids))
    (many NANoKid : (erased Type V) (erased (Char) c) (erased (String) rest) (erased (Maybe V) here) (erased (List $ NMKid V) kids) (erased (NoKid V c kids) n) ->
       (NAbsent V (SCons c rest) $ NMNode V here kids))
    (many NAStep : (erased Type V) (erased (Char) c) (erased (String) rest) (erased (Maybe V) here) (erased (List $ NMKid V) kids) (erased (NameMap V) sub)
                   (erased (KidIs V c sub kids) k) (erased (NAbsent V rest sub) p) -> (NAbsent V (SCons c rest) $ NMNode V here kids)))
  (NLookup : (Type V) ((String) name) ((NameMap V) m) -> Type
    enum
    (many NHit : (erased Type V) (erased (String) name) (erased (NameMap V) m) (many V v) (erased (NMapsTo V name v m) p) -> (NLookup V name m))
    (many NMiss : (erased Type V) (erased (String) name) (erased (NameMap V) m) (erased (NAbsent V name m) p) -> (NLookup V name m))))

(def-fns _ $ many nm-empty : (erased Type V) -> (many (NameMap V) m)
  (NMNode _ (None _) $ Nil _))

(def-fns _ $ many nm-kid : (erased Type V) (subterm many (List $ NMKid V) kids) (many (Char) c) -> (many (KidLookup V c kids) r)
  (match many kids _
    ((Nil a) (KMiss _ _ _ $ NKNil _ c))
    ((Cons a k rest)
      (match many k _
        ((MkKid b c1 sub)
          (match many (char-cmp c c1) _
            ((CEq ct cr cx) (KHit _ _ _ sub $ KHere _ c sub rest))
            ((CLt ct cr cx cy lt)
              (match many (nm-kid _ rest c) _
                ((KHit t cc kk sub2 p) (KHit _ _ _ sub2 $ KThere _ c sub2 k rest p))
                ((KMiss t cc kk p) (KMiss _ _ _ $ NKLt _ c c1 sub rest lt p))))
            ((CGt ct cr cx cy gt)
              (match many (nm-kid _ rest c) _
                ((KHit t cc kk sub2 p) (KHit _ _ _ sub2 $ KThere _ c sub2 k rest p))
                ((KMiss t cc kk p) (KMiss _ _ _ $ NKGt _ c c1 sub rest gt p))))))))))

(def-fns _ $ many nm-get : (erased Type V) (subterm many (String) name) (many (NameMap V) m) -> (many (NLookup V name m) r)
  (match many m _
    ((NMNode a here kids)
      (match many name _
        ((SNil) (match many here _ ((None b) (NMiss _ _ _ $ NAHere _ kids)) ((Some b v) (NHit _ _ _ v $ NMHere _ v kids))))
        ((SCons c rest)
          (match many (nm-kid _ kids c) _
            ((KMiss t cc kk n) (NMiss _ _ _ $ NANoKid _ c rest here kids n))
            ((KHit t cc kk sub k)
              (match many (nm-get _ rest sub) _
                ((NHit t2 nn mm v p) (NHit _ _ _ v $ NMStep _ c rest v here kids sub k p))
                ((NMiss t2 nn mm p) (NMiss _ _ _ $ NAStep _ c rest here kids sub k p))))))))))

(def-fns _ $ many nm-replace-kid : (erased Type V) (subterm many (List $ NMKid V) kids) (many (Char) c) (many (NameMap V) sub) -> (many (List $ NMKid V) r)
  (match many kids _
    ((Nil a) (Cons _ (MkKid _ c sub) $ Nil _))
    ((Cons a k rest)
      (match many k _
        ((MkKid b c1 old)
          (match many (char-cmp c c1) _
            ((CEq eq-t eq-r eq-x) (Cons _ (MkKid _ c sub) rest))
            (else (Cons _ k $ nm-replace-kid _ rest c sub))))))))

(def-fns _ $ many nm-set : (erased Type V) (subterm many (String) name) (many V v) (many (NameMap V) m) -> (many (NameMap V) r)
  (match many m _
    ((NMNode a here kids)
      (match many name _
        ((SNil) (NMNode _ (Some _ v) kids))
        ((SCons c rest)
          (let (many (NameMap V) sub) (match many (nm-kid _ kids c) _
                            ((KMiss t cc kk p) (nm-empty _))
                            ((KHit t cc kk s p) s)))
          (NMNode _ here $ nm-replace-kid _ kids c $ nm-set _ rest v sub))))))

; ---- Lists

(def-adts
  (Length : (Type A) ((List A) xs) ((Nat) n) -> Type
    enum
    (many LNil : (erased Type A) -> (Length A (Nil A) (Zero)))
    (many LCons : (erased Type A) (erased A x) (erased (List A) rest) (erased (Nat) n) (erased (Length A rest n) p) -> (Length A (Cons A x rest) (Succ n))))
  (Concat : (Type A) ((List A) xs) ((List A) ys) ((List A) zs) -> Type
    enum
    (many CatNil : (erased Type A) (erased (List A) ys) -> (Concat A (Nil A) ys ys))
    (many CatCons : (erased Type A) (erased A x) (erased (List A) rest) (erased (List A) ys) (erased (List A) zs) (erased (Concat A rest ys zs) p) ->
       (Concat A (Cons A x rest) ys (Cons A x zs))))
  (Nth : (Type A) ((List A) xs) ((Nat) i) (A x) -> Type
    enum
    (many NthHere : (erased Type A) (erased A x) (erased (List A) rest) -> (Nth A (Cons A x rest) (Zero) x))
    (many NthThere : (erased Type A) (erased A y) (erased (List A) rest) (erased (Nat) i) (erased A x) (erased (Nth A rest i x) p) -> (Nth A (Cons A y rest) (Succ i) x)))
  (OutOfRange : (Type A) ((List A) xs) ((Nat) i) -> Type
    enum
    (many OONil : (erased Type A) (erased (Nat) i) -> (OutOfRange A (Nil A) i))
    (many OOCons : (erased Type A) (erased A y) (erased (List A) rest) (erased (Nat) i) (erased (OutOfRange A rest i) p) -> (OutOfRange A (Cons A y rest) (Succ i))))
  (NthLookup : (Type A) ((List A) xs) ((Nat) i) -> Type
    enum
    (many NthHit : (erased Type A) (erased (List A) xs) (erased (Nat) i) (many A x) (erased (Nth A xs i x) p) -> (NthLookup A xs i))
    (many NthMiss : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased (OutOfRange A xs i) p) -> (NthLookup A xs i))))

(def-fns _ $ many length : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n) (erased (Length A xs n) p)
  (match many xs _
    ((Nil a) (values (Zero) (LNil _)))
    ((Cons a x rest)
      (let (many n) (erased p) (length _ rest))
      (values (Succ n) (LCons _ x rest n p)))))

(def-fns _ $ many list-replicate : (erased Type A) (subterm many (Nat) n) (many A x) -> (many (List A) r)
  (match many n _
    ((Zero) (Nil _))
    ((Succ k) (Cons _ x $ list-replicate _ k x))))

(def-fns _ $ many list-length : (erased Type A) (many (List A) xs) -> (many (Nat) n)
  (let (many n) (erased p) (delegate (length _ xs)))
  n)

; Two lists of one length, entry by entry.
(def-adts
  (Lockstep : (Type A) (Type B) ((List A) xs) ((List B) ys) -> Type
    enum
    (many LsNil : (erased Type A) (erased Type B) -> (Lockstep A B (Nil A) (Nil B)))
    (many LsCons : (erased Type A) (erased Type B) (erased A x) (erased B y) (erased (List A) xs) (erased (List B) ys) (erased (Lockstep A B xs ys) p) ->
       (Lockstep A B (Cons A x xs) (Cons B y ys)))))

(def-fns _ $ erased lockstep-trans : (erased Type A) (erased Type B) (erased Type C) (erased (List A) xs) (erased (List B) ys) (erased (List C) zs)
    (subterm erased (Lockstep A B xs ys) p) (erased (Lockstep B C ys zs) q) -> (erased (Lockstep A C xs zs) r)
  (match erased p _
    ((LsNil a b)
      (let-match erased q (LsNil c d))
      (LsNil _ _))
    ((LsCons a b x y xs2 ys2 p2)
      (let-match erased q (LsCons c d y2 z ys3 zs2 q2))
      (LsCons _ _ x z xs2 zs2 $ lockstep-trans _ _ _ _ _ _ p2 q2))))

(def-fns _ $ erased lockstep-sym : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) (subterm erased (Lockstep A B xs ys) p) -> (erased (Lockstep B A ys xs) q)
  (match erased p _
    ((LsNil a b) (LsNil _ _))
    ((LsCons a b x y xs2 ys2 p2) (LsCons _ _ y x ys2 xs2 $ lockstep-sym _ _ _ _ p2))))

(def-adts
  (LockstepDec : (Type A) (Type B) ((List A) xs) ((List B) ys) -> Type
    enum
    (many LdYes : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) (erased (Lockstep A B xs ys) p) -> (LockstepDec A B xs ys))
    (many LdNo : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) -> (LockstepDec A B xs ys))))

(def-fns _ $ many lockstep-dec : (erased Type A) (erased Type B) (subterm many (List A) xs) (many (List B) ys) -> (many (LockstepDec A B xs ys) r)
  (match many xs _
    ((Nil a) (match many ys _ ((Nil b) (LdYes _ _ _ _ $ LsNil _ _)) ((Cons b y yrest) (LdNo _ _ _ _))))
    ((Cons a x xrest)
      (match many ys _
        ((Nil b) (LdNo _ _ _ _))
        ((Cons b y yrest)
          (match many (lockstep-dec _ _ xrest yrest) _
            ((LdYes c d e f p) (LdYes _ _ _ _ $ LsCons _ _ x y xrest yrest p))
            ((LdNo c d e f) (LdNo _ _ _ _))))))))

(def-fns _ $ many list-fit : (erased Type A) (erased Type B) (subterm many (List A) xs) (many (List B) ys) (many B filler) -> (many (List B) r) (erased (Lockstep A B xs r) p)
  (match many xs _
    ((Nil a) (values (Nil _) (LsNil _ _)))
    ((Cons a x rest)
      (let (many y) (many yrest) $ match many ys ((B y0) ((List B) ys0)) ((Nil b) (values filler $ Nil _)) ((Cons b y yrest) (values y yrest)))
      (let (many r) (erased p) $ list-fit _ _ rest yrest filler)
      (values (Cons _ y r) (LsCons _ _ x y rest r p)))))

(def-fns _ $ many list-rev-onto : (erased Type A) (subterm many (List A) xs) (many (List A) acc) -> (many (List A) r)
  (match many xs _
    ((Nil a) acc)
    ((Cons a x rest) (list-rev-onto _ rest $ Cons _ x acc))))

(def-fns _ $ many list-rev : (erased Type A) (many (List A) xs) -> (many (List A) r)
  (list-rev-onto _ xs $ Nil _))

(def-fns _ $ many list-append : (erased Type A) (subterm many (List A) xs) (many (List A) ys) -> (many (List A) zs) (erased (Concat A xs ys zs) p)
  (match many xs _
    ((Nil a) (values ys (CatNil _ ys)))
    ((Cons a x rest)
      (let (many zs) (erased p) (list-append _ rest ys))
      (values (Cons _ x zs) (CatCons _ x rest ys zs p)))))

(def-fns _ $ many list-nth : (erased Type A) (subterm many (List A) xs) (many (Nat) i) -> (many (NthLookup A xs i) r)
  (match many xs _
    ((Nil a) (NthMiss _ _ _ $ OONil _ i))
    ((Cons a x rest)
      (match many i _
        ((Zero) (NthHit _ _ _ x $ NthHere _ x rest))
        ((Succ k)
          (match many (list-nth _ rest k) _
            ((NthHit t l j y p) (NthHit _ _ _ y $ NthThere _ x rest k y p))
            ((NthMiss t l j p) (NthMiss _ _ _ $ OOCons _ x rest k p))))))))

(def-fns _ $ many list-nth-or : (erased Type A) (many (List A) xs) (many (Nat) i) (many A dflt) -> (many A r)
  (match many (list-nth _ xs i) _ ((NthHit t l j x p) x) ((NthMiss t l j p) dflt)))

(def-fns _ $ many list1 : (erased Type A) (many A x) -> (many (List A) r)
  (Cons _ x $ Nil _))

(def-fns _ $ many list-is-empty : (erased Type A) (many (List A) xs) -> (many (Bool) r)
  (match many xs _ ((Nil a) (BTrue)) ((Cons a x rest) (BFalse))))

(def-fns _ $ many is-some : (erased Type A) (many (Maybe A) m) -> (many (Bool) r)
  (match many m _ ((Some a x) (BTrue)) ((None a) (BFalse))))

(def-fns _ $ many list-mem-str : (subterm many (List $ String) xs) (many (String) x) -> (many (Bool) r)
  (match many xs _
    ((Nil a) (BFalse))
    ((Cons a y rest) (match many (str-eq x y) _ ((BTrue) (BTrue)) ((BFalse) (list-mem-str rest x))))))

(def-fns _ $ many index-of-bin : (subterm many (List $ Nat) xs) (many (Nat) x) (many (Nat) i) -> (many (Maybe $ Nat) r)
  (match many xs _
    ((Nil a) (None _))
    ((Cons a y rest)
      (match many (nat-eq x y) _
        ((BTrue) (Some _ i))
        ((BFalse) (index-of-bin rest x $ Succ i))))))

(def-fns _ $ many list-mem-bin : (subterm many (List $ Nat) xs) (many (Nat) x) -> (many (Bool) r)
  (is-some _ $ index-of-bin xs x 0))

; ---- Rope: output built as a tree of chunks (the prelude's), flattened once

(def-fns _ $ many rcat : (many (Rope) a) (many (Rope) b) -> (many (Rope) r)
  (RCat a b))

(def-fns _ $ many rcat3 : (many (Rope) a) (many (Rope) b) (many (Rope) c) -> (many (Rope) r)
  (RCat a $ RCat b c))

(def-fns _ $ many rcat4 : (many (Rope) a) (many (Rope) b) (many (Rope) c) (many (Rope) d) -> (many (Rope) r)
  (RCat a $ RCat b $ RCat c d))

(def-fns _ $ many rcat5 : (many (Rope) a) (many (Rope) b) (many (Rope) c) (many (Rope) d) (many (Rope) e) -> (many (Rope) r)
  (RCat a $ RCat b $ RCat c $ RCat d e))

(def-fns _ $ many rwrap : (many (String) open) (many (Rope) body) (many (String) close) -> (many (Rope) r)
  (rcat3 (RStr open) body $ RStr close))

; Ropes joined by a separator.
(def-fns _ $ many rjoin : (subterm many (List $ Rope) rs) (many (String) sep) -> (many (Rope) r)
  (match many rs _
    ((Nil a) (REmpty))
    ((Cons a r rest)
      (match many rest _
        ((Nil b) r)
        ((Cons b r2 rest2) (RCat r $ RCat (RStr sep) $ rjoin rest sep))))))

(def-fns _ $ many rlist : (subterm many (List $ Rope) rs) -> (many (Rope) r)
  (match many rs _
    ((Nil a) (REmpty))
    ((Cons a r rest) (RCat r $ rlist rest))))

; ---- lemmas over the prelude's Lt and Double, shared with heap.sl and core.sl's fact table

(def-fns _ $ erased lt-zero : (erased (Nat) a) (erased (Lt a (Zero)) p) -> (erased (False) f)
  (match erased p _ (absurd LtZ) (absurd LtS)))

(def-fns _ $ erased le-trans : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Lt a (Succ b)) p) (erased (Lt b (Succ c)) q) -> (erased (Lt a (Succ c)) r)
  (lt-le-trans a (Succ b) (Succ c) p (LtS b (Succ c) q)))

(def-fns _ $ erased double-lt-inv : (erased (Nat) m) (erased (Nat) d) (erased (Nat) l) (erased (Nat) s) (subterm erased (Double m d) p) (erased (Double l s) q) (erased (Lt d s) lt) -> (erased (Lt m l) r)
  (match erased p _
    ((D0)
      (match erased q _
        (absurd (D0) (lt-zero d lt))
        ((DS l1 s1 q1) (LtZ l1))))
    ((DS m1 d1 p1)
      (match erased q _
        (absurd (D0) (lt-zero d lt))
        ((DS l1 s1 q1)
          (let-match erased lt (LtS x y lt1))
          (let-match erased lt1 (LtS x2 y2 lt2))
          (LtS m1 l1 (double-lt-inv m1 d1 l1 s1 p1 q1 lt2)))))))


; ---- a trie's size against a bound on its keys, the measure a walk over one recurses on

(def-fns _ $ erased lt-drop : (erased (Nat) d) (erased (Nat) s) (erased (Lt (Succ d) s) p) -> (erased (Lt d s) q)
  (let-match erased p (LtS x y q))
  (lt-weaken d y q))

(def-fns _ $ erased double-le-inv : (erased (Nat) m) (erased (Nat) d) (erased (Nat) r) (erased (Nat) s) (erased (Double m d) p) (erased (Double r s) q) (erased (Lt d (Succ s)) lt) -> (erased (Lt m (Succ r)) res)
  (double-lt-inv m d (Succ r) (Succ (Succ s)) p (DS r s q) (lt-weaken d (Succ s) lt)))

(def-adts $ Braun : ((Nat) l) ((Nat) r) -> Type
  enum
  (many BrEq : (erased (Nat) n) -> (Braun n n))
  (many BrOne : (erased (Nat) n) -> (Braun (Succ n) n)))

(def-fns _ $ erased half-lt-one : (erased (Nat) m) (erased (Nat) d) (erased (Nat) l) (erased (Nat) r) (erased (Nat) s) (erased (Double m d) dd) (erased (Add l r s) sum) (erased (Braun l r) bal) (erased (Lt d s) lt) -> (erased (Lt m l) res)
  (match erased bal _
    ((BrEq n) (double-lt-inv m d n s dd (add-diag-double n s sum) lt))
    ((BrOne n)
      (let-match erased sum (AddSucc a1 b1 c1 q))
      (double-le-inv m d n c1 dd (add-diag-double n c1 q) lt))))

(def-fns _ $ erased half-lt-two : (erased (Nat) m) (erased (Nat) d) (erased (Nat) l) (erased (Nat) r) (erased (Nat) s) (erased (Double m d) dd) (erased (Add l r s) sum) (erased (Braun l r) bal) (erased (Lt (Succ d) s) lt) -> (erased (Lt m r) res)
  (match erased bal _
    ((BrEq n) (double-lt-inv m d n s dd (add-diag-double n s sum) (lt-drop d s lt)))
    ((BrOne n)
      (let-match erased sum (AddSucc a1 b1 c1 q))
      (let-match erased lt (LtS x y lt1))
      (double-lt-inv m d n c1 dd (add-diag-double n c1 q) lt1))))

; [size] how many entries a trie holds, [max] a bound every key in it is below. The node case splits
; max the way the trie splits keys: key 0 sits here, 2m+1 in one, 2m+2 in two, so a node bounded by
; Succ m1 has children bounded by l and r with l + r = m1 and l either r or r + 1.
(def-adts $ Bounded : (Type V) ((IdMap V) m) ((Nat) size) ((Nat) max) -> Type
  enum
  (many BdEmpty : (erased Type V) (erased (Nat) max) -> (Bounded V (MEmpty V) (Zero) max))
  (many BdNone : (erased Type V) (erased (IdMap V) one) (erased (IdMap V) two)
     (erased (Nat) l) (erased (Nat) r) (erased (Nat) m1) (erased (Add l r m1) sum) (erased (Braun l r) bal)
     (erased (Nat) so) (erased (Bounded V one so l) bo) (erased (Nat) st) (erased (Bounded V two st r) bt)
     (erased (Nat) sot) (erased (Add so st sot) ssum) -> (Bounded V (MNode V (None V) one two) sot (Succ m1)))
  (many BdSome : (erased Type V) (erased V v) (erased (IdMap V) one) (erased (IdMap V) two)
     (erased (Nat) l) (erased (Nat) r) (erased (Nat) m1) (erased (Add l r m1) sum) (erased (Braun l r) bal)
     (erased (Nat) so) (erased (Bounded V one so l) bo) (erased (Nat) st) (erased (Bounded V two st r) bt)
     (erased (Nat) sot) (erased (Add so st sot) ssum) -> (Bounded V (MNode V (Some V v) one two) (Succ sot) (Succ m1))))

(def-fns _ $ erased add-le-right : (erased (Nat) x) (erased (Nat) y) (erased (Nat) z)
    (subterm erased (Add x y z) p) -> (erased (Lt y (Succ z)) r)
  (match erased p _
    ((AddZero b) (lt-succ y))
    ((AddSucc a b c q) (lt-weaken y (Succ c) (add-le-right a b c q)))))

; sums are monotone: a <= x and b <= y give a + b <= x + y
(def-fns _ $ erased add-mono : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Add a b c) p)
    (erased (Nat) x) (erased (Nat) y) (erased (Nat) z) (erased (Add x y z) q)
    (erased (Lt a (Succ x)) la) (erased (Lt b (Succ y)) lb) -> (erased (Lt c (Succ z)) r)
  (match erased p _
    ((AddZero b0) (le-trans b y z lb (add-le-right x y z q)))
    ((AddSucc a0 b0 c0 p0)
      (match erased q _
        (absurd (AddZero y0)
          (match erased la (((False) f)) ((LtS u v la0) (lt-zero a0 la0))))
        ((AddSucc x0 y0 z0 q0)
          (let-match erased la (LtS u v la0))
          (LtS c0 (Succ z0) (add-mono a0 b0 c0 p0 x0 y0 z0 q0 la0 lb)))))))

; the point: a trie bounded by max holds at most max entries
(def-fns _ $ erased bounded-le : (erased Type V) (erased (IdMap V) m) (erased (Nat) size) (erased (Nat) max)
    (subterm erased (Bounded V m size max) b) -> (erased (Lt size (Succ max)) r)
  (match erased b _
    ((BdEmpty t mx) (LtZ mx))
    ((BdNone t one two l r m1 sum bal so bo st bt sot ssum)
      (lt-weaken sot (Succ m1) (add-mono so st sot ssum l r m1 sum (bounded-le _ one so l bo) (bounded-le _ two st r bt))))
    ((BdSome t v one two l r m1 sum bal so bo st bt sot ssum)
      (LtS sot (Succ m1) (add-mono so st sot ssum l r m1 sum (bounded-le _ one so l bo) (bounded-le _ two st r bt))))))

; ---- reading an Absent witness at the child the key's halving leads to

(def-fns _ $ erased absent-not-some : (erased Type V) (erased V v) (erased (IdMap V) one) (erased (IdMap V) two)
    (erased (Absent V (Zero) (MNode V (Some V v) one two)) ab) -> (erased (False) f)
  (match erased ab (((False) f))))

(def-fns _ $ erased absent-one : (erased Type V) (erased (Nat) k1) (erased (Nat) d) (erased (Double k1 d) dd)
    (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two)
    (erased (Absent V (Succ d) (MNode V here one two)) ab) -> (erased (Absent V k1 one) r)
  (match erased ab _
    ((AB1 t k2 d2 dd2 h2 o2 t2 sub)
      (match erased (double-inj k1 k2 d dd dd2) _ ((Refl ty x) sub)))
    (absurd (AB2 t k2 d2 dd2 h2 o2 t2 sub) (double-parity k1 k2 d2 dd dd2))))

(def-fns _ $ erased absent-two : (erased Type V) (erased (Nat) k1) (erased (Nat) d) (erased (Double k1 d) dd)
    (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two)
    (erased (Absent V (Succ (Succ d)) (MNode V here one two)) ab) -> (erased (Absent V k1 two) r)
  (match erased ab _
    (absurd (AB1 t k2 d2 dd2 h2 o2 t2 sub) (double-parity k2 k1 d dd2 dd))
    ((AB2 t k2 d2 dd2 h2 o2 t2 sub)
      (match erased (double-inj k1 k2 d dd dd2) _ ((Refl ty x) sub)))))

; ---- splitting a bound the way the trie splits keys
(def-fns _ $ erased split-bound : (subterm erased (Nat) m1) ->
    (erased (Nat) l) (erased (Nat) r) (erased (Add l r m1) sum) (erased (Braun l r) bal)
  (match erased m1 _
    ((Zero) (values (Zero) (Zero) (AddZero (Zero)) (BrEq (Zero))))
    ((Succ m0)
      (let (erased l0) (erased r0) (erased sum0) (erased bal0) (split-bound m0))
      (values (Succ r0) l0 (AddSucc r0 l0 m0 (add-comm l0 r0 m0 sum0))
        (match erased bal0 (((Braun (Succ r0) l0) b))
          ((BrEq n) (BrOne n))
          ((BrOne n) (BrEq (Succ n))))))))

(def-fns _ $ erased lt-succ-inv : (erased (Nat) a) (erased (Nat) b) (erased (Lt (Succ a) (Succ b)) p) ->
    (erased (Lt a b) q)
  (let-match erased p (LtS x y q))
  q)

; a bound a key sits under is a successor, and splits the way the trie does
(def-fns _ $ erased bound-split : (erased (Nat) max) (erased (Nat) k) (erased (Lt k max) lk) ->
    (erased (Nat) m1) (erased (Eq (Nat) max (Succ m1)) e)
    (erased (Nat) l) (erased (Nat) r) (erased (Add l r m1) sum) (erased (Braun l r) bal)
  (match erased lk _
    ((LtZ b)
      (let (erased l) (erased r) (erased s) (erased ba) (split-bound b))
      (values b (Refl (Nat) (Succ b)) l r s ba))
    ((LtS x y p)
      (let (erased l) (erased r) (erased s) (erased ba) (split-bound y))
      (values y (Refl (Nat) (Succ y)) l r s ba))))

; inserting a key the trie lacks, below its bound: the size goes up by exactly one
(def-fns _ $ many idmap-set-bd : (erased Type V) (subterm many (Nat) k) (many V v) (many (IdMap V) m)
    (erased (Nat) size) (erased (Nat) max) (erased (Bounded V m size max) bd)
    (erased (Absent V k m) ab) (erased (Lt k max) lk) ->
    (many (IdMap V) m2) (erased (Bounded V m2 (Succ size) max) bd2)
  (match many m _
    ((MEmpty ta)
      (let (erased m1) (erased eqm) (erased l) (erased r) (erased sum) (erased bal) (bound-split max k lk))
      (match erased eqm (((IdMap V) r2) ((Bounded V r2 (Succ size) max) b2))
        ((Refl ty xx)
          (match erased bd (((IdMap V) r2) ((Bounded V r2 (Succ size) max) b2))
            ((BdEmpty t2 mx)
              (match many (nat-halve k) (((IdMap V) r2) ((Bounded V r2 (Succ (Zero)) (Succ m1)) b2))
                ((HZ)
                  (values (MNode _ (Some _ v) (MEmpty _) (MEmpty _))
                    (BdSome _ v _ _ l r m1 sum bal (Zero) (BdEmpty _ l) (Zero) (BdEmpty _ r) (Zero) (AddZero (Zero)))))
                ((H1 k1 d dd)
                  (let (many o2) (erased bo2)
                    (idmap-set-bd _ (subterm (lt-subterm k1 k $ double-lt k1 d dd)) k1 v (MEmpty _) (Zero) l
                      (BdEmpty _ l) (ABEmpty _ k1) (half-lt-one k1 d l r m1 dd sum bal (lt-succ-inv d m1 lk))))
                  (values (MNode _ (None _) o2 (MEmpty _))
                    (BdNone _ _ _ l r m1 sum bal (Succ (Zero)) bo2 (Zero) (BdEmpty _ r) (Succ (Zero))
                      (AddSucc (Zero) (Zero) (Zero) (AddZero (Zero))))))
                ((H2 k1 d dd)
                  (let (many t2b) (erased bt2)
                    (idmap-set-bd _ (subterm (lt-subterm k1 k $ lt-weaken k1 (Succ d) $ double-lt k1 d dd)) k1 v (MEmpty _) (Zero) r
                      (BdEmpty _ r) (ABEmpty _ k1) (half-lt-two k1 d l r m1 dd sum bal (lt-succ-inv (Succ d) m1 lk))))
                  (values (MNode _ (None _) (MEmpty _) t2b)
                    (BdNone _ _ _ l r m1 sum bal (Zero) (BdEmpty _ l) (Succ (Zero)) bt2 (Succ (Zero))
                      (AddZero (Succ (Zero))))))))))))
    ((MNode ta here one two)
      (match many here (((IdMap V) rr) ((Bounded V rr (Succ size) max) b2))
        ((None tb)
          (match erased bd (((IdMap V) rr) ((Bounded V rr (Succ size) max) b2))
            ((BdNone t2 oo tt l r m1 sum bal so bo st bt sot ssum)
              (match many (nat-halve k) (((IdMap V) rr) ((Bounded V rr (Succ sot) (Succ m1)) b2))
                ((HZ)
                  (values (MNode _ (Some _ v) one two)
                    (BdSome _ v _ _ l r m1 sum bal so bo st bt sot ssum)))
                ((H1 k1 d dd)
                  (let (many onew) (erased bonew)
                    (idmap-set-bd _ (subterm (lt-subterm k1 k $ double-lt k1 d dd)) k1 v one so l bo
                      (absent-one _ k1 d dd here one two ab)
                      (half-lt-one k1 d l r m1 dd sum bal (lt-succ-inv d m1 lk))))
                  (values (MNode _ (None _) onew two)
                    (BdNone _ _ _ l r m1 sum bal (Succ so) bonew st bt (Succ sot) (AddSucc so st sot ssum))))
                ((H2 k1 d dd)
                  (let (many tnew) (erased btnew)
                    (idmap-set-bd _ (subterm (lt-subterm k1 k $ lt-weaken k1 (Succ d) $ double-lt k1 d dd)) k1 v two st r bt
                      (absent-two _ k1 d dd here one two ab)
                      (half-lt-two k1 d l r m1 dd sum bal (lt-succ-inv (Succ d) m1 lk))))
                  (values (MNode _ (None _) one tnew)
                    (BdNone _ _ _ l r m1 sum bal so bo (Succ st) btnew (Succ sot) (add-succ-right so st sot ssum))))))))
        ((Some tb v0)
          (match erased bd (((IdMap V) rr) ((Bounded V rr (Succ size) max) b2))
            ((BdSome t2 v2 oo tt l r m1 sum bal so bo st bt sot ssum)
              (match many (nat-halve k) (((IdMap V) rr) ((Bounded V rr (Succ (Succ sot)) (Succ m1)) b2))
                (absurd (HZ) (absent-not-some _ v0 one two ab))
                ((H1 k1 d dd)
                  (let (many onew) (erased bonew)
                    (idmap-set-bd _ (subterm (lt-subterm k1 k $ double-lt k1 d dd)) k1 v one so l bo
                      (absent-one _ k1 d dd here one two ab)
                      (half-lt-one k1 d l r m1 dd sum bal (lt-succ-inv d m1 lk))))
                  (values (MNode _ (Some _ v0) onew two)
                    (BdSome _ v0 _ _ l r m1 sum bal (Succ so) bonew st bt (Succ sot) (AddSucc so st sot ssum))))
                ((H2 k1 d dd)
                  (let (many tnew) (erased btnew)
                    (idmap-set-bd _ (subterm (lt-subterm k1 k $ lt-weaken k1 (Succ d) $ double-lt k1 d dd)) k1 v two st r bt
                      (absent-two _ k1 d dd here one two ab)
                      (half-lt-two k1 d l r m1 dd sum bal (lt-succ-inv (Succ d) m1 lk))))
                  (values (MNode _ (Some _ v0) one tnew)
                    (BdSome _ v0 _ _ l r m1 sum bal so bo (Succ st) btnew (Succ sot) (add-succ-right so st sot ssum))))))))))))

; size + rest = max with size < max: rest is a successor, so it is what a walk can recurse on
(def-fns _ $ erased add-room : (erased (Nat) size) (erased (Nat) rest) (erased (Nat) max)
    (subterm erased (Add size rest max) sum) (erased (Lt size max) lt) ->
    (erased (Nat) rest2) (erased (Add (Succ size) rest2 max) sum2) (erased (Lt rest2 rest) less)
  (match erased sum _
    ((AddZero b)
      (let-match erased lt (LtZ b2))
      (values b2 (AddSucc (Zero) b2 b2 (AddZero b2)) (lt-succ b2)))
    ((AddSucc a b c q)
      (let (erased rest2) (erased sum2) (erased less) (add-room a b c q (lt-succ-inv a c lt)))
      (values rest2 (AddSucc (Succ a) rest2 c sum2) less))))

; the whole step: insert a fresh key and hand back the strictly smaller measure
(def-fns _ $ many seen-add : (erased Type V) (many (Nat) k) (many V v) (many (IdMap V) m)
    (erased (Nat) size) (erased (Nat) rest) (erased (Nat) max) (erased (Bounded V m size max) bd)
    (erased (Add size rest max) sum) (erased (Absent V k m) ab) (erased (Lt k max) lk) ->
    (many (IdMap V) m2) (erased (Nat) rest2) (erased (Bounded V m2 (Succ size) max) bd2)
    (erased (Add (Succ size) rest2 max) sum2) (erased (Lt rest2 rest) less)
  (let (many m2) (erased bd2) (idmap-set-bd _ k v m size max bd ab lk))
  (let (erased rest2) (erased sum2) (erased less)
    (add-room size rest max sum (lt-succ-inv size max (bounded-le _ m2 (Succ size) max bd2))))
  (values m2 rest2 bd2 sum2 less))

; ---- A generic merge sort, in the shape of tests/map.sl's factory: the comparison is a parameter,
; so the sort sits above its level and the factory mints the level relating them. The split is a
; Braun-shaped pile built by insertion, so every recursion here is structural.

(def-adts $ Pile : (Type A) -> Type
  enum
  (many PLeaf : (erased Type A) -> (Pile A))
  (many PNode : (erased Type A) (many A x) (many (Pile A) l) (many (Pile A) r) -> (Pile A)))

(def-fns _ $ many pile-add : (erased Type A) (many A x) (subterm many (Pile A) t) -> (many (Pile A) r)
  (match many t _
    ((PLeaf a) (PNode A x (PLeaf A) (PLeaf A)))
    ((PNode a y l rr) (PNode A x (pile-add A y rr) l))))

(def-fns _ $ many pile-of : (erased Type A) (subterm many (List A) xs) (many (Pile A) t) -> (many (Pile A) r)
  (match many xs _
    ((Nil a) t)
    ((Cons a x rest) (tail (pile-of A rest (pile-add A x t))))))

(def-fns _ $ many rev-onto : (erased Type A) (subterm many (List A) acc) (many (List A) ys) -> (many (List A) r)
  (match many acc _
    ((Nil a) ys)
    ((Cons a x rest) (tail (rev-onto A rest (Cons A x ys))))))

(def-fns _ $ many sort-factory : (erased (Level) M) ->
    (erased (Level) L)
    (many (Fn L (erased Type A)
              (many (Fn M (many A x) (many A y) -> (many (Bool) b)) leq)
              (many (List A) xs) ->
              (many (List A) ys))
          sorted)
  ; lexicographic: the first list shrinks, or it passes on unchanged and the second shrinks
  ; [acc] the output so far, newest first, so the merge itself runs in constant stack
  (def-fns _ $ many merge : (erased Type A)
      (many (Fn M (many A x) (many A y) -> (many (Bool) b)) leq)
      (subterm many (List A) xs) (subterm many (List A) ys) (many (List A) acc) -> (many (List A) zs)
    (match many xs (((List A) r))
      ((Nil a) (tail (rev-onto A acc ys)))
      ((Cons a x xr)
        (match many ys (((List A) r))
          ((Nil b) (tail (rev-onto A acc xs)))
          ((Cons b y yr)
            (match many (leq x y) (((List A) r))
              ((BTrue) (tail (merge A leq xr ys (Cons A x acc))))
              ((BFalse) (tail (merge A leq xs yr (Cons A y acc))))))))))
  (def-fns _ $ many pile-sort : (erased Type A)
      (many (Fn M (many A x) (many A y) -> (many (Bool) b)) leq)
      (subterm many (Pile A) t) -> (many (List A) r)
    (match many t _
      ((PLeaf a) (Nil A))
      ((PNode a x l rr)
        (merge A leq (Cons A x $ Nil A) (merge A leq (pile-sort A leq l) (pile-sort A leq rr) (Nil A)) (Nil A)))))
  (def-fns _ $ many sort : (erased Type A)
      (many (Fn M (many A x) (many A y) -> (many (Bool) b)) leq)
      (many (List A) xs) -> (many (List A) ys)
    (pile-sort A leq (pile-of A xs (PLeaf A))))
  (values (level-of sort) sort))
