; self/base.sl -- foundations for the self-hosted compiler (self/README.md): booleans, orders and
; their decisions, Nat/Char/String helpers over the prelude's externs, Nat identifiers and a trie map over them, a
; trie map keyed by names, list helpers and a rope of output chunks. Everything here is plain Sleight checked
; by the reference interpreter; nothing is settled design.

(def-fns _ $ (many not : (many (Bool) b) -> (many (Bool) r))
  (match many b _ ((BTrue) (BFalse)) ((BFalse) (BTrue))))

; ---- Nat

(def-fns _ $ (many cmp-is-eq : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b) (many (Cmp T R a b) c) -> (many (Bool) r))
  (match many c _ ((CEq _ _ _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many cmp-index : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b) (many (Cmp T R a b) c) -> (many (Nat) i))
  (match many c _ ((CLt _ _ _ _ _) 0) ((CEq _ _ _) 1) ((CGt _ _ _ _ _) 2)))

(def-fns _ $ (many cmp-is-lt : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b) (many (Cmp T R a b) c) -> (many (Bool) r))
  (match many c _ ((CLt _ _ _ _ _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many nat-lt : (many (Nat) a) (many (Nat) b) -> (many (Bool) r))
  (cmp-is-lt _ _ _ _ $ nat-cmp a b))

(def-fns _ $ (many nat-eq : (many (Nat) a) (many (Nat) b) -> (many (Bool) r))
  (cmp-is-eq _ _ _ _ $ nat-cmp a b))

(def-fns _ $ (many nat-pred : (many (Nat) n) -> (many (Nat) m))
  (match many n _ ((Zero) (Zero)) ((Succ k) k)))

(def-fns _ $ (many nat-sub : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (let-match many (lt-dec b (Succ a)) (Yes _ _ le)
    ((No _ _ _) (Zero)))
  (let ((many c) (erased _)) (sub a b le))
  c)

(def-fns _ $ (many nat-is-zero : (many (Nat) n) -> (many (Bool) r))
  (match many n _ ((Zero) (BTrue)) ((Succ _) (BFalse))))

; ---- Char and String

(def-fns _ $ (many char-code : (many (Char) c) -> (many (Nat) n))
  (let-match many c (MkChar u))
  (let-match many u (MkU8 k _))
  k)

; A code the modulus does not bound, which no Char holds, becomes NUL.
(def-fns _ $ (many char-of-code : (many (Nat) n) -> (many (Char) c))
  (match many (lt-dec n u8-modulus) _
    ((Yes _ _ p) (MkChar $ MkU8 n p))
    ((No _ _ _) #\x00)))

(def-fns _ $ (many char-eq : (many (Char) a) (many (Char) b) -> (many (Bool) r))
  (cmp-is-eq _ _ _ _ $ char-cmp a b))

(def-fns _ $ (many char-is : (many (Char) c) (many (Nat) code) -> (many (Bool) r))
  (nat-eq (char-code c) code))

; code in [lo, hi]
(def-fns _ $ (many char-between : (many (Char) c) (many (Nat) lo) (many (Nat) hi) -> (many (Bool) r))
  (let ((many n)) $ char-code c)
  (and (not $ nat-lt n lo) $ not $ nat-lt hi n))

(def-fns _ $ (many rope-str at flatten : (many (Rope) r) -> (many (String) s))
  (let ((many s) (erased _)) (delegate (flatten r)))
  s)

(def-fns _ $ (many str-eq : (many (String) a) (many (String) b) -> (many (Bool) r))
  (cmp-is-eq _ _ _ _ $ str-cmp a b))

(def-fns _ $ (many str-is-empty : (many (String) s) -> (many (Bool) r))
  (match many s _ ((SNil) (BTrue)) ((SCons _ _) (BFalse))))

(def-fns _ $ (many str-cat : (many (String) a) (many (String) b) -> (many (String) c))
  (str-append a b))

(def-fns _ $ (many str-cat3 : (many (String) a) (many (String) b) (many (String) c) -> (many (String) d))
  (str-append a $ str-append b c))

(def-fns _ $ (many str-starts : (subterm many (String) p) (many (String) s) -> (many (Bool) r))
  (let-match many p (SCons c prest) ((SNil) (BTrue)))
  (let-match many s (SCons d srest) ((SNil) (BFalse)))
  (match many (char-is d $ char-code c) _ ((BTrue) (tail $ str-starts prest srest)) ((BFalse) (BFalse))))

(def-fns _ $ (many str-contains : (subterm many (String) s) (many (String) p) -> (many (Bool) r))
  (let-match many (str-starts p s) (BFalse) ((BTrue) (BTrue)))
  (let-match many s (SCons _ rest) ((SNil) (BFalse)))
  (tail $ str-contains rest p))

(def-fns _ $ (many str-until-onto : (many (Rope) acc) (subterm many (String) s) (many (Nat) code) -> (many (String) before) (many (Maybe $ String) after))
  (let-match many s (SCons c rest) ((SNil) (values (rope-str acc) (None _))))
  (match many (char-is c code) _
    ((BTrue) (values (rope-str acc) (Some _ rest)))
    ((BFalse) (tail (str-until-onto (RCat acc $ RChar c) rest code)))))

(def-fns _ $ (many str-until : (many (String) s) (many (Nat) code) -> (many (String) before) (many (Maybe $ String) after))
  (str-until-onto (REmpty) s code))

(def-fns _ $ (many str-split-fuel : (subterm many (Nat) fuel) (many (String) s) (many (Nat) code) -> (many (List $ String) r))
  (let ((many b) (many a)) (str-until s code))
  (let-match many a (Some _ rest) ((None _) (Cons _ b $ Nil _)))
  (match many fuel _
    ((Zero) (Cons _ b $ Nil _))
    ((Succ f) (Cons _ b $ notail $ str-split-fuel f rest code))))

(def-fns _ $ (many split-on : (many (String) s) (many (Nat) code) -> (many (List $ String) r))
  (let ((many n) (erased _)) (str-length s))
  (str-split-fuel n s code))

(def-fns _ $ (many nat-list-eq : (subterm many (List $ Nat) a) (many (List $ Nat) b) -> (many (Bool) r))
  (match many a _
    ((Nil _) (match many b _ ((Nil _) (BTrue)) ((Cons _ _ _) (BFalse))))
    ((Cons _ x rest) (match many b _ ((Nil _) (BFalse)) ((Cons _ y rest2) (and (nat-eq x y) $ tail $ nat-list-eq rest rest2))))))

; A shape as the FFI's error messages spell it, its arities separated by spaces.
(def-fns _ $ (many spell-nats : (subterm many (List $ Nat) ns) -> (many (String) s))
  (let-match many ns (Cons _ n rest) ((Nil _) ""))
  (match many rest _
    ((Nil _) (nat-str n))
    ((Cons _ _ _) (str-cat3 (nat-str n) " " $ notail $ spell-nats rest))))

(def-fns _ $ (many all-digits : (subterm many (String) s) -> (many (Bool) r))
  (match many s _
    ((SNil) (BTrue))
    ((SCons c rest) (and (char-between c 48 57) $ tail $ all-digits rest))))

; A numeral or a #\c character literal, which no name may spell (section 1, ASSUMPTIONS 51).
(def-fns _ $ (many is-literal-name : (many (String) s) -> (many (Bool) r))
  (let-match many s (SCons c rest) ((SNil) (BFalse)))
  (or (all-digits s)
    $ and (char-is c 35) $ match many rest (((Bool) _)) ((SNil) (BFalse)) ((SCons c2 _) (char-is c2 92))))

(def-fns _ $ (many is-reserved-name : (many (String) s) -> (many (Bool) r))
  (str-starts "__" s))

(def-adts $ (LitKind : -> Type)
  enum
  (many LName : -> (LitKind))
  (many LNumeral : -> (LitKind))
  (many LChar : -> (LitKind)))

(def-fns _ $ (many classify : (many (String) s) -> (many (LitKind) k))
  (let-match many s (SCons c rest) ((SNil) (LName)))
  (let-match many (all-digits s) (BFalse) ((BTrue) (LNumeral)))
  (match many (and (char-is c 35) $ match many rest (((Bool) _)) ((SNil) (BFalse)) ((SCons c2 _) (char-is c2 92))) _
    ((BTrue) (LChar))
    ((BFalse) (LName))))

(def-fns _ $ (many parse-nat : (many (String) s) -> (many (Nat) n))
  (match many (str-nat s) _ ((Some _ n) n) ((None _) 0)))

(def-fns _ $ (many is-hex : (many (Char) c) -> (many (Bool) r))
  (or (char-between c 48 57) $ or (char-between c 97 102) $ char-between c 65 70))

(def-fns _ $ (many hex-digit : (many (Char) c) -> (many (Nat) d))
  (let ((many n)) $ char-code c)
  (let-match many (char-between c 48 57) (BFalse) ((BTrue) (nat-sub n 48)))
  (match many (char-between c 97 102) _
    ((BTrue) (nat-sub n 87))
    ((BFalse) (nat-sub n 55))))

(def-fns _ $ (many char-lit-body : (many (String) s) -> (many (String) body))
  (let-match many s (SCons _ rest) ((SNil) (SNil)))
  (match many rest _ ((SNil) (SNil)) ((SCons _ rest2) rest2)))

; The code of #\c, #\space, #\newline, #\tab or #\xHH, or None where the literal is malformed.
(def-fns _ $ (many char-lit-code : (many (String) s) -> (many (Maybe $ Nat) n))
  (let ((many body)) $ char-lit-body s)
  (match many (str-cmp body "space") _
    ((CEq _ _ _) (Some _ 32))
    (else
      (match many (str-cmp body "newline") _
        ((CEq _ _ _) (Some _ 10))
        (else
          (match many (str-cmp body "tab") _
            ((CEq _ _ _) (Some _ 9))
            (else
              (let-match many body (SCons c rest) ((SNil) (None _)))
              (let-match many rest (SCons h1 rest2) ((SNil) (Some _ $ char-code c)))
              (let-match many rest2 (SCons h2 rest3) ((SNil) (None _)))
              (match many (and (char-is c 120) $ and (is-hex h1) $ and (is-hex h2) $ str-is-empty rest3) _
                ((BTrue) (Some _ $ nat-add (nat-mul 16 $ hex-digit h1) $ hex-digit h2))
                ((BFalse) (None _))))))))))

; What is wrong with a literal's spelling, if anything (lib/literal.ml's classify).
(def-fns _ $ (many literal-error : (many (String) s) -> (many (Maybe $ String) r))
  (match many (classify s) _
    ((LName) (None _))
    ((LNumeral)
      (let-match many s (SCons c rest) ((SNil) (None _)))
      (match many (and (char-is c 48) $ not $ str-is-empty rest) _
        ((BTrue) (Some _ $ str-cat s " has a leading zero"))
        ((BFalse) (None _))))
    ((LChar)
      (match many (char-lit-code s) _
        ((Some _ _) (None _))
        ((None _) (Some _ $ str-cat "malformed character literal " s))))))

; The OCaml spelling of a string literal's body: quote, backslash, newline and tab escaped, other bytes
; outside the printable range as decimal escapes.
(def-fns _ $ (many ocaml-escape-char : (many (Char) c) -> (many (Rope) r))
  (let ((many n)) $ char-code c)
  (match many (nat-cmp n 34) (((Rope) _))
    ((CEq _ _ _) (RCat (RChar #\x5c) $ RChar #\x22))
    (else
      (match many (nat-cmp n 92) (((Rope) _))
        ((CEq _ _ _) (RCat (RChar #\x5c) $ RChar #\x5c))
        (else
          (match many (nat-cmp n 10) (((Rope) _))
            ((CEq _ _ _) (RCat (RChar #\x5c) $ RChar #\n))
            (else
              (match many (nat-cmp n 9) (((Rope) _))
                ((CEq _ _ _) (RCat (RChar #\x5c) $ RChar #\t))
                (else
                  (let-match many (or (nat-lt n 32) $ nat-lt 126 n) (BTrue) ((BFalse) (RChar c)))
                  (let ((many d)) $ RStr $ nat-str n)
                  (let ((many (Rope) d3)) (match many (nat-lt n 10) _
                                   ((BTrue) (RCat (RChar #\0) $ RCat (RChar #\0) d))
                                   ((BFalse) (match many (nat-lt n 100) (((Rope) _))
                                               ((BTrue) (RCat (RChar #\0) d))
                                               ((BFalse) d)))))
                  (RCat (RChar #\x5c) d3))))))))))

(def-fns _ $ (many ocaml-escape-onto : (many (Rope) acc) (subterm many (String) s) -> (many (Rope) r))
  (let-match many s (SCons c rest) ((SNil) acc))
  (tail $ ocaml-escape-onto (RCat acc $ ocaml-escape-char c) rest))

(def-fns _ $ (many ocaml-escape : (many (String) s) -> (many (Rope) r))
  (ocaml-escape-onto (REmpty) s))

; An Sleight name as an OCaml identifier fragment: letters and digits kept, anything else an underscore.
(def-fns _ $ (many sanitize-char : (many (Char) c) -> (many (Char) r))
  (let ((many ok)) (or (char-between c 48 57)
                    $ or (char-between c 65 90) $ char-between c 97 122))
  (match many ok _ ((BTrue) c) ((BFalse) #\_)))

(def-fns _ $ (many sanitize-onto : (many (Rope) acc) (subterm many (String) s) -> (many (Rope) r))
  (let-match many s (SCons c rest) ((SNil) acc))
  (tail $ sanitize-onto (RCat acc $ RChar $ sanitize-char c) rest))

(def-fns _ $ (many sanitize : (many (String) s) -> (many (String) r))
  (rope-str $ sanitize-onto (REmpty) s))

; ---- IdMap: a persistent trie keyed by the halves of a Nat (the prelude's Half)

(def-adts
  ((IdMap : (Type V) -> Type)
    enum
    (many MEmpty : (erased Type V) -> (IdMap V))
    (many MNode : (erased Type V) (many (Maybe V) here) (many (IdMap V) one) (many (IdMap V) two) -> (IdMap V))))

; A lookup's evidence: the key's halves lead to the value, or to an empty map or an empty slot.
(def-adts
  ((MapsTo : (Type V) ((Nat) k) (V v) ((IdMap V) m) -> Type)
    enum
    (many MTHere : (erased Type V) (erased V v) (erased (IdMap V) one) (erased (IdMap V) two) -> (MapsTo V (Zero) v $ MNode V (Some V v) one two))
    (many MT1 : (erased Type V) (erased (Nat) k) (erased (Nat) d) (erased (Double k d) dd) (erased V v) (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two) (erased (MapsTo V k v one) p)
       -> (MapsTo V (Succ d) v $ MNode V here one two))
    (many MT2 : (erased Type V) (erased (Nat) k) (erased (Nat) d) (erased (Double k d) dd) (erased V v) (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two) (erased (MapsTo V k v two) p)
       -> (MapsTo V (Succ (Succ d)) v $ MNode V here one two)))
  ((Absent : (Type V) ((Nat) k) ((IdMap V) m) -> Type)
    enum
    (many ABEmpty : (erased Type V) (erased (Nat) k) -> (Absent V k $ MEmpty V))
    (many ABHere : (erased Type V) (erased (IdMap V) one) (erased (IdMap V) two) -> (Absent V (Zero) $ MNode V (None V) one two))
    (many AB1 : (erased Type V) (erased (Nat) k) (erased (Nat) d) (erased (Double k d) dd) (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two) (erased (Absent V k one) p)
       -> (Absent V (Succ d) $ MNode V here one two))
    (many AB2 : (erased Type V) (erased (Nat) k) (erased (Nat) d) (erased (Double k d) dd) (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two) (erased (Absent V k two) p)
       -> (Absent V (Succ (Succ d)) $ MNode V here one two)))
  ((Lookup : (Type V) ((Nat) k) ((IdMap V) m) -> Type)
    enum
    (many Hit : (erased Type V) (erased (Nat) k) (erased (IdMap V) m) (many V v) (erased (MapsTo V k v m) p) -> (Lookup V k m))
    (many Miss : (erased Type V) (erased (Nat) k) (erased (IdMap V) m) (erased (Absent V k m) p) -> (Lookup V k m))))

(def-fns _ $ (many idmap-get : (erased Type V) (many (Nat) k) (subterm many (IdMap V) m) -> (many (Lookup V k m) r))
  (let-match many m (MNode _ here one two) ((MEmpty _) (Miss _ _ _ $ ABEmpty _ k)))
  (match many (nat-halve k) _
    ((HZ) (match many here _ ((None _) (Miss _ _ _ $ ABHere _ one two)) ((Some _ v) (Hit _ _ _ v $ MTHere _ v one two))))
    ((H1 k1 d dd)
      (let ((many r)) (tail $ idmap-get _ k1 one))
      (let ((erased _) (erased c)) $ match erased r (((Lookup V k m) r2) ((Coercible (Shared) (Lookup V k1 one) r (Shared) (Lookup V k m) r2) c))
        ((Hit _ _ _ v p) (values (Hit _ _ _ v $ MT1 _ k1 d dd v here one two p) (coercible-ctor (Shared) Hit V V k1 k one m (coercible-refl (Shared) v) p $ MT1 _ k1 d dd v here one two p)))
        ((Miss _ _ _ p) (values (Miss _ _ _ $ AB1 _ k1 d dd here one two p) (coercible-ctor (Shared) Miss V V k1 k one m p $ AB1 _ k1 d dd here one two p))))
      (coerce r c))
    ((H2 k1 d dd)
      (let ((many r)) (tail $ idmap-get _ k1 two))
      (let ((erased _) (erased c)) $ match erased r (((Lookup V k m) r2) ((Coercible (Shared) (Lookup V k1 two) r (Shared) (Lookup V k m) r2) c))
        ((Hit _ _ _ v p) (values (Hit _ _ _ v $ MT2 _ k1 d dd v here one two p) (coercible-ctor (Shared) Hit V V k1 k two m (coercible-refl (Shared) v) p $ MT2 _ k1 d dd v here one two p)))
        ((Miss _ _ _ p) (values (Miss _ _ _ $ AB2 _ k1 d dd here one two p) (coercible-ctor (Shared) Miss V V k1 k two m p $ AB2 _ k1 d dd here one two p))))
      (coerce r c))))

; A value a map holds is a subterm of it, for a recursion that continues into it.
(def-fns _ $ (erased mapsto-subterm : (erased Type V) (erased (Nat) k) (erased V v) (erased (IdMap V) m) (subterm erased (MapsTo V k v m) p) ->
    (erased (Subterm V v (IdMap V) m) s))
  (match erased p _
    ((MTHere _ _ _ _) (prove-subterm v m))
    ((MT1 _ _ _ _ _ _ one _ q) (subterm-trans (mapsto-subterm _ _ _ _ q) $ prove-subterm one m))
    ((MT2 _ _ _ _ _ _ _ two q) (subterm-trans (mapsto-subterm _ _ _ _ q) $ prove-subterm two m))))

(def-fns _ $ (many idmap-set : (erased Type V) (subterm many (Nat) k) (many V v) (many (IdMap V) m) -> (many (IdMap V) r))
  (let ((many (Maybe V) here) (many (IdMap V) one) (many (IdMap V) two))
    (match many m _
      ((MEmpty _) (values (None _) (MEmpty _) $ MEmpty _))
      ((MNode _ h o t) (values h o t))))
  (match many (nat-halve k) _
    ((HZ) (MNode _ (Some _ v) one two))
    ((H1 k1 d dd) (MNode _ here (notail $ idmap-set _ (subterm (lt-subterm k1 k $ double-lt k1 d dd)) k1 v one) two))
    ((H2 k1 d dd) (MNode _ here one $ notail $ idmap-set _ (subterm (lt-subterm k1 k $ lt-weaken k1 (Succ d) $ double-lt k1 d dd)) k1 v two))))

(def-fns _ $ (many idmap-mem : (erased Type V) (many (Nat) k) (many (IdMap V) m) -> (many (Bool) r))
  (match many (idmap-get _ k m) _ ((Miss _ _ _ _) (BFalse)) ((Hit _ _ _ _ _) (BTrue))))

(def-fns _ $ (many idmap-of-list : (erased Type V) (subterm many (List V) xs) (many (Nat) k) (many (IdMap V) acc) -> (many (IdMap V) r))
  (let-match many xs (Cons _ x rest) ((Nil _) acc))
  (tail $ idmap-of-list _ rest (Succ k) $ idmap-set _ k x acc))

(def-fns _ $ (many idmap-prefix : (erased Type V) (many (IdMap V) m) (subterm many (Nat) n) (many (List V) acc) -> (many (List V) r))
  (let-match many n (Succ k) ((Zero) acc))
  (tail $ idmap-prefix _ m k $ match many (idmap-get _ k m) (((List V) _)) ((Hit _ _ _ v _) (Cons _ v acc)) ((Miss _ _ _ _) acc)))

(def-fns _ $ (many idmap-pairs : (erased Type V) (subterm many (IdMap V) m) (many (Nat) a) (many (Nat) b) (many (List $ Pair (Nat) V) acc) -> (many (List $ Pair (Nat) V) r))
  (let-match many m (MNode _ here one two) ((MEmpty _) acc))
  (let ((many a2)) $ nat-add a a)
  (let ((many (List $ Pair (Nat) V) acc2)) $ match many here _ ((None _) acc) ((Some _ v) (Cons _ (MkPair _ _ b v) acc)))
  (tail $ idmap-pairs _ two a2 (nat-add a2 b) $ notail $ idmap-pairs _ one a2 (nat-add a b) acc2))

; ---- NameMap: a persistent trie keyed by a string's characters

(def-adts
  ((NameMap : (Type V) -> Type)
    enum
    (many NMNode : (erased Type V) (many (Maybe V) here) (many (List $ NMKid V) kids) -> (NameMap V)))
  ((NMKid : (Type V) -> Type)
    enum
    (many MkKid : (erased Type V) (many (Char) c) (many (NameMap V) submap) -> (NMKid V))))

; A lookup's evidence: a kid for each character, then the value; or no kid for some character, or an empty slot.
(def-adts
  ((KidIs : (Type V) ((Char) c) ((NameMap V) submap) ((List $ NMKid V) kids) -> Type)
    enum
    (many KHere : (erased Type V) (erased (Char) c) (erased (NameMap V) submap) (erased (List $ NMKid V) rest) -> (KidIs V c submap $ Cons (NMKid V) (MkKid V c submap) rest))
    (many KThere : (erased Type V) (erased (Char) c) (erased (NameMap V) submap) (erased (NMKid V) k) (erased (List $ NMKid V) rest) (erased (KidIs V c submap rest) p)
       -> (KidIs V c submap $ Cons (NMKid V) k rest)))
  ((NoKid : (Type V) ((Char) c) ((List $ NMKid V) kids) -> Type)
    enum
    (many NKNil : (erased Type V) (erased (Char) c) -> (NoKid V c $ Nil $ NMKid V))
    (many NKLt : (erased Type V) (erased (Char) c) (erased (Char) d) (erased (NameMap V) submap) (erased (List $ NMKid V) rest) (erased (CharLt c d) lt) (erased (NoKid V c rest) p)
       -> (NoKid V c $ Cons (NMKid V) (MkKid V d submap) rest))
    (many NKGt : (erased Type V) (erased (Char) c) (erased (Char) d) (erased (NameMap V) submap) (erased (List $ NMKid V) rest) (erased (CharLt d c) gt) (erased (NoKid V c rest) p)
       -> (NoKid V c $ Cons (NMKid V) (MkKid V d submap) rest)))
  ((KidLookup : (Type V) ((Char) c) ((List $ NMKid V) kids) -> Type)
    enum
    (many KHit : (erased Type V) (erased (Char) c) (erased (List $ NMKid V) kids) (many (NameMap V) submap) (erased (KidIs V c submap kids) p) -> (KidLookup V c kids))
    (many KMiss : (erased Type V) (erased (Char) c) (erased (List $ NMKid V) kids) (erased (NoKid V c kids) p) -> (KidLookup V c kids)))
  ((NMapsTo : (Type V) ((String) name) (V v) ((NameMap V) m) -> Type)
    enum
    (many NMHere : (erased Type V) (erased V v) (erased (List $ NMKid V) kids) -> (NMapsTo V (SNil) v $ NMNode V (Some V v) kids))
    (many NMStep : (erased Type V) (erased (Char) c) (erased (String) rest) (erased V v) (erased (Maybe V) here) (erased (List $ NMKid V) kids) (erased (NameMap V) submap)
                   (erased (KidIs V c submap kids) k) (erased (NMapsTo V rest v submap) p) -> (NMapsTo V (SCons c rest) v $ NMNode V here kids)))
  ((NAbsent : (Type V) ((String) name) ((NameMap V) m) -> Type)
    enum
    (many NAHere : (erased Type V) (erased (List $ NMKid V) kids) -> (NAbsent V (SNil) $ NMNode V (None V) kids))
    (many NANoKid : (erased Type V) (erased (Char) c) (erased (String) rest) (erased (Maybe V) here) (erased (List $ NMKid V) kids) (erased (NoKid V c kids) n)
       -> (NAbsent V (SCons c rest) $ NMNode V here kids))
    (many NAStep : (erased Type V) (erased (Char) c) (erased (String) rest) (erased (Maybe V) here) (erased (List $ NMKid V) kids) (erased (NameMap V) submap)
                   (erased (KidIs V c submap kids) k) (erased (NAbsent V rest submap) p) -> (NAbsent V (SCons c rest) $ NMNode V here kids)))
  ((NLookup : (Type V) ((String) name) ((NameMap V) m) -> Type)
    enum
    (many NHit : (erased Type V) (erased (String) name) (erased (NameMap V) m) (many V v) (erased (NMapsTo V name v m) p) -> (NLookup V name m))
    (many NMiss : (erased Type V) (erased (String) name) (erased (NameMap V) m) (erased (NAbsent V name m) p) -> (NLookup V name m))))

(def-fns _ $ (many nm-empty : (erased Type V) -> (many (NameMap V) m))
  (NMNode _ (None _) $ Nil _))

(def-fns _ $ (many nm-kid : (erased Type V) (subterm many (List $ NMKid V) kids) (many (Char) c) -> (many (KidLookup V c kids) r))
  (let-match many kids (Cons _ k rest) ((Nil _) (KMiss _ _ _ $ NKNil _ c)))
  (let-match many k (MkKid _ c1 sub3))
  (match many (char-cmp c c1) _
    ((CEq _ _ _) (KHit _ _ _ sub3 $ KHere _ c sub3 rest))
    ((CLt _ _ _ _ lt)
      (let ((many r)) (tail $ nm-kid _ rest c))
      (let ((erased _) (erased cp)) $ match erased r (((KidLookup V c kids) r2) ((Coercible (Shared) (KidLookup V c rest) r (Shared) (KidLookup V c kids) r2) cp))
        ((KHit _ _ _ sub2 p) (values (KHit _ _ _ sub2 $ KThere _ c sub2 k rest p) (coercible-ctor (Shared) KHit V V c c rest kids (coercible-refl (Shared) sub2) p $ KThere _ c sub2 k rest p)))
        ((KMiss _ _ _ p) (values (KMiss _ _ _ $ NKLt _ c c1 sub3 rest lt p) (coercible-ctor (Shared) KMiss V V c c rest kids p $ NKLt _ c c1 sub3 rest lt p))))
      (coerce r cp))
    ((CGt _ _ _ _ gt)
      (let ((many r)) (tail $ nm-kid _ rest c))
      (let ((erased _) (erased cp)) $ match erased r (((KidLookup V c kids) r2) ((Coercible (Shared) (KidLookup V c rest) r (Shared) (KidLookup V c kids) r2) cp))
        ((KHit _ _ _ sub2 p) (values (KHit _ _ _ sub2 $ KThere _ c sub2 k rest p) (coercible-ctor (Shared) KHit V V c c rest kids (coercible-refl (Shared) sub2) p $ KThere _ c sub2 k rest p)))
        ((KMiss _ _ _ p) (values (KMiss _ _ _ $ NKGt _ c c1 sub3 rest gt p) (coercible-ctor (Shared) KMiss V V c c rest kids p $ NKGt _ c c1 sub3 rest gt p))))
      (coerce r cp))))

(def-fns _ $ (many nm-get : (erased Type V) (subterm many (String) name) (many (NameMap V) m) -> (many (NLookup V name m) r))
  (let-match many m (NMNode _ here kids))
  (let-match many name (SCons c rest)
    ((SNil) (match many here _ ((None _) (NMiss _ _ _ $ NAHere _ kids)) ((Some _ v) (NHit _ _ _ v $ NMHere _ v kids)))))
  (let-match many (nm-kid _ kids c) (KHit _ _ _ submap k) ((KMiss _ _ _ n) (NMiss _ _ _ $ NANoKid _ c rest here kids n)))
  (let ((many r)) (tail $ nm-get _ rest submap))
  (let ((erased _) (erased cp)) $ match erased r (((NLookup V name m) r2) ((Coercible (Shared) (NLookup V rest submap) r (Shared) (NLookup V name m) r2) cp))
    ((NHit _ _ _ v p) (values (NHit _ _ _ v $ NMStep _ c rest v here kids submap k p) (coercible-ctor (Shared) NHit V V rest name submap m (coercible-refl (Shared) v) p $ NMStep _ c rest v here kids submap k p)))
    ((NMiss _ _ _ p) (values (NMiss _ _ _ $ NAStep _ c rest here kids submap k p) (coercible-ctor (Shared) NMiss V V rest name submap m p $ NAStep _ c rest here kids submap k p))))
  (coerce r cp))

(def-fns _ $ (many nm-replace-kid : (erased Type V) (subterm many (List $ NMKid V) kids) (many (Char) c) (many (NameMap V) submap) -> (many (List $ NMKid V) r))
  (let-match many kids (Cons _ k rest) ((Nil _) (Cons _ (MkKid _ c submap) $ Nil _)))
  (let-match many k (MkKid _ c1 _))
  (match many (char-cmp c c1) _
    ((CEq _ _ _) (Cons _ (MkKid _ c submap) rest))
    (else (Cons _ k $ notail $ nm-replace-kid _ rest c submap))))

(def-fns _ $ (many nm-set : (erased Type V) (subterm many (String) name) (many V v) (many (NameMap V) m) -> (many (NameMap V) r))
  (let-match many m (NMNode _ here kids))
  (let-match many name (SCons c rest) ((SNil) (NMNode _ (Some _ v) kids)))
  (let ((many (NameMap V) submap)) (match many (nm-kid _ kids c) _
                    ((KMiss _ _ _ _) (nm-empty _))
                    ((KHit _ _ _ s _) s)))
  (NMNode _ here $ nm-replace-kid _ kids c $ notail $ nm-set _ rest v submap))

; ---- Lists

(def-adts
  ((Concat : (Type A) ((List A) xs) ((List A) ys) ((List A) zs) -> Type)
    enum
    (many CatNil : (erased Type A) (erased (List A) ys) -> (Concat A (Nil A) ys ys))
    (many CatCons : (erased Type A) (erased A x) (erased (List A) rest) (erased (List A) ys) (erased (List A) zs) (erased (Concat A rest ys zs) p)
       -> (Concat A (Cons A x rest) ys (Cons A x zs))))
  ((OutOfRange : (Type A) ((List A) xs) ((Nat) i) -> Type)
    enum
    (many OONil : (erased Type A) (erased (Nat) i) -> (OutOfRange A (Nil A) i))
    (many OOCons : (erased Type A) (erased A y) (erased (List A) rest) (erased (Nat) i) (erased (OutOfRange A rest i) p) -> (OutOfRange A (Cons A y rest) (Succ i))))
  ((NthLookup : (Type A) ((List A) xs) ((Nat) i) -> Type)
    enum
    (many NthHit : (erased Type A) (erased (List A) xs) (erased (Nat) i) (many A x) (erased (Nth A xs i x) p) -> (NthLookup A xs i))
    (many NthMiss : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased (OutOfRange A xs i) p) -> (NthLookup A xs i))))

(def-fns _ $ (many length : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n) (erased (Length A xs n) p))
  (let-match many xs (Cons _ x rest) ((Nil _) (values (Zero) (LengthNil _))))
  (let ((many n) (erased p)) (notail $ length _ rest))
  (values (Succ n) (LengthCons _ x rest n p)))

(def-fns _ $ (many list-replicate : (erased Type A) (subterm many (Nat) n) (many A x) -> (many (List A) r))
  (match many n _
    ((Zero) (Nil _))
    ((Succ k) (Cons _ x $ notail $ list-replicate _ k x))))

(def-fns _ $ (many list-drop : (erased Type A) (subterm many (Nat) n) (many (List A) xs) -> (many (List A) r))
  (let-match many n (Succ k)
    ((Zero) xs))
  (match many xs _ ((Nil _) (Nil _)) ((Cons _ _ rest) (tail $ list-drop _ k rest))))

(def-fns _ $ (many list-length at length : (erased Type A) (many (List A) xs) -> (many (Nat) n))
  (let ((many n) (erased _)) (delegate (length _ xs)))
  n)

; Two lists of one length, entry by entry.
(def-adts
  ((Lockstep : (Type A) (Type B) ((List A) xs) ((List B) ys) -> Type)
    enum
    (many LsNil : (erased Type A) (erased Type B) -> (Lockstep A B (Nil A) (Nil B)))
    (many LsCons : (erased Type A) (erased Type B) (erased A x) (erased B y) (erased (List A) xs) (erased (List B) ys) (erased (Lockstep A B xs ys) p)
       -> (Lockstep A B (Cons A x xs) (Cons B y ys)))))

(def-fns _ $ (erased lockstep-trans : (erased Type A) (erased Type B) (erased Type C) (erased (List A) xs) (erased (List B) ys) (erased (List C) zs)
    (subterm erased (Lockstep A B xs ys) p) (erased (Lockstep B C ys zs) q) -> (erased (Lockstep A C xs zs) r))
  (match erased p _
    ((LsNil _ _)
      (let-match erased q (LsNil _ _))
      (LsNil _ _))
    ((LsCons _ _ x _ xs2 _ p2)
      (let-match erased q (LsCons _ _ _ z _ zs2 q2))
      (LsCons _ _ x z xs2 zs2 $ lockstep-trans _ _ _ _ _ _ p2 q2))))

(def-fns _ $ (erased lockstep-sym : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) (subterm erased (Lockstep A B xs ys) p) -> (erased (Lockstep B A ys xs) q))
  (match erased p _
    ((LsNil _ _) (LsNil _ _))
    ((LsCons _ _ x y xs2 ys2 p2) (LsCons _ _ y x ys2 xs2 $ lockstep-sym _ _ _ _ p2))))

(def-adts
  ((LockstepDec : (Type A) (Type B) ((List A) xs) ((List B) ys) -> Type)
    enum
    (many LdYes : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) (erased (Lockstep A B xs ys) p) -> (LockstepDec A B xs ys))
    (many LdNo : (erased Type A) (erased Type B) (erased (List A) xs) (erased (List B) ys) -> (LockstepDec A B xs ys))))

(def-fns _ $ (many lockstep-dec : (erased Type A) (erased Type B) (subterm many (List A) xs) (many (List B) ys) -> (many (LockstepDec A B xs ys) r))
  (let-match many xs (Cons _ x xrest)
    ((Nil _) (match many ys _ ((Nil _) (LdYes _ _ _ _ $ LsNil _ _)) ((Cons _ _ _) (LdNo _ _ _ _)))))
  (let-match many ys (Cons _ y yrest) ((Nil _) (LdNo _ _ _ _)))
  (let ((many r)) (tail $ lockstep-dec _ _ xrest yrest))
  (let ((erased _) (erased cp)) $ match erased r (((LockstepDec A B xs ys) r2) ((Coercible (Shared) (LockstepDec A B xrest yrest) r (Shared) (LockstepDec A B xs ys) r2) cp))
    ((LdYes _ _ _ _ p) (values (LdYes _ _ _ _ $ LsCons _ _ x y xrest yrest p) (coercible-ctor (Shared) LdYes A A B B xrest xs yrest ys p $ LsCons _ _ x y xrest yrest p)))
    ((LdNo _ _ _ _) (values (LdNo _ _ _ _) (coercible-ctor (Shared) LdNo A A B B xrest xs yrest ys))))
  (coerce r cp))

(def-fns _ $ (many list-fit : (erased Type A) (erased Type B) (subterm many (List A) xs) (many (List B) ys) (many B filler) -> (many (List B) r) (erased (Lockstep A B xs r) p))
  (let-match many xs (Cons _ x rest) ((Nil _) (values (Nil _) (LsNil _ _))))
  (let ((many y) (many yrest)) $ match many ys ((B _) ((List B) ys0)) ((Nil _) (values filler $ Nil _)) ((Cons _ y yrest) (values y yrest)))
  (let ((many r) (erased p)) $ notail $ list-fit _ _ rest yrest filler)
  (values (Cons _ y r) (LsCons _ _ x y rest r p)))

(def-fns _ $ (many list-rev-onto : (erased Type A) (subterm many (List A) xs) (many (List A) acc) -> (many (List A) r))
  (match many xs _
    ((Nil _) acc)
    ((Cons _ x rest) (tail $ list-rev-onto _ rest $ Cons _ x acc))))

(def-fns _ $ (many list-rev : (erased Type A) (many (List A) xs) -> (many (List A) r))
  (list-rev-onto _ xs $ Nil _))

(def-fns _ $ (many list-append : (erased Type A) (subterm many (List A) xs) (many (List A) ys) -> (many (List A) zs) (erased (Concat A xs ys zs) p))
  (let-match many xs (Cons _ x rest) ((Nil _) (values ys (CatNil _ ys))))
  (let ((many zs) (erased p)) (notail $ list-append _ rest ys))
  (values (Cons _ x zs) (CatCons _ x rest ys zs p)))

(def-fns _ $ (many list-nth : (erased Type A) (subterm many (List A) xs) (many (Nat) i) -> (many (NthLookup A xs i) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (NthMiss _ _ _ $ OONil _ i)))
  (let-match many i (Succ k) ((Zero) (NthHit _ _ _ x $ NthHere _ x rest)))
  (let ((many r)) (tail $ list-nth _ rest k))
  (let ((erased _) (erased cp)) $ match erased r (((NthLookup A xs i) r2) ((Coercible (Shared) (NthLookup A rest k) r (Shared) (NthLookup A xs i) r2) cp))
    ((NthHit _ _ _ y p) (values (NthHit _ _ _ y $ NthThere _ x rest k y p) (coercible-ctor (Shared) NthHit A A rest xs k i (coercible-refl (Shared) y) p $ NthThere _ x rest k y p)))
    ((NthMiss _ _ _ p) (values (NthMiss _ _ _ $ OOCons _ x rest k p) (coercible-ctor (Shared) NthMiss A A rest xs k i p $ OOCons _ x rest k p))))
  (coerce r cp))

(def-fns _ $ (many list-nth-or : (erased Type A) (many (List A) xs) (many (Nat) i) (many A dflt) -> (many A r))
  (match many (list-nth _ xs i) _ ((NthHit _ _ _ x _) x) ((NthMiss _ _ _ _) dflt)))

(def-fns _ $ (many list1 : (erased Type A) (many A x) -> (many (List A) r))
  (Cons _ x $ Nil _))

(def-fns _ $ (many list-is-empty : (erased Type A) (many (List A) xs) -> (many (Bool) r))
  (match many xs _ ((Nil _) (BTrue)) ((Cons _ _ _) (BFalse))))

(def-fns _ $ (many is-some : (erased Type A) (many (Maybe A) m) -> (many (Bool) r))
  (match many m _ ((Some _ _) (BTrue)) ((None _) (BFalse))))

(def-fns _ $ (many maybe-or : (erased Type A) (many (Maybe A) m) (many A d) -> (many A r))
  (match many m _ ((Some _ x) x) ((None _) d)))

(def-fns _ $ (many list-mem-str : (subterm many (List $ String) xs) (many (String) x) -> (many (Bool) r))
  (let-match many xs (Cons _ y rest)
    ((Nil _) (BFalse)))
  (match many (str-eq x y) _ ((BTrue) (BTrue)) ((BFalse) (tail $ list-mem-str rest x))))

(def-fns _ $ (many index-of-bin : (subterm many (List $ Nat) xs) (many (Nat) x) (many (Nat) i) -> (many (Maybe $ Nat) r))
  (let-match many xs (Cons _ y rest) ((Nil _) (None _)))
  (match many (nat-eq x y) _
    ((BTrue) (Some _ i))
    ((BFalse) (tail $ index-of-bin rest x $ Succ i))))

(def-fns _ $ (many list-mem-bin : (subterm many (List $ Nat) xs) (many (Nat) x) -> (many (Bool) r))
  (let-match many xs (Cons _ y rest) ((Nil _) (BFalse)))
  (match many (nat-eq x y) _ ((BTrue) (BTrue)) ((BFalse) (tail $ list-mem-bin rest x))))

(def-fns _ $ (many join-strs : (subterm many (List $ String) xs) (many (String) sep) -> (many (String) r))
  (let-match many xs (Cons _ x rest)
    ((Nil _) ""))
  (match many rest _ ((Nil _) x) ((Cons _ _ _) (str-cat3 x sep $ notail $ join-strs rest sep))))

(def-fns _ $ (many nat-min : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (match many (nat-lt a b) _ ((BTrue) a) ((BFalse) b)))

(def-fns _ $ (many char-lower : (many (Char) c) -> (many (Char) r))
  (match many (char-between c 65 90) _ ((BTrue) (char-of-code $ nat-add (char-code c) 32)) ((BFalse) c)))

(def-fns _ $ (many char-eq-nocase : (many (Char) a) (many (Char) b) -> (many (Bool) r))
  (char-eq (char-lower a) (char-lower b)))

(def-fns _ $ (many distance-first-row : (subterm many (String) bs) (many (Nat) j) -> (many (List $ Nat) r))
  (Cons _ j $ match many bs (((List $ Nat) _)) ((SNil) (Nil _)) ((SCons _ rest) (notail $ distance-first-row rest $ Succ j))))

(def-fns _ $ (many distance-swap : (many (Char) c) (many (Maybe $ Char) cp) (many (Char) bc) (many (Maybe $ Char) bp) (many (List $ Nat) up2) -> (many (Maybe $ Nat) r))
  (let-match many cp (Some _ ap) ((None _) (None _)))
  (let-match many bp (Some _ bq) ((None _) (None _)))
  (let-match many up2 (Cons _ q _) ((Nil _) (None _)))
  (match many (and (char-eq-nocase c bq) $ char-eq-nocase ap bc) _ ((BTrue) (Some _ q)) ((BFalse) (None _))))

(def-fns _ $ (many distance-row : (many (Char) c) (many (Maybe $ Char) cp) (subterm many (String) bs) (many (Maybe $ Char) bp)
    (many (List $ Nat) up) (many (List $ Nat) up2) (many (Nat) left) -> (many (List $ Nat) r))
  (let-match many bs (SCons bc rest) ((SNil) (Nil _)))
  (let-match many up (Cons _ diag up-rest) ((Nil _) (Nil _)))
  (let-match many up-rest (Cons _ above _) ((Nil _) (Nil _)))
  (let ((many best)) (nat-min (Succ $ nat-min above left) $ match many (char-eq-nocase c bc) (((Nat) _)) ((BTrue) diag) ((BFalse) (Succ diag))))
  (let ((many here)) (match many (distance-swap c cp bc bp up2) (((Nat) _)) ((Some _ q) (nat-min best $ Succ q)) ((None _) best)))
  (let ((many up2-next)) (match many bp (((List $ Nat) _)) ((None _) up2) ((Some _ _) (match many up2 (((List $ Nat) _)) ((Nil _) up2) ((Cons _ _ r2) r2)))))
  (Cons _ here $ notail $ distance-row c cp rest (Some _ bc) up-rest up2-next here))

(def-fns _ $ (many distance-rows : (subterm many (String) xs) (many (Maybe $ Char) cp) (many (String) b) (many (Nat) i) (many (List $ Nat) up) (many (List $ Nat) up2) -> (many (List $ Nat) r))
  (let-match many xs (SCons c rest) ((SNil) up))
  (let ((many row)) (Cons _ (Succ i) $ distance-row c cp b (None _) up up2 (Succ i)))
  (tail $ distance-rows rest (Some _ c) b (Succ i) row up))

(def-fns _ $ (many distance : (many (String) a) (many (String) b) -> (many (Nat) d))
  (let ((many first)) (distance-first-row b 0))
  (let-match many (list-rev _ $ distance-rows a (None _) b 0 first first) (Cons _ d _) ((Nil _) 0))
  d)

; ---- Rope: output built as a tree of chunks (the prelude's), flattened once

(def-fns _ $ (many rcat : (many (Rope) a) (many (Rope) b) -> (many (Rope) r))
  (RCat a b))

(def-fns _ $ (many rcat3 : (many (Rope) a) (many (Rope) b) (many (Rope) c) -> (many (Rope) r))
  (RCat a $ RCat b c))

(def-fns _ $ (many rcat4 : (many (Rope) a) (many (Rope) b) (many (Rope) c) (many (Rope) d) -> (many (Rope) r))
  (RCat a $ RCat b $ RCat c d))

(def-fns _ $ (many rcat5 : (many (Rope) a) (many (Rope) b) (many (Rope) c) (many (Rope) d) (many (Rope) e) -> (many (Rope) r))
  (RCat a $ RCat b $ RCat c $ RCat d e))

(def-fns _ $ (many rwrap : (many (String) open) (many (Rope) body) (many (String) close) -> (many (Rope) r))
  (rcat3 (RStr open) body $ RStr close))

; Ropes joined by a separator.
(def-fns _ $ (many rjoin : (subterm many (List $ Rope) rs) (many (String) sep) -> (many (Rope) r))
  (let-match many rs (Cons _ r rest) ((Nil _) (REmpty)))
  (match many rest _
    ((Nil _) r)
    ((Cons _ _ _) (RCat r $ RCat (RStr sep) $ notail $ rjoin rest sep))))

(let ((many sixteen-dec)) (lt-dec (Zero) 16))
(comptime-match many sixteen-dec (Yes sda sdb sixteen-positive))

(def-fns _ $ (many hex-rope : (many (Nat) n) -> (many (Rope) r))
  (RChar $ char-of-code $ match many (nat-lt n 10) (((Nat) _)) ((BTrue) (nat-add 48 n)) ((BFalse) (nat-add 87 n))))

(def-fns _ $ (many hex-byte-rope : (many (Nat) c) -> (many (Rope) r))
  (let ((many hi) (many lo) (erased _) (erased _) (erased _) (erased _)) (divmod c 16 sixteen-positive))
  (rcat (hex-rope hi) $ hex-rope lo))

(def-fns _ $ (many hex-pair : (many (Char) a) (many (Char) b) -> (many (Maybe $ Char) r))
  (match many (and (is-hex a) (is-hex b)) _
    ((BTrue) (Some _ $ char-of-code $ nat-add (nat-mul (hex-digit a) 16) $ hex-digit b))
    ((BFalse) (None _))))

(def-fns _ $ (many escape-char : (many (Char) c) -> (many (Rope) r))
  (let ((many k)) $ char-code c)
  (let-match many (nat-eq k 34) (BFalse) ((BTrue) (RStr "\\\"")))
  (let-match many (nat-eq k 92) (BFalse) ((BTrue) (RStr "\\\\")))
  (let-match many (nat-eq k 10) (BFalse) ((BTrue) (RStr "\\n")))
  (let-match many (nat-eq k 9) (BFalse) ((BTrue) (RStr "\\t")))
  (match many (and (nat-lt 31 k) (nat-lt k 127)) _
    ((BTrue) (RChar c))
    ((BFalse) (rcat (RStr "\\x") $ hex-byte-rope k))))

(def-fns _ $ (many word-code : (many (Nat) n) -> (many (Bool) r))
  (and (and (nat-lt 32 n) (nat-lt n 127)) $ not $ or (nat-eq n 40) $ or (nat-eq n 41) $ nat-eq n 59))

; Bare where the reader's word syntax admits the character, hexadecimal otherwise.
(def-fns _ $ (many lit-char-rope : (many (Nat) c) -> (many (Rope) r))
  (let-match many (nat-eq c 32) (BFalse) ((BTrue) (RStr "#\\space")))
  (let-match many (nat-eq c 10) (BFalse) ((BTrue) (RStr "#\\newline")))
  (let-match many (nat-eq c 9) (BFalse) ((BTrue) (RStr "#\\tab")))
  (let-match many (word-code c) (BFalse) ((BTrue) (rcat (RStr "#\\") $ RChar $ char-of-code c)))
  (rcat (RStr "#\\x") $ hex-byte-rope c))

(def-fns _ $ (many str-escape : (subterm many (String) s) -> (many (Rope) r))
  (match many s _
    ((SNil) (REmpty))
    ((SCons c rest) (rcat (escape-char c) $ notail $ str-escape rest))))

(def-fns _ $ (many lit-string-rope : (many (String) s) -> (many (Rope) r))
  (rwrap "\"" (str-escape s) "\""))

(def-fns _ $ (many all-word-chars : (subterm many (String) s) -> (many (Bool) r))
  (match many s _
    ((SNil) (BTrue))
    ((SCons c rest) (and (word-code $ char-code c) $ tail $ all-word-chars rest))))

(def-fns _ $ (many is-plain-name : (many (String) s) -> (many (Bool) r))
  (let-match many s (SCons c _) ((SNil) (BFalse)))
  (and (all-word-chars s) $ and (not $ is-literal-name s) $ and (not $ str-eq s "_") $ and (not $ str-eq s "$")
    $ and (not $ char-is c 34) $ and (not $ is-reserved-name s) $ not $ str-starts "#\"" s))

(def-fns _ $ (many spell-text : (many (String) s) -> (many (String) r))
  (match many (is-plain-name s) _ ((BTrue) s) ((BFalse) (rope-str $ rcat (RStr "#") $ lit-string-rope s))))

(def-adts $ (Multiplicity : -> Type)
  enum
  (many Erased : -> (Multiplicity))
  (many Many : -> (Multiplicity))
  (many Once : -> (Multiplicity)))

(def-adts $ (Reading : -> Type)
  enum
  (many MintedIs : -> (Reading))
  (many MintedType : -> (Reading)))

(def-fns _ $ (many reading-eq : (many (Reading) a) (many (Reading) b) -> (many (Bool) r))
  (match many a _
    ((MintedIs) (match many b _ ((MintedIs) (BTrue)) ((MintedType) (BFalse))))
    ((MintedType) (match many b _ ((MintedIs) (BFalse)) ((MintedType) (BTrue))))))

(def-adts $ (Name : -> Type)
  enum
  (many NSrc : (many (String) s) -> (Name))
  (many NGen : (many (Nat) n) (many (String) s) -> (Name))
  (many NHandle : (many (Nat) id) (many (Reading) rd) (many (Multiplicity) m) (many (String) shown) -> (Name)))

(def-fns _ $ (many spell-name : (many (Name) n) -> (many (String) r))
  (match many n _
    ((NSrc s) (spell-text s))
    ((NGen k s) (str-cat3 "__g" (nat-str k) $ str-cat "_" $ spell-text s))
    ((NHandle _ _ _ s) s)))

(def-fns _ $ (many name-text : (many (Name) n) -> (many (String) r))
  (match many n _ ((NSrc s) s) (else (spell-name n))))

(def-fns _ $ (many name-eq : (many (Name) a) (many (Name) b) -> (many (Bool) r))
  (match many a _
    ((NSrc s) (match many b _ ((NSrc t) (str-eq s t)) (else (BFalse))))
    ((NGen m _) (match many b _ ((NGen n _) (nat-eq m n)) (else (BFalse))))
    ((NHandle m ra _ _) (match many b _ ((NHandle n rb _ _) (and (nat-eq m n) $ reading-eq ra rb)) (else (BFalse))))))

(def-fns _ $ (many rlist : (subterm many (List $ Rope) rs) -> (many (Rope) r))
  (match many rs _
    ((Nil _) (REmpty))
    ((Cons _ r rest) (RCat r $ notail $ rlist rest))))

; Every name a NameMap holds, with its value.
(def-fns _
  ((many nm-entries : (erased Type V) (subterm many (NameMap V) m) (many (Rope) path) (many (List $ Pair (String) V) acc) -> (many (List $ Pair (String) V) r))
    (let-match many m (NMNode _ here kids))
    (let ((many acc2)) $ match many here (((List $ Pair (String) V) _)) ((None _) acc) ((Some _ v) (Cons _ (MkPair _ _ (rope-str path) v) acc)))
    (tail $ nm-kids-entries _ kids path acc2))
  ((many nm-kids-entries : (erased Type V) (subterm many (List $ NMKid V) kids) (many (Rope) path) (many (List $ Pair (String) V) acc) -> (many (List $ Pair (String) V) r))
    (let-match many kids (Cons _ k rest) ((Nil _) acc))
    (match many k _
      ((MkKid _ c submap) (tail $ nm-kids-entries _ rest path $ notail $ nm-entries _ submap (rcat path $ RChar c) acc)))))

(def-adts $ (NameIndex : (Type V) -> Type)
  enum
  (many MkNameIndex : (erased Type V) (many (NameMap V) src) (many (List $ Pair (Name) V) gen) -> (NameIndex V)))

(def-fns _ $ (many name-index-empty : (erased Type V) -> (many (NameIndex V) m))
  (MkNameIndex _ (nm-empty _) (Nil _)))

(def-fns _ $ (many gen-get : (erased Type V) (many (Name) n) (subterm many (List $ Pair (Name) V) gs) -> (many (Maybe V) r))
  (let-match many gs (Cons _ g rest) ((Nil _) (None _)))
  (let-match many g (MkPair _ _ k v))
  (match many (name-eq k n) _ ((BTrue) (Some _ v)) ((BFalse) (tail $ gen-get _ n rest))))

(def-fns _ $ (many gen-id : (many (Name) n) -> (many (Nat) k))
  (match many n _ ((NGen k _) k) (else 0)))

(def-fns _ $ (many gen-set : (erased Type V) (many (Name) n) (many V v) (subterm many (List $ Pair (Name) V) gs) -> (many (List $ Pair (Name) V) r))
  (let-match many gs (Cons _ g rest) ((Nil _) (Cons _ (MkPair _ _ n v) $ Nil _)))
  (let-match many g (MkPair _ _ k _))
  (match many (nat-lt (gen-id k) $ gen-id n) _
    ((BTrue) (Cons _ g $ notail $ gen-set _ n v rest))
    ((BFalse) (Cons _ (MkPair _ _ n v) $ match many (name-eq k n) (((List $ Pair (Name) V) _)) ((BTrue) rest) ((BFalse) gs)))))

(def-fns _ $ (many name-index-get : (erased Type V) (many (Name) n) (many (NameIndex V) m) -> (many (Maybe V) r))
  (let-match many m (MkNameIndex _ src gen))
  (let-match many n (NSrc s) (else (gen-get _ n gen)))
  (match many (nm-get _ s src) _ ((NHit _ _ _ x _) (Some _ x)) ((NMiss _ _ _ _) (None _))))

(def-fns _ $ (many name-index-set : (erased Type V) (many (Name) n) (many V v) (many (NameIndex V) m) -> (many (NameIndex V) r))
  (let-match many m (MkNameIndex _ src gen))
  (match many n _
    ((NSrc s) (MkNameIndex _ (nm-set _ s v src) gen))
    (else (MkNameIndex _ src $ gen-set _ n v gen))))

(def-fns _ $ (many src-pairs : (erased Type V) (subterm many (List $ Pair (String) V) ps) (many (List $ Pair (Name) V) acc) -> (many (List $ Pair (Name) V) r))
  (let-match many ps (Cons _ p rest) ((Nil _) acc))
  (let-match many p (MkPair _ _ s v))
  (Cons _ (MkPair _ _ (NSrc s) v) $ notail $ src-pairs _ rest acc))

(def-fns _ $ (many name-index-entries : (erased Type V) (many (NameIndex V) m) -> (many (List $ Pair (Name) V) r))
  (let-match many m (MkNameIndex _ src gen))
  (src-pairs _ (nm-entries _ src (REmpty) $ Nil _) $ list-rev _ gen))

; ---- lemmas over the prelude's Lt and Double, shared with heap.sl and core.sl's fact table

(def-fns _ $ (erased absurd lt-zero : (erased (Nat) a) (erased (Lt a (Zero)) p) -> (erased (False) f))
  p)

(def-fns _ $ (erased le-trans : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Lt a (Succ b)) p) (erased (Lt b (Succ c)) q) -> (erased (Lt a (Succ c)) r))
  (lt-le-trans a (Succ b) (Succ c) p (LtS b (Succ c) q)))

(def-fns _ $ (erased double-lt-inv : (erased (Nat) m) (erased (Nat) d) (erased (Nat) l) (erased (Nat) s) (subterm erased (Double m d) p) (erased (Double l s) q) (erased (Lt d s) lt) -> (erased (Lt m l) r))
  (match erased p _
    ((D0)
      (match erased q _
        (absurd (D0) (lt-zero d lt))
        ((DS l1 _ _) (LtZ l1))))
    ((DS m1 d1 p1)
      (let-match erased q (DS l1 s1 q1) (absurd (D0) (lt-zero d lt)))
      (let-match erased lt (LtS _ _ lt1))
      (let-match erased lt1 (LtS _ _ lt2))
      (LtS m1 l1 (double-lt-inv m1 d1 l1 s1 p1 q1 lt2)))))


; ---- a trie's size against a bound on its keys, the measure a walk over one recurses on

(def-fns _ $ (erased lt-drop : (erased (Nat) d) (erased (Nat) s) (erased (Lt (Succ d) s) p) -> (erased (Lt d s) q))
  (let-match erased p (LtS _ y q))
  (lt-weaken d y q))

(def-fns _ $ (erased double-le-inv : (erased (Nat) m) (erased (Nat) d) (erased (Nat) r) (erased (Nat) s) (erased (Double m d) p) (erased (Double r s) q) (erased (Lt d (Succ s)) lt) -> (erased (Lt m (Succ r)) res))
  (double-lt-inv m d (Succ r) (Succ (Succ s)) p (DS r s q) (lt-weaken d (Succ s) lt)))

(def-adts $ (Braun : ((Nat) l) ((Nat) r) -> Type)
  enum
  (many BrEq : (erased (Nat) n) -> (Braun n n))
  (many BrOne : (erased (Nat) n) -> (Braun (Succ n) n)))

(def-fns _ $ (erased half-lt-one : (erased (Nat) m) (erased (Nat) d) (erased (Nat) l) (erased (Nat) r) (erased (Nat) s) (erased (Double m d) dd) (erased (Add l r s) sum) (erased (Braun l r) bal) (erased (Lt d s) lt) -> (erased (Lt m l) res))
  (let-match erased bal (BrOne n) ((BrEq n) (double-lt-inv m d n s dd (add-diag-double n s sum) lt)))
  (let-match erased sum (AddSucc _ _ c1 q))
  (double-le-inv m d n c1 dd (add-diag-double n c1 q) lt))

(def-fns _ $ (erased half-lt-two : (erased (Nat) m) (erased (Nat) d) (erased (Nat) l) (erased (Nat) r) (erased (Nat) s) (erased (Double m d) dd) (erased (Add l r s) sum) (erased (Braun l r) bal) (erased (Lt (Succ d) s) lt) -> (erased (Lt m r) res))
  (let-match erased bal (BrOne n) ((BrEq n) (double-lt-inv m d n s dd (add-diag-double n s sum) (lt-drop d s lt))))
  (let-match erased sum (AddSucc _ _ c1 q))
  (let-match erased lt (LtS _ _ lt1))
  (double-lt-inv m d n c1 dd (add-diag-double n c1 q) lt1))

; [size] how many entries a trie holds, [max] a bound every key in it is below. The node case splits
; max the way the trie splits keys: key 0 sits here, 2m+1 in one, 2m+2 in two, so a node bounded by
; Succ m1 has children bounded by l and r with l + r = m1 and l either r or r + 1.
(def-adts $ (Bounded : (Type V) ((IdMap V) m) ((Nat) size) ((Nat) max) -> Type)
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

(def-fns _ $ (erased add-le-right : (erased (Nat) x) (erased (Nat) y) (erased (Nat) z)
    (subterm erased (Add x y z) p) -> (erased (Lt y (Succ z)) r))
  (match erased p _
    ((AddZero _) (lt-succ y))
    ((AddSucc a b c q) (lt-weaken y (Succ c) (add-le-right a b c q)))))

; sums are monotone: a <= x and b <= y give a + b <= x + y
(def-fns _ $ (erased add-mono : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (subterm erased (Add a b c) p)
    (erased (Nat) x) (erased (Nat) y) (erased (Nat) z) (erased (Add x y z) q)
    (erased (Lt a (Succ x)) la) (erased (Lt b (Succ y)) lb) -> (erased (Lt c (Succ z)) r))
  (let-match erased p (AddSucc a0 b0 c0 p0) ((AddZero _) (le-trans b y z lb (add-le-right x y z q))))
  (match erased q _
    (absurd (AddZero _)
      (let-match erased la (LtS _ _ la0)) (lt-zero a0 la0))
    ((AddSucc x0 y0 z0 q0)
      (let-match erased la (LtS _ _ la0))
      (LtS c0 (Succ z0) (add-mono a0 b0 c0 p0 x0 y0 z0 q0 la0 lb)))))

; the point: a trie bounded by max holds at most max entries
(def-fns _ $ (erased bounded-le : (erased Type V) (erased (IdMap V) m) (erased (Nat) size) (erased (Nat) max)
    (subterm erased (Bounded V m size max) b) -> (erased (Lt size (Succ max)) r))
  (match erased b _
    ((BdEmpty _ mx) (LtZ mx))
    ((BdNone _ one two l r m1 sum _ so bo st bt sot ssum)
      (lt-weaken sot (Succ m1) (add-mono so st sot ssum l r m1 sum (bounded-le _ one so l bo) (bounded-le _ two st r bt))))
    ((BdSome _ _ one two l r m1 sum _ so bo st bt sot ssum)
      (LtS sot (Succ m1) (add-mono so st sot ssum l r m1 sum (bounded-le _ one so l bo) (bounded-le _ two st r bt))))))

; ---- reading an Absent witness at the child the key's halving leads to

(def-fns _ $ (erased absurd absent-not-some : (erased Type V) (erased V v) (erased (IdMap V) one) (erased (IdMap V) two)
    (erased (Absent V (Zero) (MNode V (Some V v) one two)) ab) -> (erased (False) f))
  ab)

(def-fns _ $ (erased absent-one : (erased Type V) (erased (Nat) k1) (erased (Nat) d) (erased (Double k1 d) dd)
    (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two)
    (erased (Absent V (Succ d) (MNode V here one two)) ab) -> (erased (Absent V k1 one) r))
  (let-match erased ab (AB1 _ k2 _ dd2 _ _ _ sub2)
    (absurd (AB2 _ k2 d2 dd2 _ _ _ _) (double-parity k1 k2 d2 dd dd2)))
  (match erased (double-inj k1 k2 d dd dd2) _ ((Refl _ _) sub2)))

(def-fns _ $ (erased absent-two : (erased Type V) (erased (Nat) k1) (erased (Nat) d) (erased (Double k1 d) dd)
    (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two)
    (erased (Absent V (Succ (Succ d)) (MNode V here one two)) ab) -> (erased (Absent V k1 two) r))
  (let-match erased ab (AB2 _ k2 _ dd2 _ _ _ sub2)
    (absurd (AB1 _ k2 _ dd2 _ _ _ _) (double-parity k2 k1 d dd2 dd)))
  (match erased (double-inj k1 k2 d dd dd2) _ ((Refl _ _) sub2)))

; ---- splitting a bound the way the trie splits keys
(def-fns _ $ (erased split-bound : (subterm erased (Nat) m1) ->
    (erased (Nat) l) (erased (Nat) r) (erased (Add l r m1) sum) (erased (Braun l r) bal))
  (let-match erased m1 (Succ m0) ((Zero) (values (Zero) (Zero) (AddZero (Zero)) (BrEq (Zero)))))
  (let ((erased l0) (erased r0) (erased sum0) (erased bal0)) (split-bound m0))
  (values (Succ r0) l0 (AddSucc r0 l0 m0 (add-comm l0 r0 m0 sum0))
    (match erased bal0 (((Braun (Succ r0) l0) _))
      ((BrEq n) (BrOne n))
      ((BrOne n) (BrEq (Succ n))))))

(def-fns _ $ (erased lt-succ-inv : (erased (Nat) a) (erased (Nat) b) (erased (Lt (Succ a) (Succ b)) p) ->
    (erased (Lt a b) q))
  (let-match erased p (LtS _ _ q))
  q)

; a bound a key sits under is a successor, and splits the way the trie does
(def-fns _ $ (erased bound-split : (erased (Nat) max) (erased (Nat) k) (erased (Lt k max) lk) ->
    (erased (Nat) m1) (erased (Eq (Nat) max (Succ m1)) e)
    (erased (Nat) l) (erased (Nat) r) (erased (Add l r m1) sum) (erased (Braun l r) bal))
  (match erased lk _
    ((LtZ b)
      (let ((erased l) (erased r) (erased s) (erased ba)) (split-bound b))
      (values b (Refl (Nat) (Succ b)) l r s ba))
    ((LtS _ y _)
      (let ((erased l) (erased r) (erased s) (erased ba)) (split-bound y))
      (values y (Refl (Nat) (Succ y)) l r s ba))))

; inserting a key the trie lacks, below its bound: the size goes up by exactly one
(def-fns _ $ (many idmap-set-bd : (erased Type V) (subterm many (Nat) k) (many V v) (many (IdMap V) m)
    (erased (Nat) size) (erased (Nat) max) (erased (Bounded V m size max) bd)
    (erased (Absent V k m) ab) (erased (Lt k max) lk) ->
    (many (IdMap V) m2) (erased (Bounded V m2 (Succ size) max) bd2))
  (match many m _
    ((MEmpty _)
      (let ((erased m1) (erased eqm) (erased l) (erased r) (erased sum) (erased bal)) (bound-split max k lk))
      (let-match erased eqm (Refl _ _))
      (let-match erased bd (BdEmpty _ _))
      (match many (nat-halve k) (((IdMap V) r2) ((Bounded V r2 (Succ (Zero)) (Succ m1)) b2))
        ((HZ)
          (values (MNode _ (Some _ v) (MEmpty _) (MEmpty _))
            (BdSome _ v _ _ l r m1 sum bal (Zero) (BdEmpty _ l) (Zero) (BdEmpty _ r) (Zero) (AddZero (Zero)))))
        ((H1 k1 d dd)
          (let ((many o2) (erased bo2))
            (notail $ idmap-set-bd _ (subterm (lt-subterm k1 k $ double-lt k1 d dd)) k1 v (MEmpty _) (Zero) l
              (BdEmpty _ l) (ABEmpty _ k1) (half-lt-one k1 d l r m1 dd sum bal (lt-succ-inv d m1 lk))))
          (values (MNode _ (None _) o2 (MEmpty _))
            (BdNone _ _ _ l r m1 sum bal (Succ (Zero)) bo2 (Zero) (BdEmpty _ r) (Succ (Zero))
              (AddSucc (Zero) (Zero) (Zero) (AddZero (Zero))))))
        ((H2 k1 d dd)
          (let ((many t2b) (erased bt2))
            (notail $ idmap-set-bd _ (subterm (lt-subterm k1 k $ lt-weaken k1 (Succ d) $ double-lt k1 d dd)) k1 v (MEmpty _) (Zero) r
              (BdEmpty _ r) (ABEmpty _ k1) (half-lt-two k1 d l r m1 dd sum bal (lt-succ-inv (Succ d) m1 lk))))
          (values (MNode _ (None _) (MEmpty _) t2b)
            (BdNone _ _ _ l r m1 sum bal (Zero) (BdEmpty _ l) (Succ (Zero)) bt2 (Succ (Zero))
              (AddZero (Succ (Zero))))))))
    ((MNode _ here one two)
      (match many here (((IdMap V) rr) ((Bounded V rr (Succ size) max) b2))
        ((None _)
          (let-match erased bd (BdNone _ _ _ l r m1 sum bal so bo st bt sot ssum))
          (match many (nat-halve k) (((IdMap V) rr) ((Bounded V rr (Succ sot) (Succ m1)) b2))
            ((HZ)
              (values (MNode _ (Some _ v) one two)
                (BdSome _ v _ _ l r m1 sum bal so bo st bt sot ssum)))
            ((H1 k1 d dd)
              (let ((many onew) (erased bonew))
                (notail $ idmap-set-bd _ (subterm (lt-subterm k1 k $ double-lt k1 d dd)) k1 v one so l bo
                  (absent-one _ k1 d dd here one two ab)
                  (half-lt-one k1 d l r m1 dd sum bal (lt-succ-inv d m1 lk))))
              (values (MNode _ (None _) onew two)
                (BdNone _ _ _ l r m1 sum bal (Succ so) bonew st bt (Succ sot) (AddSucc so st sot ssum))))
            ((H2 k1 d dd)
              (let ((many tnew) (erased btnew))
                (notail $ idmap-set-bd _ (subterm (lt-subterm k1 k $ lt-weaken k1 (Succ d) $ double-lt k1 d dd)) k1 v two st r bt
                  (absent-two _ k1 d dd here one two ab)
                  (half-lt-two k1 d l r m1 dd sum bal (lt-succ-inv (Succ d) m1 lk))))
              (values (MNode _ (None _) one tnew)
                (BdNone _ _ _ l r m1 sum bal so bo (Succ st) btnew (Succ sot) (add-succ-right so st sot ssum))))))
        ((Some _ v0)
          (let-match erased bd (BdSome _ _ _ _ l r m1 sum bal so bo st bt sot ssum))
          (match many (nat-halve k) (((IdMap V) rr) ((Bounded V rr (Succ (Succ sot)) (Succ m1)) b2))
            (absurd (HZ) (absent-not-some _ v0 one two ab))
            ((H1 k1 d dd)
              (let ((many onew) (erased bonew))
                (notail $ idmap-set-bd _ (subterm (lt-subterm k1 k $ double-lt k1 d dd)) k1 v one so l bo
                  (absent-one _ k1 d dd here one two ab)
                  (half-lt-one k1 d l r m1 dd sum bal (lt-succ-inv d m1 lk))))
              (values (MNode _ (Some _ v0) onew two)
                (BdSome _ v0 _ _ l r m1 sum bal (Succ so) bonew st bt (Succ sot) (AddSucc so st sot ssum))))
            ((H2 k1 d dd)
              (let ((many tnew) (erased btnew))
                (notail $ idmap-set-bd _ (subterm (lt-subterm k1 k $ lt-weaken k1 (Succ d) $ double-lt k1 d dd)) k1 v two st r bt
                  (absent-two _ k1 d dd here one two ab)
                  (half-lt-two k1 d l r m1 dd sum bal (lt-succ-inv (Succ d) m1 lk))))
              (values (MNode _ (Some _ v0) one tnew)
                (BdSome _ v0 _ _ l r m1 sum bal so bo (Succ st) btnew (Succ sot) (add-succ-right so st sot ssum))))))))))

; size + rest = max with size < max: rest is a successor, so it is what a walk can recurse on
(def-fns _ $ (erased add-room : (erased (Nat) size) (erased (Nat) rest) (erased (Nat) max)
    (subterm erased (Add size rest max) sum) (erased (Lt size max) lt) ->
    (erased (Nat) rest2) (erased (Add (Succ size) rest2 max) sum2) (erased (Lt rest2 rest) less))
  (match erased sum _
    ((AddZero _)
      (let-match erased lt (LtZ b2))
      (values b2 (AddSucc (Zero) b2 b2 (AddZero b2)) (lt-succ b2)))
    ((AddSucc a b c q)
      (let ((erased rest2) (erased sum2) (erased less)) (add-room a b c q (lt-succ-inv a c lt)))
      (values rest2 (AddSucc (Succ a) rest2 c sum2) less))))

; the whole step: insert a fresh key and hand back the strictly smaller measure
(def-fns _ $ (many seen-add : (erased Type V) (many (Nat) k) (many V v) (many (IdMap V) m)
    (erased (Nat) size) (erased (Nat) rest) (erased (Nat) max) (erased (Bounded V m size max) bd)
    (erased (Add size rest max) sum) (erased (Absent V k m) ab) (erased (Lt k max) lk) ->
    (many (IdMap V) m2) (erased (Nat) rest2) (erased (Bounded V m2 (Succ size) max) bd2)
    (erased (Add (Succ size) rest2 max) sum2) (erased (Lt rest2 rest) less))
  (let ((many m2) (erased bd2)) (idmap-set-bd _ k v m size max bd ab lk))
  (let ((erased rest2) (erased sum2) (erased less))
    (add-room size rest max sum (lt-succ-inv size max (bounded-le _ m2 (Succ size) max bd2))))
  (values m2 rest2 bd2 sum2 less))

; ---- A generic merge sort, in the shape of tests/map.sl's factory: the comparison is a parameter,
; so the sort sits above its level and the factory mints the level relating them. The split is a
; Braun-shaped pile built by insertion, so every recursion here is structural.

(def-adts $ (Pile : (Type A) -> Type)
  enum
  (many PLeaf : (erased Type A) -> (Pile A))
  (many PNode : (erased Type A) (many A x) (many (Pile A) l) (many (Pile A) r) -> (Pile A)))

(def-fns _ $ (many pile-add : (erased Type A) (many A x) (subterm many (Pile A) t) -> (many (Pile A) r))
  (match many t _
    ((PLeaf _) (PNode A x (PLeaf A) (PLeaf A)))
    ((PNode _ y l rr) (PNode A x (notail $ pile-add A y rr) l))))

(def-fns _ $ (many pile-of : (erased Type A) (subterm many (List A) xs) (many (Pile A) t) -> (many (Pile A) r))
  (match many xs _
    ((Nil _) t)
    ((Cons _ x rest) (tail (pile-of A rest (pile-add A x t))))))

(def-fns _ $ (many rev-onto : (erased Type A) (subterm many (List A) acc) (many (List A) ys) -> (many (List A) r))
  (match many acc _
    ((Nil _) ys)
    ((Cons _ x rest) (tail (rev-onto A rest (Cons A x ys))))))

(def-fns _ $ (many sort-factory : (erased (Level) M) ->
    (erased (Level) L)
    (many (Fn L (erased Type A)
              (many (Fn M (many A x) (many A y) -> (many (Bool) b)) leq)
              (many (List A) xs) ->
              (many (List A) ys))
          sorted))
  ; lexicographic: the first list shrinks, or it passes on unchanged and the second shrinks
  ; [acc] the output so far, newest first, so the merge itself runs in constant stack
  (def-fns _ $ (many merge : (erased Type A)
      (many (Fn M (many A x) (many A y) -> (many (Bool) b)) leq)
      (subterm many (List A) xs) (subterm many (List A) ys) (many (List A) acc) -> (many (List A) zs))
    (let-match many xs (Cons _ x xr) ((Nil _) (tail (rev-onto A acc ys))))
    (let-match many ys (Cons _ y yr) ((Nil _) (tail (rev-onto A acc xs))))
    (match many (leq x y) (((List A) _))
      ((BTrue) (tail (merge A leq xr ys (Cons A x acc))))
      ((BFalse) (tail (merge A leq xs yr (Cons A y acc))))))
  (def-fns _ $ (many pile-sort : (erased Type A)
      (many (Fn M (many A x) (many A y) -> (many (Bool) b)) leq)
      (subterm many (Pile A) t) -> (many (List A) r))
    (match many t _
      ((PLeaf _) (Nil A))
      ((PNode _ x l rr)
        (merge A leq (Cons A x $ Nil A) (merge A leq (notail $ pile-sort A leq l) (notail $ pile-sort A leq rr) (Nil A)) (Nil A)))))
  (def-fns _ $ (many sort : (erased Type A)
      (many (Fn M (many A x) (many A y) -> (many (Bool) b)) leq)
      (many (List A) xs) -> (many (List A) ys))
    (pile-sort A leq (pile-of A xs (PLeaf A))))
  (values (level-of sort) sort))
