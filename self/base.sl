; self/base.sl -- foundations for the self-hosted compiler (self/README.md): booleans, pairs, orders and
; their decisions, Nat/Char/String helpers over the prelude's externs, Bin-keyed identifiers and a trie map over them, a
; trie map keyed by names, list helpers and a rope of output chunks. Everything here is plain SL checked
; by the reference interpreter; nothing is settled design.

(def-adts $ Bool : -> Type
  enum
  (many BTrue : -> (Bool))
  (many BFalse : -> (Bool)))

(def-adts
  (Pair : (Type A) (Type B) -> Type
    enum
    (many MkPair : (erased Type A) (erased Type B) (many A fst) (many B snd) -> (Pair A B))))

(def-fns _ $ many not : (many (Bool) b) -> (many (Bool) r)
  (match many b _ ((BTrue) (BFalse)) ((BFalse) (BTrue))))

(def-fns _ $ many and : (many (Bool) a) (many (Bool) b) -> (many (Bool) r)
  (match many a _ ((BTrue) b) ((BFalse) (BFalse))))

(def-fns _ $ many or : (many (Bool) a) (many (Bool) b) -> (many (Bool) r)
  (match many a _ ((BTrue) (BTrue)) ((BFalse) b)))

; ---- Nat

(def-fns _ $ many nat-lt : (many (Nat) a) (many (Nat) b) -> (many (Bool) r)
  (match many (nat-cmp a b) _ ((CLt eq-t eq-r eq-x eq-y eq-p) (BTrue)) (else (BFalse))))

(def-fns _ $ many nat-eq : (many (Nat) a) (many (Nat) b) -> (many (Bool) r)
  (match many (nat-cmp a b) _ ((CEq eq-t eq-r eq-x) (BTrue)) (else (BFalse))))

(def-fns _ $ many nat-pred : (many (Nat) n) -> (many (Nat) m)
  (match many n _ ((Zero) (Zero)) ((Succ k) k)))

(def-fns _ $ many nat-sub : (many (Nat) a) (subterm many (Nat) b) -> (many (Nat) c)
  (match many b _ ((Zero) a) ((Succ b1) (nat-sub (nat-pred a) b1))))

(def-fns _ $ many nat-is-zero : (many (Nat) n) -> (many (Bool) r)
  (match many n _ ((Zero) (BTrue)) ((Succ k) (BFalse))))

; ---- Char and String

(let (many zero-below-modulus) $ lt-dec 0 u8-modulus)
(comptime-match zero-below-modulus (Yes zero-lt-a zero-lt-b zero-lt))
(let (many char-zero) $ MkChar $ MkU8 0 zero-lt)

(def-fns _ $ many char-code : (many (Char) c) -> (many (Nat) n)
  (let-match many c (MkChar u))
  (let-match many u (MkU8 k p))
  k)

; A code the modulus does not bound, which no Char holds, becomes char-zero.
(def-fns _ $ many char-of-code : (many (Nat) n) -> (many (Char) c)
  (match many (lt-dec n u8-modulus) _
    ((Yes a b p) (MkChar $ MkU8 n p))
    ((No a b q) char-zero)))

(def-fns _ $ many char-eq : (many (Char) a) (many (Char) b) -> (many (Bool) r)
  (match many (char-cmp a b) _ ((CEq eq-t eq-r eq-x) (BTrue)) (else (BFalse))))

(def-fns _ $ many char-is : (many (Char) c) (many (Nat) code) -> (many (Bool) r)
  (nat-eq (char-code c) code))

; code in [lo, hi]
(def-fns _ $ many char-between : (many (Char) c) (many (Nat) lo) (many (Nat) hi) -> (many (Bool) r)
  (let (many n) $ char-code c)
  (and (not $ nat-lt n lo) $ not $ nat-lt hi n))

; The lexicographic order on strings, and its decision with proofs: CEq forces the two strings equal.
(def-adts
  (StrLt : ((String) a) ((String) b) -> Type
    enum
    (many SLtNil : (erased (Char) d) (erased (String) t) -> (StrLt (SNil) (SCons d t)))
    (many SLtHead : (erased (Char) c) (erased (Char) d) (erased (String) s) (erased (String) t) (erased (CharLt c d) p) -> (StrLt (SCons c s) (SCons d t)))
    (many SLtTail : (erased (Char) c) (erased (String) s) (erased (String) t) (erased (StrLt s t) p) -> (StrLt (SCons c s) (SCons c t)))))

(def-fns _ $ many str-cmp : (subterm many (String) a) (many (String) b) -> (many (Cmp (String) StrLt a b) r)
  (match many a _
    ((SNil) (match many b _ ((SNil) (CEq _ _ a)) ((SCons d t) (CLt _ _ a b $ SLtNil d t))))
    ((SCons c s)
      (match many b _
        ((SNil) (CGt _ _ a b $ SLtNil c s))
        ((SCons d t)
          (match many (char-cmp c d) _
            ((CLt ct cr cx cy p) (CLt _ _ a b $ SLtHead c d s t p))
            ((CEq ct cr cx)
              (match many (str-cmp s t) _
                ((CLt st sr sx sy q) (CLt _ _ a b $ SLtTail c s t q))
                ((CEq st sr sx) (CEq _ _ a))
                ((CGt st sr sx sy q) (CGt _ _ a b $ SLtTail c t s q))))
            ((CGt ct cr cx cy p) (CGt _ _ a b $ SLtHead d c t s p))))))))

(def-fns _ $ many rope-str : (many (Rope) r) -> (many (String) s)
  (let (many s) (erased p) (delegate (flatten r)))
  s)

(def-fns _ $ many str-eq : (many (String) a) (many (String) b) -> (many (Bool) r)
  (match many (str-cmp a b) _ ((CEq eq-t eq-r eq-x) (BTrue)) (else (BFalse))))

(def-fns _ $ many str-is-empty : (many (String) s) -> (many (Bool) r)
  (match many s _ ((SNil) (BTrue)) ((SCons c r) (BFalse))))

(def-fns _ $ many str-cat : (many (String) a) (many (String) b) -> (many (String) c)
  (str-append a b))

(def-fns _ $ many str-cat3 : (many (String) a) (many (String) b) (many (String) c) -> (many (String) d)
  (str-append a $ str-append b c))

(def-fns _ $ many str-length : (subterm many (String) s) -> (many (Nat) n)
  (match many s _
    ((SNil) (Zero))
    ((SCons c rest) (Succ $ str-length rest))))

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

; Decimal digits of a Nat, least significant first, counted up from zero.
(def-fns _ $ many digit-char : (many (Nat) d) -> (many (Char) c)
  (char-of-code $ nat-add 48 d))

(def-fns _ $ many dec-succ : (subterm many (List $ Nat) ds) -> (many (List $ Nat) r)
  (match many ds _
    ((Nil a) (Cons _ 1 $ Nil _))
    ((Cons a d rest) (match many (nat-cmp d 9) _ ((CEq eq-t eq-r eq-x) (Cons _ 0 $ dec-succ rest)) (else (Cons _ (Succ d) rest))))))

(def-fns _ $ many count-up : (subterm many (Nat) n) (many (List $ Nat) ds) -> (many (List $ Nat) r)
  (match many n _
    ((Zero) ds)
    ((Succ m) (count-up m $ dec-succ ds))))

(def-fns _ $ many digits-rope : (subterm many (List $ Nat) ds) (many (Rope) acc) -> (many (Rope) r)
  (match many ds _
    ((Nil a) acc)
    ((Cons a d rest) (digits-rope rest $ RCat (RChar $ digit-char d) acc))))

(def-fns _ $ many nat-str : (many (Nat) n) -> (many (String) s)
  (rope-str $ digits-rope (count-up n $ Cons _ 0 $ Nil _) $ REmpty))

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

; ---- Bin identifiers

(def-fns _ $ many bin-succ : (subterm many (Bin) b) -> (many (Bin) c)
  (match many b _
    ((BZ) (B1 $ BZ))
    ((B1 b1) (B2 b1))
    ((B2 b1) (B1 $ bin-succ b1))))

; The order on ids, digit by digit (B1 a is 2a+1, B2 a is 2a+2), and its decision with proofs.
(def-adts
  (BinLt : ((Bin) a) ((Bin) b) -> Type
    enum
    (many LtZ1 : (erased (Bin) b) -> (BinLt (BZ) $ B1 b))
    (many LtZ2 : (erased (Bin) b) -> (BinLt (BZ) $ B2 b))
    (many Lt11 : (erased (Bin) a) (erased (Bin) b) (erased (BinLt a b) p) -> (BinLt (B1 a) $ B1 b))
    (many Lt12 : (erased (Bin) a) (erased (Bin) b) (erased (BinLe a b) p) -> (BinLt (B1 a) $ B2 b))
    (many Lt21 : (erased (Bin) a) (erased (Bin) b) (erased (BinLt a b) p) -> (BinLt (B2 a) $ B1 b))
    (many Lt22 : (erased (Bin) a) (erased (Bin) b) (erased (BinLt a b) p) -> (BinLt (B2 a) $ B2 b)))
  (BinLe : ((Bin) a) ((Bin) b) -> Type
    enum
    (many LeZ : (erased (Bin) b) -> (BinLe (BZ) b))
    (many Le11 : (erased (Bin) a) (erased (Bin) b) (erased (BinLe a b) p) -> (BinLe (B1 a) $ B1 b))
    (many Le12 : (erased (Bin) a) (erased (Bin) b) (erased (BinLe a b) p) -> (BinLe (B1 a) $ B2 b))
    (many Le21 : (erased (Bin) a) (erased (Bin) b) (erased (BinLt a b) p) -> (BinLe (B2 a) $ B1 b))
    (many Le22 : (erased (Bin) a) (erased (Bin) b) (erased (BinLe a b) p) -> (BinLe (B2 a) $ B2 b))))

(def-fns _ $ erased le-refl : (subterm erased (Bin) a) -> (erased (BinLe a a) r)
  (match erased a _
    ((BZ) (LeZ _))
    ((B1 a1) (Le11 _ _ $ le-refl a1))
    ((B2 a1) (Le22 _ _ $ le-refl a1))))

(def-fns _ $ erased lt-le : (erased (Bin) a) (erased (Bin) b) (subterm erased (BinLt a b) p) -> (erased (BinLe a b) r)
  (match erased p _
    ((LtZ1 b1) (LeZ _)) ((LtZ2 b1) (LeZ _))
    ((Lt11 a1 b1 q) (Le11 _ _ $ lt-le a1 b1 q))
    ((Lt12 a1 b1 q) (Le12 _ _ q))
    ((Lt21 a1 b1 q) (Le21 _ _ q))
    ((Lt22 a1 b1 q) (Le22 _ _ $ lt-le a1 b1 q))))

(def-fns _ $ many bin-cmp : (subterm many (Bin) a) (many (Bin) b) -> (many (Cmp (Bin) BinLt a b) r)
  (match many a _
    ((BZ) (match many b _ ((BZ) (CEq _ _ a)) ((B1 b1) (CLt _ _ a b $ LtZ1 b1)) ((B2 b1) (CLt _ _ a b $ LtZ2 b1))))
    ((B1 a1)
      (match many b _
        ((BZ) (CGt _ _ a b $ LtZ1 a1))
        ((B1 b1) (match many (bin-cmp a1 b1) _ ((CLt t r x y p) (CLt _ _ a b $ Lt11 a1 b1 p)) ((CEq t r x) (CEq _ _ a)) ((CGt t r x y p) (CGt _ _ a b $ Lt11 b1 a1 p))))
        ((B2 b1) (match many (bin-cmp a1 b1) _ ((CLt t r x y p) (CLt _ _ a b $ Lt12 a1 b1 $ lt-le a1 b1 p)) ((CEq t r x) (CLt _ _ a b $ Lt12 a1 a1 $ le-refl a1)) ((CGt t r x y p) (CGt _ _ a b $ Lt21 b1 a1 p))))))
    ((B2 a1)
      (match many b _
        ((BZ) (CGt _ _ a b $ LtZ2 a1))
        ((B1 b1) (match many (bin-cmp a1 b1) _ ((CLt t r x y p) (CLt _ _ a b $ Lt21 a1 b1 p)) ((CEq t r x) (CGt _ _ a b $ Lt12 a1 a1 $ le-refl a1)) ((CGt t r x y p) (CGt _ _ a b $ Lt12 b1 a1 $ lt-le b1 a1 p))))
        ((B2 b1) (match many (bin-cmp a1 b1) _ ((CLt t r x y p) (CLt _ _ a b $ Lt22 a1 b1 p)) ((CEq t r x) (CEq _ _ a)) ((CGt t r x y p) (CGt _ _ a b $ Lt22 b1 a1 p))))))))

(def-fns _ $ many bin-eq : (many (Bin) a) (many (Bin) b) -> (many (Bool) r)
  (match many (bin-cmp a b) _ ((CEq eq-t eq-r eq-x) (BTrue)) (else (BFalse))))

(def-fns _ $ many bin-lt : (many (Bin) a) (many (Bin) b) -> (many (Bool) r)
  (match many (bin-cmp a b) _ ((CLt eq-t eq-r eq-x eq-y eq-p) (BTrue)) (else (BFalse))))

; The digits of a Bin, least significant first, as text: an injective spelling for OCaml names.
(def-fns _ $ many bin-rope : (subterm many (Bin) b) -> (many (Rope) r)
  (match many b _
    ((BZ) (REmpty))
    ((B1 b1) (RCat (RChar #\1) $ bin-rope b1))
    ((B2 b1) (RCat (RChar #\2) $ bin-rope b1))))

(def-fns _ $ many bin-str : (many (Bin) b) -> (many (String) s)
  (rope-str $ bin-rope b))

; ---- IdMap: a persistent trie keyed by a Bin's digits

(def-adts
  (IdMap : (Type V) -> Type
    enum
    (many MEmpty : (erased Type V) -> (IdMap V))
    (many MNode : (erased Type V) (many (Maybe V) here) (many (IdMap V) one) (many (IdMap V) two) -> (IdMap V))))

; A lookup's evidence: the key's digits lead to the value, or to an empty map or an empty slot.
(def-adts
  (MapsTo : (Type V) ((Bin) k) (V v) ((IdMap V) m) -> Type
    enum
    (many MTHere : (erased Type V) (erased V v) (erased (IdMap V) one) (erased (IdMap V) two) -> (MapsTo V (BZ) v $ MNode V (Some V v) one two))
    (many MT1 : (erased Type V) (erased (Bin) k) (erased V v) (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two) (erased (MapsTo V k v one) p) ->
       (MapsTo V (B1 k) v $ MNode V here one two))
    (many MT2 : (erased Type V) (erased (Bin) k) (erased V v) (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two) (erased (MapsTo V k v two) p) ->
       (MapsTo V (B2 k) v $ MNode V here one two)))
  (Absent : (Type V) ((Bin) k) ((IdMap V) m) -> Type
    enum
    (many ABEmpty : (erased Type V) (erased (Bin) k) -> (Absent V k $ MEmpty V))
    (many ABHere : (erased Type V) (erased (IdMap V) one) (erased (IdMap V) two) -> (Absent V (BZ) $ MNode V (None V) one two))
    (many AB1 : (erased Type V) (erased (Bin) k) (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two) (erased (Absent V k one) p) -> (Absent V (B1 k) $ MNode V here one two))
    (many AB2 : (erased Type V) (erased (Bin) k) (erased (Maybe V) here) (erased (IdMap V) one) (erased (IdMap V) two) (erased (Absent V k two) p) -> (Absent V (B2 k) $ MNode V here one two)))
  (Lookup : (Type V) ((Bin) k) ((IdMap V) m) -> Type
    enum
    (many Hit : (erased Type V) (erased (Bin) k) (erased (IdMap V) m) (many V v) (erased (MapsTo V k v m) p) -> (Lookup V k m))
    (many Miss : (erased Type V) (erased (Bin) k) (erased (IdMap V) m) (erased (Absent V k m) p) -> (Lookup V k m))))

(def-fns _ $ many idmap-get : (erased Type V) (subterm many (Bin) k) (many (IdMap V) m) -> (many (Lookup V k m) r)
  (match many m _
    ((MEmpty a) (Miss _ _ _ $ ABEmpty _ k))
    ((MNode a here one two)
      (match many k _
        ((BZ) (match many here _ ((None b) (Miss _ _ _ $ ABHere _ one two)) ((Some b v) (Hit _ _ _ v $ MTHere _ v one two))))
        ((B1 k1)
          (match many (idmap-get _ k1 one) _
            ((Hit t kk mm v p) (Hit _ _ _ v $ MT1 _ k1 v here one two p))
            ((Miss t kk mm p) (Miss _ _ _ $ AB1 _ k1 here one two p))))
        ((B2 k1)
          (match many (idmap-get _ k1 two) _
            ((Hit t kk mm v p) (Hit _ _ _ v $ MT2 _ k1 v here one two p))
            ((Miss t kk mm p) (Miss _ _ _ $ AB2 _ k1 here one two p))))))))

; A value a map holds is a subterm of it, for a recursion that continues into it.
(def-fns _ $ erased mapsto-subterm : (erased Type V) (erased (Bin) k) (erased V v) (erased (IdMap V) m) (subterm erased (MapsTo V k v m) p) ->
    (erased (Subterm V v (IdMap V) m) s)
  (match erased p _
    ((MTHere t w one two) (prove-subterm v m))
    ((MT1 t k1 w here one two q) (subterm-trans (mapsto-subterm _ _ _ _ q) $ prove-subterm one m))
    ((MT2 t k1 w here one two q) (subterm-trans (mapsto-subterm _ _ _ _ q) $ prove-subterm two m))))

(def-fns _ $ many idmap-set : (erased Type V) (subterm many (Bin) k) (many V v) (many (IdMap V) m) -> (many (IdMap V) r)
  (let (many (Maybe V) here) (many (IdMap V) one) (many (IdMap V) two)
    (match many m _
      ((MEmpty a) (values (None _) (MEmpty _) $ MEmpty _))
      ((MNode a h o t) (values h o t))))
  (match many k _
    ((BZ) (MNode _ (Some _ v) one two))
    ((B1 k1) (MNode _ here (idmap-set _ k1 v one) two))
    ((B2 k1) (MNode _ here one $ idmap-set _ k1 v two))))

(def-fns _ $ many idmap-mem : (erased Type V) (many (Bin) k) (many (IdMap V) m) -> (many (Bool) r)
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
    ((LsNil a b) (match erased q _ ((LsNil c d) (LsNil _ _))))
    ((LsCons a b x y xs2 ys2 p2)
      (match erased q _
        ((LsCons c d y2 z ys3 zs2 q2) (LsCons _ _ x z xs2 zs2 $ lockstep-trans _ _ _ _ _ _ p2 q2))))))

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

(def-fns _ $ many list-is-empty : (erased Type A) (many (List A) xs) -> (many (Bool) r)
  (match many xs _ ((Nil a) (BTrue)) ((Cons a x rest) (BFalse))))

(def-fns _ $ many list-mem-str : (subterm many (List $ String) xs) (many (String) x) -> (many (Bool) r)
  (match many xs _
    ((Nil a) (BFalse))
    ((Cons a y rest)
      (match many (str-cmp x y) _
        ((CEq eq-t eq-r eq-x) (BTrue))
        (else (list-mem-str rest x))))))

(def-fns _ $ many list-mem-bin : (subterm many (List $ Bin) xs) (many (Bin) x) -> (many (Bool) r)
  (match many xs _
    ((Nil a) (BFalse))
    ((Cons a y rest)
      (match many (bin-cmp x y) _
        ((CEq eq-t eq-r eq-x) (BTrue))
        (else (list-mem-bin rest x))))))

(def-fns _ $ many index-of-bin : (subterm many (List $ Bin) xs) (many (Bin) x) (many (Nat) i) -> (many (Maybe $ Nat) r)
  (match many xs _
    ((Nil a) (None _))
    ((Cons a y rest)
      (match many (bin-cmp x y) _
        ((CEq eq-t eq-r eq-x) (Some _ i))
        (else (index-of-bin rest x $ Succ i))))))

; ---- Rope: output built as a tree of chunks (the prelude's), flattened once

(def-fns _ $ many rcat : (many (Rope) a) (many (Rope) b) -> (many (Rope) r)
  (RCat a b))

(def-fns _ $ many rcat3 : (many (Rope) a) (many (Rope) b) (many (Rope) c) -> (many (Rope) r)
  (RCat a $ RCat b c))

(def-fns _ $ many rcat4 : (many (Rope) a) (many (Rope) b) (many (Rope) c) (many (Rope) d) -> (many (Rope) r)
  (RCat a $ RCat b $ RCat c d))

(def-fns _ $ many rcat5 : (many (Rope) a) (many (Rope) b) (many (Rope) c) (many (Rope) d) (many (Rope) e) -> (many (Rope) r)
  (RCat a $ RCat b $ RCat c $ RCat d e))

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

