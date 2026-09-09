; self/base.sl -- foundations for the self-hosted compiler (self/README.md): booleans, pairs, orderings,
; Nat/Char/String helpers over the prelude's externs, Bin-keyed identifiers and a trie map over them, a
; trie map keyed by names, list helpers and a rope of output chunks. Everything here is plain SL checked
; by the reference interpreter; nothing is settled design.

(def-adts $ Bool : -> Type
  enum
  (many BTrue : -> (Bool))
  (many BFalse : -> (Bool)))

(def-adts $ Ord : -> Type
  enum
  (many OLt : -> (Ord))
  (many OEq : -> (Ord))
  (many OGt : -> (Ord)))

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
  (match many (lt-dec a b) _ ((Yes x y p) (BTrue)) ((No x y q) (BFalse))))

(def-fns _ $ many nat-eq : (many (Nat) a) (many (Nat) b) -> (many (Bool) r)
  (match many (nat-lt a b) _
    ((BTrue) (BFalse))
    ((BFalse) (not $ nat-lt b a))))

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
  (nat-eq (char-code a) $ char-code b))

(def-fns _ $ many char-is : (many (Char) c) (many (Nat) code) -> (many (Bool) r)
  (nat-eq (char-code c) code))

; code in [lo, hi]
(def-fns _ $ many char-between : (many (Char) c) (many (Nat) lo) (many (Nat) hi) -> (many (Bool) r)
  (let (many n) $ char-code c)
  (and (not $ nat-lt n lo) $ not $ nat-lt hi n))

(def-fns _ $ many str-eq : (subterm many (String) a) (many (String) b) -> (many (Bool) r)
  (match many a _
    ((SNil) (match many b _ ((SNil) (BTrue)) ((SCons c r) (BFalse))))
    ((SCons c1 r1)
      (match many b _
        ((SNil) (BFalse))
        ((SCons c2 r2)
          (match many (char-eq c1 c2) _
            ((BTrue) (str-eq r1 r2))
            ((BFalse) (BFalse))))))))

(def-fns _ $ many str-is-empty : (many (String) s) -> (many (Bool) r)
  (match many s _ ((SNil) (BTrue)) ((SCons c r) (BFalse))))

(def-fns _ $ many str-of-chars : (subterm many (List $ Char) cs) -> (many (String) s)
  (match many cs _
    ((Nil a) (SNil))
    ((Cons a c rest) (SCons c $ str-of-chars rest))))

(def-fns _ $ many str-rev-onto : (subterm many (String) s) (many (String) acc) -> (many (String) r)
  (match many s _
    ((SNil) acc)
    ((SCons c rest) (str-rev-onto rest $ SCons c acc))))

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
    ((Cons a d rest) (match many (nat-eq d 9) _ ((BTrue) (Cons _ 0 $ dec-succ rest)) ((BFalse) (Cons _ (Succ d) rest))))))

(def-fns _ $ many count-up : (subterm many (Nat) n) (many (List $ Nat) ds) -> (many (List $ Nat) r)
  (match many n _
    ((Zero) ds)
    ((Succ m) (count-up m $ dec-succ ds))))

(def-fns _ $ many digits-str : (subterm many (List $ Nat) ds) (many (String) acc) -> (many (String) s)
  (match many ds _
    ((Nil a) acc)
    ((Cons a d rest) (digits-str rest $ SCons (digit-char d) acc))))

(def-fns _ $ many nat-str : (many (Nat) n) -> (many (String) s)
  (digits-str (count-up n $ Cons _ 0 $ Nil _) $ SNil))

; The OCaml spelling of a string literal's body: quote, backslash, newline and tab escaped, other bytes
; outside the printable range as decimal escapes.
(def-fns _ $ many ocaml-escape : (subterm many (String) s) -> (many (String) r)
  (match many s _
    ((SNil) (SNil))
    ((SCons c rest)
      (let (many tail) $ ocaml-escape rest)
      (let (many n) $ char-code c)
      (match many (nat-eq n 34) (((String) r))
        ((BTrue) (SCons #\x5c $ SCons #\x22 tail))
        ((BFalse)
          (match many (nat-eq n 92) (((String) r))
            ((BTrue) (SCons #\x5c $ SCons #\x5c tail))
            ((BFalse)
              (match many (nat-eq n 10) (((String) r))
                ((BTrue) (SCons #\x5c $ SCons #\n tail))
                ((BFalse)
                  (match many (nat-eq n 9) (((String) r))
                    ((BTrue) (SCons #\x5c $ SCons #\t tail))
                    ((BFalse)
                      (match many (or (nat-lt n 32) $ nat-lt 126 n) (((String) r))
                        ((BTrue)
                          (let (many d) $ nat-str n)
                          (let (many (String) d3) (match many (nat-lt n 10) _
                                           ((BTrue) (SCons #\0 $ SCons #\0 d))
                                           ((BFalse) (match many (nat-lt n 100) (((String) p))
                                                       ((BTrue) (SCons #\0 d))
                                                       ((BFalse) d)))))
                          (SCons #\x5c $ str-cat d3 tail))
                        ((BFalse) (SCons c tail))))))))))))))

; An SL name as an OCaml identifier fragment: letters and digits kept, anything else an underscore.
(def-fns _ $ many sanitize : (subterm many (String) s) -> (many (String) r)
  (match many s _
    ((SNil) (SNil))
    ((SCons c rest)
      (let (many tail) $ sanitize rest)
      (let (many ok) (or (char-between c 48 57)
                        $ or (char-between c 65 90) $ char-between c 97 122))
      (match many ok (((String) r))
        ((BTrue) (SCons c tail))
        ((BFalse) (SCons #\_ tail))))))

; ---- Bin identifiers

(def-fns _ $ many bin-succ : (subterm many (Bin) b) -> (many (Bin) c)
  (match many b _
    ((BZ) (B1 $ BZ))
    ((B1 b1) (B2 b1))
    ((B2 b1) (B1 $ bin-succ b1))))

(def-fns _ $ many bin-cmp : (subterm many (Bin) a) (many (Bin) b) -> (many (Ord) o)
  (match many a _
    ((BZ) (match many b _ ((BZ) (OEq)) (else (OLt))))
    ((B1 a1)
      (match many b _
        ((BZ) (OGt))
        ((B1 b1) (bin-cmp a1 b1))
        ((B2 b1) (match many (bin-cmp a1 b1) _ ((OGt) (OGt)) (else (OLt))))))
    ((B2 a1)
      (match many b _
        ((BZ) (OGt))
        ((B2 b1) (bin-cmp a1 b1))
        ((B1 b1) (match many (bin-cmp a1 b1) _ ((OLt) (OLt)) (else (OGt))))))))

(def-fns _ $ many bin-eq : (many (Bin) a) (many (Bin) b) -> (many (Bool) r)
  (match many (bin-cmp a b) _ ((OEq) (BTrue)) (else (BFalse))))

(def-fns _ $ many bin-lt : (many (Bin) a) (many (Bin) b) -> (many (Bool) r)
  (match many (bin-cmp a b) _ ((OLt) (BTrue)) (else (BFalse))))

; The digits of a Bin, least significant first, as text: an injective spelling for OCaml names.
(def-fns _ $ many bin-str : (subterm many (Bin) b) -> (many (String) s)
  (match many b _
    ((BZ) (SNil))
    ((B1 b1) (SCons #\1 $ bin-str b1))
    ((B2 b1) (SCons #\2 $ bin-str b1))))

; ---- IdMap: a persistent trie keyed by a Bin's digits

(def-adts
  (IdMap : (Type V) -> Type
    enum
    (many MEmpty : (erased Type V) -> (IdMap V))
    (many MNode : (erased Type V) (many (Maybe V) here) (many (IdMap V) one) (many (IdMap V) two) -> (IdMap V))))

(def-fns _ $ many idmap-get : (erased Type V) (subterm many (Bin) k) (many (IdMap V) m) -> (many (Maybe V) r)
  (match many m _
    ((MEmpty a) (None _))
    ((MNode a here one two)
      (match many k _
        ((BZ) here)
        ((B1 k1) (idmap-get _ k1 one))
        ((B2 k1) (idmap-get _ k1 two))))))

; A lookup that also proves the value found is a subterm of the map, for a recursion that continues into it.
(def-adts $ MapHit : (Type V) ((IdMap V) m) -> Type
  enum
  (many MkMapHit : (erased Type V) (erased (IdMap V) m) (many V v) (erased (Subterm V v (IdMap V) m) p) -> (MapHit V m)))

(def-fns _ $ many idmap-get-sub : (erased Type V) (subterm many (Bin) k) (many (IdMap V) m) -> (many (Maybe $ MapHit V m) r)
  (match many m _
    ((MEmpty a) (None _))
    ((MNode a here one two)
      (match many k _
        ((BZ) (match many here _ ((None b) (None _)) ((Some b v) (Some _ $ MkMapHit _ _ v $ prove-subterm v m))))
        ((B1 k1)
          (match many (idmap-get-sub _ k1 one) _
            ((None b) (None _))
            ((Some b h) (match many h _ ((MkMapHit c d v p) (Some _ $ MkMapHit _ _ v $ subterm-trans p $ prove-subterm one m))))))
        ((B2 k1)
          (match many (idmap-get-sub _ k1 two) _
            ((None b) (None _))
            ((Some b h) (match many h _ ((MkMapHit c d v p) (Some _ $ MkMapHit _ _ v $ subterm-trans p $ prove-subterm two m))))))))))

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
  (match many (idmap-get _ k m) _ ((None a) (BFalse)) ((Some a v) (BTrue))))

; ---- NameMap: a persistent trie keyed by a string's characters

(def-adts
  (NameMap : (Type V) -> Type
    enum
    (many NMNode : (erased Type V) (many (Maybe V) here) (many (List $ NMKid V) kids) -> (NameMap V)))
  (NMKid : (Type V) -> Type
    enum
    (many MkKid : (erased Type V) (many (Char) c) (many (NameMap V) sub) -> (NMKid V))))

(def-fns _ $ many nm-empty : (erased Type V) -> (many (NameMap V) m)
  (NMNode _ (None _) $ Nil _))

(def-fns _ $ many nm-kid : (erased Type V) (subterm many (List $ NMKid V) kids) (many (Char) c) -> (many (Maybe $ NameMap V) r)
  (match many kids _
    ((Nil a) (None _))
    ((Cons a k rest)
      (match many k _
        ((MkKid b c1 sub)
          (match many (char-eq c c1) _
            ((BTrue) (Some _ sub))
            ((BFalse) (nm-kid _ rest c))))))))

(def-fns _ $ many nm-get : (erased Type V) (subterm many (String) name) (many (NameMap V) m) -> (many (Maybe V) r)
  (match many m _
    ((NMNode a here kids)
      (match many name _
        ((SNil) here)
        ((SCons c rest)
          (match many (nm-kid _ kids c) _
            ((None b) (None _))
            ((Some b sub) (nm-get _ rest sub))))))))

(def-fns _ $ many nm-replace-kid : (erased Type V) (subterm many (List $ NMKid V) kids) (many (Char) c) (many (NameMap V) sub) -> (many (List $ NMKid V) r)
  (match many kids _
    ((Nil a) (Cons _ (MkKid _ c sub) $ Nil _))
    ((Cons a k rest)
      (match many k _
        ((MkKid b c1 old)
          (match many (char-eq c c1) _
            ((BTrue) (Cons _ (MkKid _ c sub) rest))
            ((BFalse) (Cons _ k $ nm-replace-kid _ rest c sub))))))))

(def-fns _ $ many nm-set : (erased Type V) (subterm many (String) name) (many V v) (many (NameMap V) m) -> (many (NameMap V) r)
  (match many m _
    ((NMNode a here kids)
      (match many name _
        ((SNil) (NMNode _ (Some _ v) kids))
        ((SCons c rest)
          (let (many (NameMap V) sub) (match many (nm-kid _ kids c) _
                            ((None b) (nm-empty _))
                            ((Some b s) s)))
          (NMNode _ here $ nm-replace-kid _ kids c $ nm-set _ rest v sub))))))

; ---- Lists

(def-fns _ $ many list-length : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n)
  (match many xs _
    ((Nil a) (Zero))
    ((Cons a x rest) (Succ $ list-length _ rest))))

(def-fns _ $ many list-rev-onto : (erased Type A) (subterm many (List A) xs) (many (List A) acc) -> (many (List A) r)
  (match many xs _
    ((Nil a) acc)
    ((Cons a x rest) (list-rev-onto _ rest $ Cons _ x acc))))

(def-fns _ $ many list-rev : (erased Type A) (many (List A) xs) -> (many (List A) r)
  (list-rev-onto _ xs $ Nil _))

(def-fns _ $ many list-append : (erased Type A) (subterm many (List A) xs) (many (List A) ys) -> (many (List A) r)
  (match many xs _
    ((Nil a) ys)
    ((Cons a x rest) (Cons _ x $ list-append _ rest ys))))

(def-fns _ $ many list-nth : (erased Type A) (subterm many (List A) xs) (many (Nat) i) -> (many (Maybe A) r)
  (match many xs _
    ((Nil a) (None _))
    ((Cons a x rest)
      (match many i _
        ((Zero) (Some _ x))
        ((Succ k) (list-nth _ rest k))))))

(def-fns _ $ many list-is-empty : (erased Type A) (many (List A) xs) -> (many (Bool) r)
  (match many xs _ ((Nil a) (BTrue)) ((Cons a x rest) (BFalse))))

(def-fns _ $ many list-mem-str : (subterm many (List $ String) xs) (many (String) x) -> (many (Bool) r)
  (match many xs _
    ((Nil a) (BFalse))
    ((Cons a y rest)
      (match many (str-eq x y) _
        ((BTrue) (BTrue))
        ((BFalse) (list-mem-str rest x))))))

(def-fns _ $ many list-mem-bin : (subterm many (List $ Bin) xs) (many (Bin) x) -> (many (Bool) r)
  (match many xs _
    ((Nil a) (BFalse))
    ((Cons a y rest)
      (match many (bin-eq x y) _
        ((BTrue) (BTrue))
        ((BFalse) (list-mem-bin rest x))))))

(def-fns _ $ many index-of-bin : (subterm many (List $ Bin) xs) (many (Bin) x) (many (Nat) i) -> (many (Maybe $ Nat) r)
  (match many xs _
    ((Nil a) (None _))
    ((Cons a y rest)
      (match many (bin-eq x y) _
        ((BTrue) (Some _ i))
        ((BFalse) (index-of-bin rest x $ Succ i))))))

; ---- Rope: output built as a tree of chunks, never by appending long strings

(def-adts $ Rope : -> Type
  enum
  (many REmpty : -> (Rope))
  (many RStr : (many (String) s) -> (Rope))
  (many RCat : (many (Rope) a) (many (Rope) b) -> (Rope)))

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

;  A rope as one string, for short diagnostics only.
(def-fns _ $ many rope-str : (subterm many (Rope) r) -> (many (String) s)
  (match many r _
    ((REmpty) (SNil))
    ((RStr s) s)
    ((RCat a b) (str-append (rope-str a) $ rope-str b))))

; Flattens a rope into an IO chain writing each chunk, ending in [next].
(def-fns _ $ many rope-io : (erased (Level) L) (subterm many (Rope) r) (many (IO L) next) -> (many (IO L) io)
  (match many r _
    ((REmpty) next)
    ((RStr s) (WriteOut _ s next))
    ((RCat a b) (rope-io _ a $ rope-io _ b next))))
