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
  (match many (lt-dec (predates _) a b) _ ((Yes x y p) (BTrue)) ((No x y q) (BFalse))))

(def-fns _ $ many nat-eq : (many (Nat) a) (many (Nat) b) -> (many (Bool) r)
  (match many (nat-lt (predates _) a b) _
    ((BTrue) (BFalse))
    ((BFalse) (not (predates _) (nat-lt (predates _) b a)))))

(def-fns _ $ many nat-pred : (many (Nat) n) -> (many (Nat) m)
  (match many n _ ((Zero) (Zero)) ((Succ k) k)))

(def-fns _ $ many nat-sub : (many (Nat) a) (subterm many (Nat) b) -> (many (Nat) c)
  (match many b _ ((Zero) a) ((Succ b1) (nat-sub (nat-pred (predates _) a) (subterm _) b1))))

(def-fns _ $ many nat-is-zero : (many (Nat) n) -> (many (Bool) r)
  (match many n _ ((Zero) (BTrue)) ((Succ k) (BFalse))))

; ---- Char and String

(def-fns _ $ many char-code : (many (Char) c) -> (many (Nat) n)
  (match many c _ ((MkChar u) (u8-to-nat (predates _) u))))

(def-fns _ $ many char-of-code : (many (Nat) n) -> (many (Char) c)
  (MkChar (nat-to-u8 (predates _) n)))

(def-fns _ $ many char-eq : (many (Char) a) (many (Char) b) -> (many (Bool) r)
  (nat-eq (predates _) (char-code (predates _) a) (char-code (predates _) b)))

(def-fns _ $ many char-is : (many (Char) c) (many (Nat) code) -> (many (Bool) r)
  (nat-eq (predates _) (char-code (predates _) c) code))

; code in [lo, hi]
(def-fns _ $ many char-between : (many (Char) c) (many (Nat) lo) (many (Nat) hi) -> (many (Bool) r)
  (let (many n) (char-code (predates _) c))
  (and (predates _) (not (predates _) (nat-lt (predates _) n lo)) (not (predates _) (nat-lt (predates _) hi n))))

(def-fns _ $ many str-eq : (subterm many (String) a) (many (String) b) -> (many (Bool) r)
  (match many a _
    ((SNil) (match many b _ ((SNil) (BTrue)) ((SCons c r) (BFalse))))
    ((SCons c1 r1)
      (match many b _
        ((SNil) (BFalse))
        ((SCons c2 r2)
          (match many (char-eq (predates _) c1 c2) _
            ((BTrue) (str-eq (subterm _) r1 r2))
            ((BFalse) (BFalse))))))))

(def-fns _ $ many str-is-empty : (many (String) s) -> (many (Bool) r)
  (match many s _ ((SNil) (BTrue)) ((SCons c r) (BFalse))))

(def-fns _ $ many str-of-chars : (subterm many (List (Char)) cs) -> (many (String) s)
  (match many cs _
    ((Nil a) (SNil))
    ((Cons a c rest) (SCons c (str-of-chars (subterm _) rest)))))

(def-fns _ $ many str-rev-onto : (subterm many (String) s) (many (String) acc) -> (many (String) r)
  (match many s _
    ((SNil) acc)
    ((SCons c rest) (str-rev-onto (subterm _) rest (SCons c acc)))))

(def-fns _ $ many str-cat : (many (String) a) (many (String) b) -> (many (String) c)
  (str-append (predates _) a b))

(def-fns _ $ many str-cat3 : (many (String) a) (many (String) b) (many (String) c) -> (many (String) d)
  (str-append (predates _) a (str-append (predates _) b c)))

(def-fns _ $ many str-length : (subterm many (String) s) -> (many (Nat) n)
  (match many s _
    ((SNil) (Zero))
    ((SCons c rest) (Succ (str-length (subterm _) rest)))))

; Decimal digits of a Nat, by repeated subtraction of ten; the fuel is the number itself.
(def-fns _ $ many digit-char : (many (Nat) d) -> (many (Char) c)
  (char-of-code (predates _) (nat-add (predates _) 48 d)))

(def-fns _
  (many divmod10 : (subterm many (Nat) fuel) (many (Nat) n) -> (many (Nat) q) (many (Nat) r)
    (match many fuel _
      ((Zero) (values (Zero) n))
      ((Succ k)
        (match many (nat-lt (predates _) n 10) _
          ((BTrue) (values (Zero) n))
          ((BFalse)
            (let (many q1) (many r1) (divmod10 (subterm _) k (nat-sub (predates _) n 10)))
            (values (Succ q1) r1))))))
  (many nat-digits : (subterm many (Nat) fuel) (many (Nat) n) (many (String) acc) -> (many (String) s)
    (match many fuel _
      ((Zero) acc)
      ((Succ k)
        (let (many q) (many r) (divmod10 (subterm _) k n))
        (let (many acc1) (SCons (digit-char (predates _) r) acc))
        (match many (nat-is-zero (predates _) q) _
          ((BTrue) acc1)
          ((BFalse) (nat-digits (subterm _) k q acc1)))))))

(def-fns _ $ many nat-str : (many (Nat) n) -> (many (String) s)
  (nat-digits (predates _) (Succ n) n (SNil)))

; The OCaml spelling of a string literal's body: quote, backslash, newline and tab escaped, other bytes
; outside the printable range as decimal escapes.
(def-fns _ $ many ocaml-escape : (subterm many (String) s) -> (many (String) r)
  (match many s _
    ((SNil) (SNil))
    ((SCons c rest)
      (let (many tail) (ocaml-escape (subterm _) rest))
      (let (many n) (char-code (predates _) c))
      (match many (nat-eq (predates _) n 34) (((String) r))
        ((BTrue) (SCons #\x5c (SCons #\x22 tail)))
        ((BFalse)
          (match many (nat-eq (predates _) n 92) (((String) r))
            ((BTrue) (SCons #\x5c (SCons #\x5c tail)))
            ((BFalse)
              (match many (nat-eq (predates _) n 10) (((String) r))
                ((BTrue) (SCons #\x5c (SCons #\n tail)))
                ((BFalse)
                  (match many (nat-eq (predates _) n 9) (((String) r))
                    ((BTrue) (SCons #\x5c (SCons #\t tail)))
                    ((BFalse)
                      (match many (or (predates _) (nat-lt (predates _) n 32) (nat-lt (predates _) 126 n)) (((String) r))
                        ((BTrue)
                          (let (many d) (nat-str (predates _) n))
                          (let (many d3) (match many (nat-lt (predates _) n 10) (((String) p))
                                           ((BTrue) (SCons #\0 (SCons #\0 d)))
                                           ((BFalse) (match many (nat-lt (predates _) n 100) (((String) p))
                                                       ((BTrue) (SCons #\0 d))
                                                       ((BFalse) d)))))
                          (SCons #\x5c (str-cat (predates _) d3 tail)))
                        ((BFalse) (SCons c tail))))))))))))))

; An SL name as an OCaml identifier fragment: letters and digits kept, anything else an underscore.
(def-fns _ $ many sanitize : (subterm many (String) s) -> (many (String) r)
  (match many s _
    ((SNil) (SNil))
    ((SCons c rest)
      (let (many tail) (sanitize (subterm _) rest))
      (let (many ok) (or (predates _) (char-between (predates _) c 48 57)
                        (or (predates _) (char-between (predates _) c 65 90) (char-between (predates _) c 97 122))))
      (match many ok (((String) r))
        ((BTrue) (SCons c tail))
        ((BFalse) (SCons #\_ tail))))))

; ---- Bin identifiers

(def-fns _ $ many bin-succ : (subterm many (Bin) b) -> (many (Bin) c)
  (match many b _
    ((BZ) (B1 (BZ)))
    ((B1 b1) (B2 b1))
    ((B2 b1) (B1 (bin-succ (subterm _) b1)))))

(def-fns _ $ many bin-cmp : (subterm many (Bin) a) (many (Bin) b) -> (many (Ord) o)
  (match many a _
    ((BZ) (match many b _ ((BZ) (OEq)) ((B1 x) (OLt)) ((B2 x) (OLt))))
    ((B1 a1)
      (match many b _
        ((BZ) (OGt))
        ((B1 b1) (bin-cmp (subterm _) a1 b1))
        ((B2 b1) (match many (bin-cmp (subterm _) a1 b1) _ ((OLt) (OLt)) ((OEq) (OLt)) ((OGt) (OGt))))))
    ((B2 a1)
      (match many b _
        ((BZ) (OGt))
        ((B2 b1) (bin-cmp (subterm _) a1 b1))
        ((B1 b1) (match many (bin-cmp (subterm _) a1 b1) _ ((OLt) (OLt)) ((OEq) (OGt)) ((OGt) (OGt))))))))

(def-fns _ $ many bin-eq : (many (Bin) a) (many (Bin) b) -> (many (Bool) r)
  (match many (bin-cmp (predates _) a b) _ ((OLt) (BFalse)) ((OEq) (BTrue)) ((OGt) (BFalse))))

(def-fns _ $ many bin-lt : (many (Bin) a) (many (Bin) b) -> (many (Bool) r)
  (match many (bin-cmp (predates _) a b) _ ((OLt) (BTrue)) ((OEq) (BFalse)) ((OGt) (BFalse))))

; The digits of a Bin, least significant first, as text: an injective spelling for OCaml names.
(def-fns _ $ many bin-str : (subterm many (Bin) b) -> (many (String) s)
  (match many b _
    ((BZ) (SNil))
    ((B1 b1) (SCons #\1 (bin-str (subterm _) b1)))
    ((B2 b1) (SCons #\2 (bin-str (subterm _) b1)))))

; ---- IdMap: a persistent trie keyed by a Bin's digits

(def-adts
  (IdMap : (Type V) -> Type
    enum
    (many MEmpty : (erased Type V) -> (IdMap V))
    (many MNode : (erased Type V) (many (Maybe V) here) (many (IdMap V) one) (many (IdMap V) two) -> (IdMap V))))

(def-fns _ $ many idmap-get : (erased Type V) (subterm many (Bin) k) (many (IdMap V) m) -> (many (Maybe V) r)
  (match many m _
    ((MEmpty a) (None V))
    ((MNode a here one two)
      (match many k _
        ((BZ) here)
        ((B1 k1) (idmap-get V (subterm _) k1 one))
        ((B2 k1) (idmap-get V (subterm _) k1 two))))))

(def-fns _ $ many idmap-set : (erased Type V) (subterm many (Bin) k) (many V v) (many (IdMap V) m) -> (many (IdMap V) r)
  (let (many here) (many one) (many two)
    (match many m (((Maybe V) h) ((IdMap V) o) ((IdMap V) t))
      ((MEmpty a) (values (None V) (MEmpty V) (MEmpty V)))
      ((MNode a h o t) (values h o t))))
  (match many k _
    ((BZ) (MNode V (Some V v) one two))
    ((B1 k1) (MNode V here (idmap-set V (subterm _) k1 v one) two))
    ((B2 k1) (MNode V here one (idmap-set V (subterm _) k1 v two)))))

(def-fns _ $ many idmap-mem : (erased Type V) (many (Bin) k) (many (IdMap V) m) -> (many (Bool) r)
  (match many (idmap-get (predates _) V k m) _ ((None a) (BFalse)) ((Some a v) (BTrue))))

; ---- NameMap: a persistent trie keyed by a string's characters

(def-adts
  (NameMap : (Type V) -> Type
    enum
    (many NMNode : (erased Type V) (many (Maybe V) here) (many (List (NMKid V)) kids) -> (NameMap V)))
  (NMKid : (Type V) -> Type
    enum
    (many MkKid : (erased Type V) (many (Char) c) (many (NameMap V) sub) -> (NMKid V))))

(def-fns _ $ many nm-empty : (erased Type V) -> (many (NameMap V) m)
  (NMNode V (None V) (Nil (NMKid V))))

(def-fns _ $ many nm-kid : (erased Type V) (subterm many (List (NMKid V)) kids) (many (Char) c) -> (many (Maybe (NameMap V)) r)
  (match many kids _
    ((Nil a) (None (NameMap V)))
    ((Cons a k rest)
      (match many k _
        ((MkKid b c1 sub)
          (match many (char-eq (predates _) c c1) _
            ((BTrue) (Some (NameMap V) sub))
            ((BFalse) (nm-kid V (subterm _) rest c))))))))

(def-fns _ $ many nm-get : (erased Type V) (subterm many (String) name) (many (NameMap V) m) -> (many (Maybe V) r)
  (match many m _
    ((NMNode a here kids)
      (match many name _
        ((SNil) here)
        ((SCons c rest)
          (match many (nm-kid (predates _) V kids c) _
            ((None b) (None V))
            ((Some b sub) (nm-get V (subterm _) rest sub))))))))

(def-fns _ $ many nm-replace-kid : (erased Type V) (subterm many (List (NMKid V)) kids) (many (Char) c) (many (NameMap V) sub) -> (many (List (NMKid V)) r)
  (match many kids _
    ((Nil a) (Cons (NMKid V) (MkKid V c sub) (Nil (NMKid V))))
    ((Cons a k rest)
      (match many k _
        ((MkKid b c1 old)
          (match many (char-eq (predates _) c c1) _
            ((BTrue) (Cons (NMKid V) (MkKid V c sub) rest))
            ((BFalse) (Cons (NMKid V) k (nm-replace-kid V (subterm _) rest c sub)))))))))

(def-fns _ $ many nm-set : (erased Type V) (subterm many (String) name) (many V v) (many (NameMap V) m) -> (many (NameMap V) r)
  (match many m _
    ((NMNode a here kids)
      (match many name _
        ((SNil) (NMNode V (Some V v) kids))
        ((SCons c rest)
          (let (many sub) (match many (nm-kid (predates _) V kids c) (((NameMap V) s))
                            ((None b) (nm-empty (predates _) V))
                            ((Some b s) s)))
          (NMNode V here (nm-replace-kid (predates _) V kids c (nm-set V (subterm _) rest v sub))))))))

; ---- Lists

(def-fns _ $ many list-length : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n)
  (match many xs _
    ((Nil a) (Zero))
    ((Cons a x rest) (Succ (list-length A (subterm _) rest)))))

(def-fns _ $ many list-rev-onto : (erased Type A) (subterm many (List A) xs) (many (List A) acc) -> (many (List A) r)
  (match many xs _
    ((Nil a) acc)
    ((Cons a x rest) (list-rev-onto A (subterm _) rest (Cons A x acc)))))

(def-fns _ $ many list-rev : (erased Type A) (many (List A) xs) -> (many (List A) r)
  (list-rev-onto (predates _) A xs (Nil A)))

(def-fns _ $ many list-append : (erased Type A) (subterm many (List A) xs) (many (List A) ys) -> (many (List A) r)
  (match many xs _
    ((Nil a) ys)
    ((Cons a x rest) (Cons A x (list-append A (subterm _) rest ys)))))

(def-fns _ $ many list-nth : (erased Type A) (subterm many (List A) xs) (many (Nat) i) -> (many (Maybe A) r)
  (match many xs _
    ((Nil a) (None A))
    ((Cons a x rest)
      (match many i _
        ((Zero) (Some A x))
        ((Succ k) (list-nth A (subterm _) rest k))))))

(def-fns _ $ many list-is-empty : (erased Type A) (many (List A) xs) -> (many (Bool) r)
  (match many xs _ ((Nil a) (BTrue)) ((Cons a x rest) (BFalse))))

(def-fns _ $ many list-mem-bin : (subterm many (List (Bin)) xs) (many (Bin) x) -> (many (Bool) r)
  (match many xs _
    ((Nil a) (BFalse))
    ((Cons a y rest)
      (match many (bin-eq (predates _) x y) _
        ((BTrue) (BTrue))
        ((BFalse) (list-mem-bin (subterm _) rest x))))))

(def-fns _ $ many index-of-bin : (subterm many (List (Bin)) xs) (many (Bin) x) (many (Nat) i) -> (many (Maybe (Nat)) r)
  (match many xs _
    ((Nil a) (None (Nat)))
    ((Cons a y rest)
      (match many (bin-eq (predates _) x y) _
        ((BTrue) (Some (Nat) i))
        ((BFalse) (index-of-bin (subterm _) rest x (Succ i)))))))

; ---- Rope: output built as a tree of chunks, never by appending long strings

(def-adts $ Rope : -> Type
  enum
  (many REmpty : -> (Rope))
  (many RStr : (many (String) s) -> (Rope))
  (many RCat : (many (Rope) a) (many (Rope) b) -> (Rope)))

(def-fns _ $ many rcat : (many (Rope) a) (many (Rope) b) -> (many (Rope) r)
  (RCat a b))

(def-fns _ $ many rcat3 : (many (Rope) a) (many (Rope) b) (many (Rope) c) -> (many (Rope) r)
  (RCat a (RCat b c)))

(def-fns _ $ many rcat4 : (many (Rope) a) (many (Rope) b) (many (Rope) c) (many (Rope) d) -> (many (Rope) r)
  (RCat a (RCat b (RCat c d))))

(def-fns _ $ many rcat5 : (many (Rope) a) (many (Rope) b) (many (Rope) c) (many (Rope) d) (many (Rope) e) -> (many (Rope) r)
  (RCat a (RCat b (RCat c (RCat d e)))))

; Ropes joined by a separator.
(def-fns _ $ many rjoin : (subterm many (List (Rope)) rs) (many (String) sep) -> (many (Rope) r)
  (match many rs _
    ((Nil a) (REmpty))
    ((Cons a r rest)
      (match many rest _
        ((Nil b) r)
        ((Cons b r2 rest2) (RCat r (RCat (RStr sep) (rjoin (subterm _) rest sep))))))))

(def-fns _ $ many rlist : (subterm many (List (Rope)) rs) -> (many (Rope) r)
  (match many rs _
    ((Nil a) (REmpty))
    ((Cons a r rest) (RCat r (rlist (subterm _) rest)))))

;  A rope as one string, for short diagnostics only.
(def-fns _ $ many rope-str : (subterm many (Rope) r) -> (many (String) s)
  (match many r _
    ((REmpty) (SNil))
    ((RStr s) s)
    ((RCat a b) (str-append (predates _) (rope-str (subterm _) a) (rope-str (subterm _) b)))))

; Flattens a rope into an IO chain writing each chunk, ending in [next].
(def-fns _ $ many rope-io : (erased (Level) L) (subterm many (Rope) r) (many (IO L) next) -> (many (IO L) io)
  (match many r _
    ((REmpty) next)
    ((RStr s) (WriteOut L s next))
    ((RCat a b) (rope-io L (subterm _) a (rope-io L (subterm _) b next)))))
