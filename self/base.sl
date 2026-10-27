; self/base.sl -- foundations for the self-hosted compiler (self/README.md): booleans, orders and
; their decisions, Nat/Char/String helpers over the prelude's externs, Nat identifiers and a trie map over them, a
; trie map keyed by names, list helpers and a rope of output chunks. Everything here is plain Sleight checked
; by the reference interpreter; nothing is settled design.

(def-fns _ $ (many not : (many (Bool) b) -> (many (Bool) r))
  (match many b _ ((BTrue) (BFalse)) ((BFalse) (BTrue))))

; ---- Nat

(def-fns _ $ (many cmp-index : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b) (many (Cmp T R a b) c) -> (many (Nat) i))
  (match many c _ ((CLt _ _ _ _ _) 0) ((CEq _ _ _) 1) ((CGt _ _ _ _ _) 2)))

(def-fns _ $ (many cmp-is-lt : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b) (many (Cmp T R a b) c) -> (many (Bool) r))
  (match many c _ ((CLt _ _ _ _ _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many nat-lt : (many (Nat) a) (many (Nat) b) -> (many (Bool) r))
  (cmp-is-lt _ _ _ _ $ nat-cmp a b))

(def-fns _ $ (many is-same : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b) (many (EqDec T R a b) e) -> (many (Bool) r))
  (match many e _ ((Equal _ _ _) (BTrue)) ((Unequal _ _ _ _ _) (BFalse))))

(def-fns _ $ (many nat-eqb : (many (Nat) a) (many (Nat) b) -> (many (Bool) r))
  (is-same _ _ _ _ $ nat-eq a b))

(def-fns _ $ (many nat-pred : (many (Nat) n) -> (many (Nat) m))
  (match many n _ ((Zero) (Zero)) ((Succ k) k)))

(def-fns _ $ (many nat-sub : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (let-match many (lt-dec b (Succ a)) (Yes _ _ _ _ le)
    ((No _ _ _ _ _) (Zero)))
  (let ((many c) (erased _)) (sub a b le))
  c)

(def-fns _ $ (many nat-is-zero : (many (Nat) n) -> (many (Bool) r))
  (match many n _ ((Zero) (BTrue)) ((Succ _) (BFalse))))

; ---- Char and String

(def-fns _ $ (many char-code : (many (Char) c) -> (many (Nat) n))
  (let-match many c (MkChar u))
  (let-match many u (MkU8 k _))
  k)

(def-fns _ $ (many char-eqb : (many (Char) a) (many (Char) b) -> (many (Bool) r))
  (is-same _ _ _ _ $ char-eq a b))

; code in [lo, hi]
(def-fns _ $ (many char-between : (many (Char) c) (many (Char) lo) (many (Char) hi) -> (many (Bool) r))
  (let-match many (char-lt-dec c lo) (No _ _ _ _ _) ((Yes _ _ _ _ _) (BFalse)))
  (match many (char-lt-dec hi c) _ ((Yes _ _ _ _ _) (BFalse)) ((No _ _ _ _ _) (BTrue))))

(def-fns _ $ (erased u8-u62 : (erased (Nat) k) (erased (Lt k u8-modulus) p) -> (erased (Lt k u62-modulus) q))
  (lt-trans _ _ _ p u8-below-u62))

(def-fns _ $ (many char-minus : (many (Char) a) (many (Char) b) -> (many (Nat) d) (erased (Lt d u62-modulus) pd))
  (let-match many a (MkChar ua))
  (let-match many ua (MkU8 ka pa))
  (let-match many b (MkChar ub))
  (let-match many ub (MkU8 kb pb))
  (let-match many (u62-lt-dec ka kb (u8-u62 _ pa) (u8-u62 _ pb)) (No _ _ _ _ le) ((Yes _ _ _ _ _) (values (Zero) u62-modulus-pos)))
  (let ((many d) (erased _) (erased pd)) (u62-sub ka kb (u8-u62 _ pa) (le-lt-succ _ _ le)))
  (values d pd))

(def-fns _ $ (many rope-str at flatten : (many (Rope) r) -> (many (String) s))
  (let ((many s) (erased _)) (delegate (flatten r)))
  s)

(def-fns _ $ (many str-eqb : (many (String) a) (many (String) b) -> (many (Bool) r))
  (is-same _ _ _ _ $ str-eq a b))

(def-fns _ $ (many str-is-empty : (many (String) s) -> (many (Bool) r))
  (match many s _ ((SNil) (BTrue)) ((SCons _ _) (BFalse))))

(def-fns _ $ (many str-cat : (many (String) a) (many (String) b) -> (many (String) c))
  (str-append a b))

(def-fns _ $ (many str-cat3 : (many (String) a) (many (String) b) (many (String) c) -> (many (String) d))
  (str-append a $ str-append b c))

(def-fns _ $ (many str-starts : (subterm many (String) p) (many (String) s) -> (many (Bool) r))
  (let-match many p (SCons c prest) ((SNil) (BTrue)))
  (let-match many s (SCons d srest) ((SNil) (BFalse)))
  (match many (char-eqb d c) _ ((BTrue) (tail $ str-starts prest srest)) ((BFalse) (BFalse))))

(def-fns _ $ (many str-contains : (subterm many (String) s) (many (String) p) -> (many (Bool) r))
  (let-match many (str-starts p s) (BFalse) ((BTrue) (BTrue)))
  (let-match many s (SCons _ rest) ((SNil) (BFalse)))
  (tail $ str-contains rest p))

(def-fns _ $ (many str-until-onto : (many (Rope) acc) (subterm many (String) s) (many (Char) code) -> (many (String) before) (many (Maybe $ String) after))
  (let-match many s (SCons c rest) ((SNil) (values (rope-str acc) (None _))))
  (match many (char-eqb c code) _
    ((BTrue) (values (rope-str acc) (Some _ rest)))
    ((BFalse) (tail (str-until-onto (RCat acc $ RChar c) rest code)))))

(def-fns _ $ (many str-until : (many (String) s) (many (Char) code) -> (many (String) before) (many (Maybe $ String) after))
  (str-until-onto (REmpty) s code))

(def-fns _ $ (many str-split-fuel : (subterm many (Nat) fuel) (many (String) s) (many (Char) code) -> (many (List $ String) r))
  (let ((many b) (many a)) (str-until s code))
  (let-match many a (Some _ rest) ((None _) (Cons _ b $ Nil _)))
  (match many fuel _
    ((Zero) (Cons _ b $ Nil _))
    ((Succ f) (Cons _ b $ notail $ str-split-fuel f rest code))))

(def-fns _ $ (many split-on : (many (String) s) (many (Char) code) -> (many (List $ String) r))
  (let ((many n) (erased _)) (str-length s))
  (str-split-fuel n s code))

(def-fns _ $ (many nat-list-eq : (subterm many (List $ Nat) a) (many (List $ Nat) b) -> (many (Bool) r))
  (match many a _
    ((Nil _) (match many b _ ((Nil _) (BTrue)) ((Cons _ _ _) (BFalse))))
    ((Cons _ x rest) (match many b _ ((Nil _) (BFalse)) ((Cons _ y rest2) (and (nat-eqb x y) $ tail $ nat-list-eq rest rest2))))))

; A shape as the FFI's error messages spell it, its arities separated by spaces.
(def-fns _ $ (many spell-nats : (subterm many (List $ Nat) ns) -> (many (String) s))
  (let-match many ns (Cons _ n rest) ((Nil _) ""))
  (match many rest _
    ((Nil _) (nat-str n))
    ((Cons _ _ _) (str-cat3 (nat-str n) " " $ notail $ spell-nats rest))))

(def-fns _ $ (many all-digits : (subterm many (String) s) -> (many (Bool) r))
  (match many s _
    ((SNil) (BTrue))
    ((SCons c rest) (and (char-between c #\0 #\9) $ tail $ all-digits rest))))

; A numeral or a #\c character literal, which no name may spell (section 1, ASSUMPTIONS 51).
(def-fns _ $ (many is-literal-name : (many (String) s) -> (many (Bool) r))
  (let-match many s (SCons c rest) ((SNil) (BFalse)))
  (or (all-digits s)
    $ and (char-eqb c #\#) $ match many rest (((Bool) _)) ((SNil) (BFalse)) ((SCons c2 _) (char-eqb c2 #\\))))

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
  (match many (and (char-eqb c #\#) $ match many rest (((Bool) _)) ((SNil) (BFalse)) ((SCons c2 _) (char-eqb c2 #\\))) _
    ((BTrue) (LChar))
    ((BFalse) (LName))))

(def-fns _ $ (many parse-nat : (many (String) s) -> (many (Nat) n))
  (match many (str-nat s) _ ((Some _ n) n) ((None _) 0)))

(def-fns _ $ (many is-hex : (many (Char) c) -> (many (Bool) r))
  (or (char-between c #\0 #\9) $ or (char-between c #\a #\f) $ char-between c #\A #\F))

(let ((many sixteen-dec)) (lt-dec (Zero) 16))
(comptime-match many sixteen-dec (Yes _ _ sda sdb sixteen-positive))
(let ((many m256) (erased sixteen-squared)) (mul 16 16))
(comptime-match many (nat-eq m256 u8-modulus) (Equal _ _ _))
(let ((many s16) (erased ten-six)) (add 10 6))
(comptime-match many (nat-eq s16 16) (Equal _ _ _))

(def-fns _ $ (erased add-lt-mono : (erased (Nat) a x y s t) (subterm erased (Add a x s) p) (erased (Add a y t) q) (erased (Lt x y) l) -> (erased (Lt s t) r))
  (match erased p _
    ((AddZero _) (let-match erased q (AddZero _)) l)
    ((AddSucc a1 _ s1 p1)
      (let-match erased q (AddSucc _ _ t1 q1))
      (LtS s1 t1 (add-lt-mono a1 x y s1 t1 p1 q1 l)))))

(def-fns _ $ (erased mul-le-mono : (erased (Nat) c q m x y) (erased (Lt c (Succ q)) l) (subterm erased (Mul c m x) p) (erased (Mul q m y) r) -> (erased (Lt x (Succ y)) o))
  (let-match erased p (MulSucc c1 _ x1 _ p1 ax) ((MulZero _) (LtZ y)))
  (let-match erased l (LtS _ _ l1))
  (let-match erased r (MulSucc q1 _ y1 _ r1 ay) (absurd (MulZero _) l1))
  (add-lt-mono m x1 (Succ y1) x (Succ y) (add-comm _ _ _ ax) (add-succ-right _ _ _ (add-comm _ _ _ ay)) (mul-le-mono c1 q1 m x1 y1 l1 p1 r1)))

(def-fns _ $ (erased div-small : (erased (Nat) q c m r n s) (erased (Mul q c m) mm) (erased (Add m r n) ad) (erased (Lt n s) ns) (erased (Mul c c s) cc) -> (erased (Lt q c) l))
  (let-match erased (lt-dec q c) (Yes _ _ _ _ l)
    (absurd (No _ _ _ _ ge) (lt-asym n m (lt-le-trans n s m ns (mul-le-mono c q c s m (le-lt-succ _ _ ge) cc mm)) (add-le-left m r n ad))))
  l)

(def-fns _ $ (erased digits-byte : (erased (Nat) a b x v) (erased (Lt a 16) pa) (erased (Lt b 16) pb) (erased (Mul a 16 x) mx) (erased (Add x b v) av) -> (erased (Lt v u8-modulus) l))
  (let ((erased x2) (erased a16)) (add x 16))
  (lt-le-trans v x2 u8-modulus (add-lt-mono x b 16 v x2 av a16 pb)
    (mul-le-mono (Succ a) 16 16 x2 u8-modulus (LtS a 16 pa) (MulSucc a 16 x x2 mx a16) sixteen-squared)))

(def-adts $ (Nibble : -> Type)
  enum newtype
  (many MkNibble : (many (Nat) n) (erased (Lt n 16) p) -> (Nibble)))

(def-fns _ $ (many range-digit : (many (Nat) k) (erased (Lt k u62-modulus) pk) (many (Nat) lo) (erased (Lt lo u62-modulus) plo)
    (many (Nat) width) (erased (Lt width u62-modulus) pw) (many (Nat) off) (erased (Nat) top) (erased (Add off width top) aw) (erased (Lt top (Succ 16)) ptop)
    -> (many (Maybe $ Nibble) r))
  (let-match many (u62-lt-dec k lo pk plo) (No _ _ _ _ ge) ((Yes _ _ _ _ _) (None _)))
  (let ((many x) (erased _) (erased px)) (u62-sub k lo pk (le-lt-succ _ _ ge)))
  (let-match many (u62-lt-dec x width px pw) (Yes _ _ _ _ xw) ((No _ _ _ _ _) (None _)))
  (let ((many d) (erased ad)) (add off x))
  (Some _ $ MkNibble d (lt-le-trans d top 16 (add-lt-mono off x width d top ad aw xw) ptop)))

(let ((erased b48)) (u8-u62 _ (prove-literal-lt 48 u8-modulus)))
(let ((erased b97)) (u8-u62 _ (prove-literal-lt 97 u8-modulus)))
(let ((erased b65)) (u8-u62 _ (prove-literal-lt 65 u8-modulus)))
(let ((erased b10)) (u8-u62 _ (prove-literal-lt 10 u8-modulus)))
(let ((erased b6)) (u8-u62 _ (prove-literal-lt 6 u8-modulus)))
(let ((erased ten-top)) (lt-weaken _ _ (prove-literal-lt 10 16)))

(def-fns _ $ (many hex-digit : (many (Char) c) -> (many (Nibble) d))
  (let-match many c (MkChar u))
  (let-match many u (MkU8 k q))
  (let ((erased pk)) (u8-u62 _ q))
  (let-match many (range-digit k pk 48 b48 10 b10 (Zero) _ (AddZero 10) ten-top) (None _) ((Some _ d) d))
  (let-match many (range-digit k pk 97 b97 6 b6 10 _ ten-six (lt-succ 16)) (None _) ((Some _ d) d))
  (match many (range-digit k pk 65 b65 6 b6 10 _ ten-six (lt-succ 16)) _ ((Some _ d) d) ((None _) (MkNibble (Zero) sixteen-positive))))

(def-fns _ $ (many byte-of-nibbles : (many (Nibble) hi) (many (Nibble) lo) -> (many (Char) c))
  (let-match many hi (MkNibble a pa))
  (let-match many lo (MkNibble b pb))
  (let ((many x) (erased mx)) (mul a 16))
  (let ((many v) (erased av)) (add x b))
  (MkChar $ MkU8 v (digits-byte a b x v pa pb mx av)))

(def-fns _ $ (many char-lit-body : (many (String) s) -> (many (String) body))
  (let-match many s (SCons _ rest) ((SNil) (SNil)))
  (match many rest _ ((SNil) (SNil)) ((SCons _ rest2) rest2)))

; The character #\c, #\space, #\newline, #\tab or #\xHH spells, or None where the literal is malformed.
(def-fns _ $ (many char-lit-code : (many (String) s) -> (many (Maybe $ Char) n))
  (let ((many body)) $ char-lit-body s)
  (match many (str-cmp body "space") _
    ((CEq _ _ _) (Some _ #\space))
    (else
      (match many (str-cmp body "newline") _
        ((CEq _ _ _) (Some _ #\newline))
        (else
          (match many (str-cmp body "tab") _
            ((CEq _ _ _) (Some _ #\tab))
            (else
              (let-match many body (SCons c rest) ((SNil) (None _)))
              (let-match many rest (SCons h1 rest2) ((SNil) (Some _ c)))
              (let-match many rest2 (SCons h2 rest3) ((SNil) (None _)))
              (match many (and (char-eqb c #\x) $ and (is-hex h1) $ and (is-hex h2) $ str-is-empty rest3) _
                ((BTrue) (Some _ $ byte-of-nibbles (hex-digit h1) (hex-digit h2)))
                ((BFalse) (None _))))))))))

; What is wrong with a literal's spelling, if anything (lib/literal.ml's classify).
(def-fns _ $ (many literal-error : (many (String) s) -> (many (Maybe $ String) r))
  (match many (classify s) _
    ((LName) (None _))
    ((LNumeral)
      (let-match many s (SCons c rest) ((SNil) (None _)))
      (match many (and (char-eqb c #\0) $ not $ str-is-empty rest) _
        ((BTrue) (Some _ $ str-cat s " has a leading zero"))
        ((BFalse) (None _))))
    ((LChar)
      (match many (char-lit-code s) _
        ((Some _ _) (None _))
        ((None _) (Some _ $ str-cat "malformed character literal " s))))))

; An Sleight name as an OCaml identifier fragment: letters and digits kept, anything else an underscore.
(def-fns _ $ (many sanitize-char : (many (Char) c) -> (many (Char) r))
  (let ((many ok)) (or (char-between c #\0 #\9)
                    $ or (char-between c #\A #\Z) $ char-between c #\a #\z))
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

(def-fns _ $ (erased append-nil-right : (subterm erased (String) s) -> (erased (Append s (SNil) s) p))
  (match erased s _
    ((SNil) (AppNil (SNil)))
    ((SCons c t) (AppCons c t (SNil) t (append-nil-right t)))))

(def-fns _ $ (erased append-unique : (erased (String) a b t u s) (erased (Nat) i)
    (subterm erased (Append a t s) p) (erased (StrLength a i) la) (erased (Append b u s) q) (erased (StrLength b i) lb) ->
    (erased (Eq (String) t u) e))
  (match erased p _
    ((AppNil _)
      (let-match erased la (SLenNil))
      (let-match erased lb (SLenNil))
      (let-match erased q (AppNil _))
      (Refl _ t))
    ((AppCons _ a1 _ s1 p1)
      (let-match erased la (SLenCons _ _ i1 la1))
      (let-match erased lb (SLenCons _ b1 _ lb1))
      (let-match erased q (AppCons _ _ _ _ q1))
      (append-unique a1 b1 t u s1 i1 p1 la1 q1 lb1))))

(def-fns _ $ (erased append-snoc : (erased (String) a t s) (erased (Char) c) (erased (Nat) i)
    (subterm erased (Append a (SCons c t) s) p) (erased (StrLength a i) la) ->
    (erased (String) a2) (erased (Append a2 t s) q) (erased (StrLength a2 (Succ i)) la2))
  (match erased p _
    ((AppNil _)
      (let-match erased la (SLenNil))
      (values (SCons c (SNil)) (AppCons c (SNil) t t (AppNil t)) (SLenCons c (SNil) (Zero) (SLenNil))))
    ((AppCons d a1 _ s1 p1)
      (let-match erased la (SLenCons _ _ i1 la1))
      (let ((erased a3) (erased q1) (erased l1)) (append-snoc a1 t s1 c i1 p1 la1))
      (values (SCons d a3) (AppCons d a3 t s1 q1) (SLenCons d a3 (Succ i1) l1)))))

(def-fns _ $ (erased prefix-lt : (erased (String) a t s) (erased (Nat) i len)
    (subterm erased (Append a t s) p) (erased (StrLength a i) la) (erased (StrLength s len) ls) ->
    (erased (Lt i (Succ len)) lt))
  (match erased p _
    ((AppNil _) (let-match erased la (SLenNil)) (LtZ len))
    ((AppCons _ a1 _ s1 p1)
      (let-match erased la (SLenCons _ _ i1 la1))
      (let-match erased ls (SLenCons _ _ len1 ls1))
      (LtS i1 (Succ len1) (prefix-lt a1 t s1 i1 len1 p1 la1 ls1)))))

(def-fns _ $ (many common-prefix : (erased (String) s) (subterm many (String) a) (many (String) b) (many (Nat) k)
    (erased (String) p) (erased (Append p a s) ap) (erased (StrLength p k) lp) ->
    (many (Nat) n) (many (String) a2) (many (String) b2) (erased (String) q) (erased (Append q a2 s) aq) (erased (StrLength q n) lq))
  (let-match many a (SCons c a1) ((SNil) (values k a b p ap lp)))
  (let-match many b (SCons d b1) ((SNil) (values k a b p ap lp)))
  (let-match many (char-eq c d) (Equal _ _ _) ((Unequal _ _ _ _ _) (values k a b p ap lp)))
  (let ((erased p2) (erased ap2) (erased lp2)) (append-snoc p a1 s c k ap lp))
  (tail $ common-prefix s a1 b1 (Succ k) p2 ap2 lp2))

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

(def-fns _ $ (many list-pop : (erased Type A) (many (List A) xs) (many A dflt) -> (many A x) (many (List A) rest))
  (match many xs _ ((Cons _ x rest) (values x rest)) ((Nil _) (values dflt $ Nil _))))

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
  (match many (str-eqb x y) _ ((BTrue) (BTrue)) ((BFalse) (tail $ list-mem-str rest x))))

(def-fns _ $ (many index-of-bin : (subterm many (List $ Nat) xs) (many (Nat) x) (many (Nat) i) -> (many (Maybe $ Nat) r))
  (let-match many xs (Cons _ y rest) ((Nil _) (None _)))
  (match many (nat-eqb x y) _
    ((BTrue) (Some _ i))
    ((BFalse) (tail $ index-of-bin rest x $ Succ i))))

(def-fns _ $ (many list-mem-bin : (subterm many (List $ Nat) xs) (many (Nat) x) -> (many (Bool) r))
  (let-match many xs (Cons _ y rest) ((Nil _) (BFalse)))
  (match many (nat-eqb x y) _ ((BTrue) (BTrue)) ((BFalse) (tail $ list-mem-bin rest x))))

(def-fns _ $ (many join-strs : (subterm many (List $ String) xs) (many (String) sep) -> (many (String) r))
  (let-match many xs (Cons _ x rest)
    ((Nil _) ""))
  (match many rest _ ((Nil _) x) ((Cons _ _ _) (str-cat3 x sep $ notail $ join-strs rest sep))))

(def-fns _ $ (many nat-min : (many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (match many (nat-lt a b) _ ((BTrue) a) ((BFalse) b)))

(let ((erased thirty-two-u62)) (u8-u62 _ (prove-literal-lt 32 u8-modulus)))

(def-fns _ $ (many case-pair : (many (Char) upper) (many (Char) lower) -> (many (Bool) r))
  (let-match many (char-between upper #\A #\Z) (BTrue) ((BFalse) (BFalse)))
  (let ((many d) (erased pd)) (char-minus lower upper))
  (is-same _ _ _ _ $ u62-eq d 32 pd thirty-two-u62))

(def-fns _ $ (many char-eq-nocase : (many (Char) a) (many (Char) b) -> (many (Bool) r))
  (or (char-eqb a b) $ or (case-pair a b) $ case-pair b a))

(def-fns _ $ (many distance-first-row : (subterm many (String) bs) (many (Nat) j) (many (List $ Nat) acc) -> (many (List $ Nat) r))
  (let-match many bs (SCons _ rest) ((SNil) (list-rev _ $ Cons _ j acc)))
  (tail $ distance-first-row rest (Succ j) $ Cons _ j acc))

(def-fns _ $ (many distance-swap : (many (Char) c) (many (Maybe $ Char) cp) (many (Char) bc) (many (Maybe $ Char) bp) (many (List $ Nat) up2) -> (many (Maybe $ Nat) r))
  (let-match many cp (Some _ ap) ((None _) (None _)))
  (let-match many bp (Some _ bq) ((None _) (None _)))
  (let-match many up2 (Cons _ q _) ((Nil _) (None _)))
  (match many (and (char-eq-nocase c bq) $ char-eq-nocase ap bc) _ ((BTrue) (Some _ q)) ((BFalse) (None _))))

(def-fns _ $ (many distance-row : (many (Char) c) (many (Maybe $ Char) cp) (subterm many (String) bs) (many (Maybe $ Char) bp)
    (many (List $ Nat) up) (many (List $ Nat) up2) (many (Nat) left) (many (List $ Nat) acc) -> (many (List $ Nat) r))
  (let-match many bs (SCons bc rest) ((SNil) (list-rev _ acc)))
  (let-match many up (Cons _ diag up-rest) ((Nil _) (list-rev _ acc)))
  (let-match many up-rest (Cons _ above _) ((Nil _) (list-rev _ acc)))
  (let ((many best)) (nat-min (Succ $ nat-min above left) $ match many (char-eq-nocase c bc) (((Nat) _)) ((BTrue) diag) ((BFalse) (Succ diag))))
  (let ((many here)) (match many (distance-swap c cp bc bp up2) (((Nat) _)) ((Some _ q) (nat-min best $ Succ q)) ((None _) best)))
  (let ((many up2-next)) (match many bp (((List $ Nat) _)) ((None _) up2) ((Some _ _) (match many up2 (((List $ Nat) _)) ((Nil _) up2) ((Cons _ _ r2) r2)))))
  (tail $ distance-row c cp rest (Some _ bc) up-rest up2-next here $ Cons _ here acc))

(def-fns _ $ (many distance-rows : (subterm many (String) xs) (many (Maybe $ Char) cp) (many (String) b) (many (Nat) i) (many (List $ Nat) up) (many (List $ Nat) up2) -> (many (List $ Nat) r))
  (let-match many xs (SCons c rest) ((SNil) up))
  (let ((many row)) (distance-row c cp b (None _) up up2 (Succ i) $ Cons _ (Succ i) $ Nil _))
  (tail $ distance-rows rest (Some _ c) b (Succ i) row up))

(def-fns _ $ (many distance : (many (String) a) (many (String) b) -> (many (Nat) d))
  (let ((many first)) (distance-first-row b 0 $ Nil _))
  (let-match many (list-rev _ $ distance-rows a (None _) b 0 first first) (Cons _ d _) ((Nil _) 0))
  d)

; ---- WordMap: a persistent radix trie over keys of a type K, each key spelling a word over symbols S;
; an edge is its first symbol and the rest of its label

(def-adts
  ((ListLt : (Type S) ((TyCtor (S x) (S y) -> Type) R) ((List S) a) ((List S) b) -> Type)
    enum
    (many LLNil : (erased Type S) (erased (TyCtor (S x) (S y) -> Type) R) (erased S d) (erased (List S) t) -> (ListLt S R (Nil S) (Cons S d t)))
    (many LLHead : (erased Type S) (erased (TyCtor (S x) (S y) -> Type) R) (erased S c) (erased S d) (erased (List S) s) (erased (List S) t) (erased (R c d) p)
       -> (ListLt S R (Cons S c s) (Cons S d t)))
    (many LLTail : (erased Type S) (erased (TyCtor (S x) (S y) -> Type) R) (erased S c) (erased (List S) s) (erased (List S) t) (erased (ListLt S R s t) p)
       -> (ListLt S R (Cons S c s) (Cons S c t))))
  ((WordApart : (Type S) ((TyCtor (S x) (S y) -> Type) R) ((List S) a) ((List S) b) -> Type)
    enum
    (many WALt : (erased Type S) (erased (TyCtor (S x) (S y) -> Type) R) (erased (List S) a) (erased (List S) b) (erased (ListLt S R a b) p) -> (WordApart S R a b))
    (many WAGt : (erased Type S) (erased (TyCtor (S x) (S y) -> Type) R) (erased (List S) a) (erased (List S) b) (erased (ListLt S R b a) p) -> (WordApart S R a b)))
  ((WordEq : (Type S) ((TyCtor (S x) (S y) -> Type) R) ((List S) a) ((List S) b) -> Type)
    enum
    (many WESame : (erased Type S) (erased (TyCtor (S x) (S y) -> Type) R) (erased (List S) a) -> (WordEq S R a a))
    (many WEApart : (erased Type S) (erased (TyCtor (S x) (S y) -> Type) R) (erased (List S) a) (erased (List S) b) (erased (WordApart S R a b) d) -> (WordEq S R a b))))

(def-adts
  ((WordMap : (Type K) (Type S) (Type V) -> Type)
    enum
    (many WMNode : (erased Type K) (erased Type S) (erased Type V) (many (Maybe V) here) (many (List $ WMKid K S V) kids) -> (WordMap K S V)))
  ((WMKid : (Type K) (Type S) (Type V) -> Type)
    enum
    (many MkWMKid : (erased Type K) (erased Type S) (erased Type V) (many S c) (many K lab) (many (WordMap K S V) submap) -> (WMKid K S V))))

(def-adts
  ((KView : (Type K) (Type S) ((TyCtor (K k) ((List S) w) -> Type) Sp) (K k) ((List S) w) -> Type)
    enum
    (many KEnd : (erased Type K) (erased Type S) (erased (TyCtor (K k) ((List S) w) -> Type) Sp) (erased K k) -> (KView K S Sp k (Nil S)))
    (many KNext : (erased Type K) (erased Type S) (erased (TyCtor (K k) ((List S) w) -> Type) Sp) (erased K k)
       (many S c) (many K rest) (erased (List S) rw) (erased (Sp rest rw) p) -> (KView K S Sp k (Cons S c rw)))))

(def-adts $ (KeyOps : ((Level) M) (Type K) (Type S) ((TyCtor (K k) ((List S) w) -> Type) Sp) ((TyCtor (S x) (S y) -> Type) R) -> Type)
  enum
  (many MkKeyOps : (erased (Level) M) (erased Type K) (erased Type S) (erased (TyCtor (K k) ((List S) w) -> Type) Sp) (erased (TyCtor (S x) (S y) -> Type) R)
    (erased (Fn M (erased K k) -> (erased (List S) w) (erased (Sp k w) p)) kword)
    (many (Fn M (many K k) (erased (List S) w) (erased (Sp k w) p) -> (many (KView K S Sp k w) v)) kview)
    (many (Fn M (many K k) (erased (List S) w) (erased (Sp k w) p) -> (many (Nat) n) (erased (Length S w n) l)) klen)
    (many (Fn M (many K k) (erased (List S) w) (erased (Sp k w) p) (many (Nat) n) (erased (Nat) len) (erased (Length S w len) l) (erased (Lt n (Succ len)) le) ->
        (many K a) (many K b) (erased (List S) wa) (erased (List S) wb) (erased (Sp a wa) pa) (erased (Sp b wb) pb) (erased (Concat S wa wb w) c) (erased (Length S wa n) la)) ksplit)
    (many (Fn M (many K a) (erased (List S) wa) (erased (Sp a wa) pa) (many K b) (erased (List S) wb) (erased (Sp b wb) pb) ->
        (many (WordEq S R wa wb) e)) keq)
    (many (Fn M (many K a) (many K b) -> (many K common) (many K ra) (many K rb)) kdiverge)
    (many (Fn M (many S a) (many S b) -> (many (Cmp S R a b) c)) scmp)
    -> (KeyOps M K S Sp R)))
; A lookup's evidence: an edge for each step, its label's word a prefix of the key's, then the value; or no edge
; for some symbol, a label the word does not start with, or an empty slot.
(def-adts
  ((WKidIs : (Type K) (Type S) (Type V) (S c) (K lab) ((WordMap K S V) submap) ((List $ WMKid K S V) kids) -> Type)
    enum
    (many WKHere : (erased Type K) (erased Type S) (erased Type V) (erased S c) (erased K lab) (erased (WordMap K S V) submap) (erased (List $ WMKid K S V) rest)
       -> (WKidIs K S V c lab submap $ Cons (WMKid K S V) (MkWMKid K S V c lab submap) rest))
    (many WKThere : (erased Type K) (erased Type S) (erased Type V) (erased S c) (erased K lab) (erased (WordMap K S V) submap) (erased (WMKid K S V) k) (erased (List $ WMKid K S V) rest)
       (erased (WKidIs K S V c lab submap rest) p) -> (WKidIs K S V c lab submap $ Cons (WMKid K S V) k rest)))
  ((WNoKid : (Type K) (Type S) (Type V) ((TyCtor (S x) (S y) -> Type) R) (S c) ((List $ WMKid K S V) kids) -> Type)
    enum
    (many WNKNil : (erased Type K) (erased Type S) (erased Type V) (erased (TyCtor (S x) (S y) -> Type) R) (erased S c) -> (WNoKid K S V R c $ Nil $ WMKid K S V))
    (many WNKLt : (erased Type K) (erased Type S) (erased Type V) (erased (TyCtor (S x) (S y) -> Type) R) (erased S c) (erased S d) (erased K lab) (erased (WordMap K S V) submap)
       (erased (List $ WMKid K S V) rest) (erased (R c d) lt) (erased (WNoKid K S V R c rest) p) -> (WNoKid K S V R c $ Cons (WMKid K S V) (MkWMKid K S V d lab submap) rest))
    (many WNKGt : (erased Type K) (erased Type S) (erased Type V) (erased (TyCtor (S x) (S y) -> Type) R) (erased S c) (erased S d) (erased K lab) (erased (WordMap K S V) submap)
       (erased (List $ WMKid K S V) rest) (erased (R d c) gt) (erased (WNoKid K S V R c rest) p) -> (WNoKid K S V R c $ Cons (WMKid K S V) (MkWMKid K S V d lab submap) rest)))
  ((WKidLookup : (Type K) (Type S) (Type V) ((TyCtor (S x) (S y) -> Type) R) (S c) ((List $ WMKid K S V) kids) -> Type)
    enum
    (many WKHit : (erased Type K) (erased Type S) (erased Type V) (erased (TyCtor (S x) (S y) -> Type) R) (erased S c) (erased (List $ WMKid K S V) kids) (many K lab) (many (WordMap K S V) submap)
       (erased (WKidIs K S V c lab submap kids) p) (erased (Subterm (WordMap K S V) submap (List $ WMKid K S V) kids) st) -> (WKidLookup K S V R c kids))
    (many WKMiss : (erased Type K) (erased Type S) (erased Type V) (erased (TyCtor (S x) (S y) -> Type) R) (erased S c) (erased (List $ WMKid K S V) kids)
       (erased (WNoKid K S V R c kids) p) -> (WKidLookup K S V R c kids)))
  ((WNotPrefix : (Type S) ((TyCtor (S x) (S y) -> Type) R) ((List S) lab) ((List S) name) -> Type)
    enum
    (many WNPShort : (erased Type S) (erased (TyCtor (S x) (S y) -> Type) R) (erased (List S) lab) (erased (List S) name) (erased (Nat) n) (erased (Nat) len)
       (erased (Length S name n) ln) (erased (Length S lab len) ll) (erased (Lt n len) lt) -> (WNotPrefix S R lab name))
    (many WNPDiff : (erased Type S) (erased (TyCtor (S x) (S y) -> Type) R) (erased (List S) lab) (erased (List S) name) (erased (List S) p) (erased (List S) r) (erased (Nat) len)
       (erased (Concat S p r name) ap) (erased (Length S p len) lp) (erased (Length S lab len) ll) (erased (WordApart S R p lab) d) -> (WNotPrefix S R lab name)))
  ((WMapsTo : (Type K) (Type S) ((TyCtor (K k) ((List S) w) -> Type) Sp) (Type V) ((List S) name) (V v) ((WordMap K S V) m) -> Type)
    enum
    (many WMHere : (erased Type K) (erased Type S) (erased (TyCtor (K k) ((List S) w) -> Type) Sp) (erased Type V) (erased V v) (erased (List $ WMKid K S V) kids)
       -> (WMapsTo K S Sp V (Nil S) v $ WMNode K S V (Some V v) kids))
    (many WMStep : (erased Type K) (erased Type S) (erased (TyCtor (K k) ((List S) w) -> Type) Sp) (erased Type V) (erased S c) (erased K lab) (erased (List S) lw)
       (erased (List S) name) (erased (List S) rest) (erased V v) (erased (Maybe V) here) (erased (List $ WMKid K S V) kids) (erased (WordMap K S V) submap)
       (erased (WKidIs K S V c lab submap kids) k) (erased (Sp lab lw) sl) (erased (Concat S lw rest name) ap) (erased (WMapsTo K S Sp V rest v submap) p)
       -> (WMapsTo K S Sp V (Cons S c name) v $ WMNode K S V here kids)))
  ((WAbsent : (Type K) (Type S) ((TyCtor (K k) ((List S) w) -> Type) Sp) ((TyCtor (S x) (S y) -> Type) R) (Type V) ((List S) name) ((WordMap K S V) m) -> Type)
    enum
    (many WAHere : (erased Type K) (erased Type S) (erased (TyCtor (K k) ((List S) w) -> Type) Sp) (erased (TyCtor (S x) (S y) -> Type) R) (erased Type V) (erased (List $ WMKid K S V) kids)
       -> (WAbsent K S Sp R V (Nil S) $ WMNode K S V (None V) kids))
    (many WANoKid : (erased Type K) (erased Type S) (erased (TyCtor (K k) ((List S) w) -> Type) Sp) (erased (TyCtor (S x) (S y) -> Type) R) (erased Type V)
       (erased S c) (erased (List S) rest) (erased (Maybe V) here) (erased (List $ WMKid K S V) kids) (erased (WNoKid K S V R c kids) n)
       -> (WAbsent K S Sp R V (Cons S c rest) $ WMNode K S V here kids))
    (many WADiverge : (erased Type K) (erased Type S) (erased (TyCtor (K k) ((List S) w) -> Type) Sp) (erased (TyCtor (S x) (S y) -> Type) R) (erased Type V)
       (erased S c) (erased K lab) (erased (List S) lw) (erased (List S) name) (erased (Maybe V) here) (erased (List $ WMKid K S V) kids) (erased (WordMap K S V) submap)
       (erased (WKidIs K S V c lab submap kids) k) (erased (Sp lab lw) sl) (erased (WNotPrefix S R lw name) np)
       -> (WAbsent K S Sp R V (Cons S c name) $ WMNode K S V here kids))
    (many WAStep : (erased Type K) (erased Type S) (erased (TyCtor (K k) ((List S) w) -> Type) Sp) (erased (TyCtor (S x) (S y) -> Type) R) (erased Type V)
       (erased S c) (erased K lab) (erased (List S) lw) (erased (List S) name) (erased (List S) rest) (erased (Maybe V) here) (erased (List $ WMKid K S V) kids)
       (erased (WordMap K S V) submap) (erased (WKidIs K S V c lab submap kids) k) (erased (Sp lab lw) sl) (erased (Concat S lw rest name) ap) (erased (WAbsent K S Sp R V rest submap) p)
       -> (WAbsent K S Sp R V (Cons S c name) $ WMNode K S V here kids)))
  ((WLookup : (Type K) (Type S) ((TyCtor (K k) ((List S) w) -> Type) Sp) ((TyCtor (S x) (S y) -> Type) R) (Type V) ((List S) name) ((WordMap K S V) m) -> Type)
    enum
    (many WHit : (erased Type K) (erased Type S) (erased (TyCtor (K k) ((List S) w) -> Type) Sp) (erased (TyCtor (S x) (S y) -> Type) R) (erased Type V)
       (erased (List S) name) (erased (WordMap K S V) m) (many V v) (erased (WMapsTo K S Sp V name v m) p) -> (WLookup K S Sp R V name m))
    (many WMiss : (erased Type K) (erased Type S) (erased (TyCtor (K k) ((List S) w) -> Type) Sp) (erased (TyCtor (S x) (S y) -> Type) R) (erased Type V)
       (erased (List S) name) (erased (WordMap K S V) m) (erased (WAbsent K S Sp R V name m) p) -> (WLookup K S Sp R V name m))))

(def-fns _ $ (many wm-empty : (erased Type K) (erased Type S) (erased Type V) -> (many (WordMap K S V) m))
  (WMNode _ _ _ (None _) $ Nil _))
(def-fns _ $ (many word-map-factory : (erased (Level) M) (erased Type K) (erased Type S) (erased (TyCtor (K k) ((List S) w) -> Type) Sp) (erased (TyCtor (S x) (S y) -> Type) R)
    (many (KeyOps M K S Sp R) ops) ->
    (erased (Level) L)
    (many (Fn L (erased Type V) (many K k) (subterm many (WordMap K S V) m) -> (erased (List S) w) (erased (Sp k w) p) (many (WLookup K S Sp R V w m) r)) get)
    (many (Fn L (erased Type V) (many K k) (many V v) (subterm many (WordMap K S V) m) -> (many (WordMap K S V) r)) set))
  (let-match many ops (MkKeyOps _ _ _ _ _ kword kview klen ksplit keq kdiverge scmp))
  (def-fns _ $ (many kid : (erased Type V) (subterm many (List $ WMKid K S V) kids) (many S c) -> (many (WKidLookup K S V R c kids) r))
    (let-match many kids (Cons _ k rest) ((Nil _) (WKMiss _ _ _ _ _ _ $ WNKNil _ _ _ _ c)))
    (let-match many k (MkWMKid _ _ _ c1 lab3 sub3))
    (match many (scmp c c1) _
      ((CEq _ _ _) (WKHit _ _ _ _ _ _ lab3 sub3 (WKHere _ _ _ c lab3 sub3 rest) (prove-subterm sub3 kids)))
      ((CLt _ _ _ _ lt)
        (let ((many r)) (tail $ kid _ rest c))
        (let ((erased _) (erased cp)) $ match erased r (((WKidLookup K S V R c kids) r2) ((Coercible (Shared) (WKidLookup K S V R c rest) r (Shared) (WKidLookup K S V R c kids) r2) cp))
          ((WKHit _ _ _ _ _ _ lab2 sub2 p st)
            (let ((erased p2)) (WKThere _ _ _ c lab2 sub2 k rest p))
            (let ((erased st2)) (subterm-trans st (prove-subterm rest kids)))
            (values (WKHit _ _ _ _ _ _ lab2 sub2 p2 st2)
              (coercible-ctor (Shared) WKHit K K S S V V R R c c rest kids (coercible-refl (Shared) lab2) (coercible-refl (Shared) sub2) p p2 st st2)))
          ((WKMiss _ _ _ _ _ _ p)
            (let ((erased p2)) (WNKLt _ _ _ _ c c1 lab3 sub3 rest lt p))
            (values (WKMiss _ _ _ _ _ _ p2) (coercible-ctor (Shared) WKMiss K K S S V V R R c c rest kids p p2))))
        (coerce r cp))
      ((CGt _ _ _ _ gt)
        (let ((many r)) (tail $ kid _ rest c))
        (let ((erased _) (erased cp)) $ match erased r (((WKidLookup K S V R c kids) r2) ((Coercible (Shared) (WKidLookup K S V R c rest) r (Shared) (WKidLookup K S V R c kids) r2) cp))
          ((WKHit _ _ _ _ _ _ lab2 sub2 p st)
            (let ((erased p2)) (WKThere _ _ _ c lab2 sub2 k rest p))
            (let ((erased st2)) (subterm-trans st (prove-subterm rest kids)))
            (values (WKHit _ _ _ _ _ _ lab2 sub2 p2 st2)
              (coercible-ctor (Shared) WKHit K K S S V V R R c c rest kids (coercible-refl (Shared) lab2) (coercible-refl (Shared) sub2) p p2 st st2)))
          ((WKMiss _ _ _ _ _ _ p)
            (let ((erased p2)) (WNKGt _ _ _ _ c c1 lab3 sub3 rest gt p))
            (values (WKMiss _ _ _ _ _ _ p2) (coercible-ctor (Shared) WKMiss K K S S V V R R c c rest kids p p2))))
        (coerce r cp))))
  (def-fns _ $ (many look : (erased Type V) (many K name) (erased (List S) w) (erased (Sp name w) sp) (subterm many (WordMap K S V) m) -> (many (WLookup K S Sp R V w m) r))
    (let-match many m (WMNode _ _ _ here kids))
    (let-match many (kview name w sp) (KNext _ _ _ _ c name1 w1 sp1)
      ((KEnd _ _ _ _) (match many here _
        ((None _) (WMiss _ _ _ _ _ _ _ $ WAHere _ _ _ _ _ kids))
        ((Some _ v) (WHit _ _ _ _ _ _ _ v $ WMHere _ _ _ _ v kids)))))
    (let-match many (kid _ kids c) (WKHit _ _ _ _ _ _ lab submap k st) ((WKMiss _ _ _ _ _ _ n) (WMiss _ _ _ _ _ _ _ $ WANoKid _ _ _ _ _ c w1 here kids n)))
    (let ((erased lw) (erased sl)) (kword lab))
    (let ((many ln) (erased lnp)) (klen name1 w1 sp1))
    (let ((many ll) (erased llp)) (klen lab lw sl))
    (let-match many (lt-dec ln ll) (No _ _ _ _ le-ge)
      ((Yes _ _ _ _ lt) (WMiss _ _ _ _ _ _ _ $ WADiverge _ _ _ _ _ c lab lw w1 here kids submap k sl $ WNPShort _ _ lw w1 ln ll lnp llp lt)))
    (let ((erased ge)) (le-lt-succ _ _ le-ge))
    (let ((many p) (many rest) (erased pw) (erased rw) (erased psp) (erased rsp) (erased ap) (erased lp)) (ksplit name1 w1 sp1 ll ln lnp ge))
    (let-match many (keq p pw psp lab lw sl) (WESame _ _ _)
      ((WEApart _ _ _ _ d) (WMiss _ _ _ _ _ _ _ $ WADiverge _ _ _ _ _ c lab lw w1 here kids submap k sl $ WNPDiff _ _ lw w1 pw rw ll ap lp llp d)))
    (let ((many r)) (tail $ look _ rest rw rsp (subterm (subterm-trans st (prove-subterm kids m))) submap))
    (let ((erased _) (erased cp)) $ match erased r (((WLookup K S Sp R V w m) r2) ((Coercible (Shared) (WLookup K S Sp R V rw submap) r (Shared) (WLookup K S Sp R V w m) r2) cp))
      ((WHit _ _ _ _ _ _ _ v q)
        (let ((erased q2)) (WMStep _ _ _ _ c lab lw w1 rw v here kids submap k sl ap q))
        (values (WHit _ _ _ _ _ _ _ v q2) (coercible-ctor (Shared) WHit K K S S Sp Sp R R V V rw w submap m (coercible-refl (Shared) v) q q2)))
      ((WMiss _ _ _ _ _ _ _ q)
        (let ((erased q2)) (WAStep _ _ _ _ _ c lab lw w1 rw here kids submap k sl ap q))
        (values (WMiss _ _ _ _ _ _ _ q2) (coercible-ctor (Shared) WMiss K K S S Sp Sp R R V V rw w submap m q q2))))
    (coerce r cp))
  (def-fns _ $ (many put-kid : (erased Type V) (subterm many (List $ WMKid K S V) kids) (many S c) (many K lab) (many (WordMap K S V) submap) -> (many (List $ WMKid K S V) r))
    (let-match many kids (Cons _ k rest) ((Nil _) (Cons _ (MkWMKid _ _ _ c lab submap) $ Nil _)))
    (let-match many k (MkWMKid _ _ _ c1 _ _))
    (match many (scmp c c1) _
      ((CEq _ _ _) (Cons _ (MkWMKid _ _ _ c lab submap) rest))
      (else (Cons _ k $ notail $ put-kid _ rest c lab submap))))
  (def-fns _
    ((many get : (erased Type V) (many K k) (subterm many (WordMap K S V) m) -> (erased (List S) w) (erased (Sp k w) p) (many (WLookup K S Sp R V w m) r))
      (let ((erased w) (erased p)) (kword k))
      (values w p $ look _ k w p m))
    ((many put : (erased Type V) (many K name) (many V v) (subterm many (WordMap K S V) m) -> (many (WordMap K S V) r))
      (let-match many m (WMNode _ _ _ here kids))
      (let ((erased w) (erased sp)) (kword name))
      (let-match many (kview name w sp) (KNext _ _ _ _ c name1 _ _) ((KEnd _ _ _ _) (WMNode _ _ _ (Some _ v) kids)))
      (let ((many leaf)) (WMNode K S V (Some _ v) $ Nil _))
      (let-match many (kid _ kids c) (WKHit _ _ _ _ _ _ lab submap _ st) ((WKMiss _ _ _ _ _ _ _) (WMNode _ _ _ here $ put-kid _ kids c name1 leaf)))
      (let ((many lp) (many lt) (many nt)) (kdiverge lab name1))
      (let ((erased ltw) (erased ltp)) (kword lt))
      (let-match many (kview lt ltw ltp) (KNext _ _ _ _ d lt1 _ _)
        ((KEnd _ _ _ _) (WMNode _ _ _ here $ put-kid _ kids c lab $ notail $ put _ nt v (subterm (subterm-trans st (prove-subterm kids m))) submap)))
      (let ((erased ntw) (erased ntp)) (kword nt))
      (let ((many mid)) $ match many (kview nt ntw ntp) (((WordMap K S V) _))
        ((KEnd _ _ _ _) (WMNode _ _ _ (Some _ v) $ Cons _ (MkWMKid _ _ _ d lt1 submap) $ Nil _))
        ((KNext _ _ _ _ e nt1 _ _) (WMNode _ _ _ (None _) $ Cons _ (MkWMKid _ _ _ d lt1 submap) $ Cons _ (MkWMKid _ _ _ e nt1 leaf) $ Nil _)))
      (WMNode _ _ _ here $ put-kid _ kids c lp mid)))
  (values (level-of get) get put))

(def-adts
  ((StrWord : ((String) s) ((List (Char)) w) -> Type)
    enum
    (many SWNil : -> (StrWord (SNil) (Nil (Char))))
    (many SWCons : (erased (Char) c) (erased (String) s) (erased (List (Char)) w) (erased (StrWord s w) p) -> (StrWord (SCons c s) (Cons (Char) c w)))))

(def-fns _ $ (erased str-word : (subterm erased (String) s) -> (erased (List (Char)) w) (erased (StrWord s w) p))
  (let-match erased s (SCons c rest) ((SNil) (values (Nil _) (SWNil))))
  (let ((erased w) (erased p)) (str-word rest))
  (values (Cons _ c w) (SWCons c rest w p)))

(def-fns _ $ (erased strword-fn : (erased (String) s) (erased (List (Char)) w1 w2) (subterm erased (StrWord s w1) p1) (erased (StrWord s w2) p2) -> (erased (Eq (List (Char)) w1 w2) e))
  (let-match erased p1 (SWCons _ s1 v1 q1) ((SWNil) (let-match erased p2 (SWNil)) (Refl _ w1)))
  (let-match erased p2 (SWCons _ _ v2 q2))
  (let-match erased (strword-fn s1 v1 v2 q1 q2) (Refl _ _))
  (Refl _ w1))

(def-fns _ $ (erased strlen-word : (erased (String) s) (erased (Nat) n) (erased (List (Char)) w) (subterm erased (StrLength s n) l) (erased (StrWord s w) p) -> (erased (Length (Char) w n) r))
  (let-match erased l (SLenCons c s1 n1 l1) ((SLenNil) (let-match erased p (SWNil)) (LengthNil _)))
  (let-match erased p (SWCons _ _ w1 p1))
  (LengthCons _ c w1 n1 $ strlen-word s1 n1 w1 l1 p1))

(def-fns _ $ (erased word-strlen : (erased (String) s) (erased (List (Char)) w) (erased (Nat) n) (subterm erased (StrWord s w) p) (erased (Length (Char) w n) l) -> (erased (StrLength s n) r))
  (let-match erased p (SWCons c s1 w1 p1) ((SWNil) (let-match erased l (LengthNil _)) (SLenNil)))
  (let-match erased l (LengthCons _ _ _ n1 l1))
  (SLenCons c s1 n1 $ word-strlen s1 w1 n1 p1 l1))

(def-fns _ $ (erased append-word : (erased (String) a b s) (erased (List (Char)) wa wb w) (subterm erased (Append a b s) ap) (erased (StrWord a wa) pa) (erased (StrWord b wb) pb) (erased (StrWord s w) p) ->
    (erased (Concat (Char) wa wb w) r))
  (let-match erased ap (AppCons c a1 _ s1 ap1)
    ((AppNil _) (let-match erased pa (SWNil)) (let-match erased (strword-fn b wb w pb p) (Refl _ _)) (CatNil _ wb)))
  (let-match erased pa (SWCons _ _ wa1 pa1))
  (let-match erased p (SWCons _ _ w1 p1))
  (CatCons _ c wa1 wb w1 $ append-word a1 b s1 wa1 wb w1 ap1 pa1 pb p1))

(def-fns _ $ (erased strlt-word : (erased (String) a b) (erased (List (Char)) wa wb) (subterm erased (StrLt a b) lt) (erased (StrWord a wa) pa) (erased (StrWord b wb) pb) ->
    (erased (ListLt (Char) CharLt wa wb) r))
  (match erased lt _
    ((SLtNil d _) (let-match erased pa (SWNil)) (let-match erased pb (SWCons _ _ tw _)) (LLNil _ _ d tw))
    ((SLtHead c d _ _ q)
      (let-match erased pa (SWCons _ _ sw _))
      (let-match erased pb (SWCons _ _ tw _))
      (LLHead _ _ c d sw tw q))
    ((SLtTail c s t q)
      (let-match erased pa (SWCons _ _ sw pa1))
      (let-match erased pb (SWCons _ _ tw pb1))
      (LLTail _ _ c sw tw $ strlt-word s t sw tw q pa1 pb1))))

(def-fns _
  ((erased str-kword : (erased (String) s) -> (erased (List (Char)) w) (erased (StrWord s w) p))
    (str-word s))
  ((many str-kview : (many (String) s) (erased (List (Char)) w) (erased (StrWord s w) p) -> (many (KView (String) (Char) StrWord s w) v))
    (match many s _
      ((SNil) (let-match erased p (SWNil)) (KEnd _ _ _ s))
      ((SCons c rest) (let-match erased p (SWCons _ _ rw q)) (KNext _ _ _ s c rest rw q))))
  ((many str-klen : (many (String) s) (erased (List (Char)) w) (erased (StrWord s w) p) -> (many (Nat) n) (erased (Length (Char) w n) l))
    (let ((many n) (erased l)) (str-length s))
    (values n $ strlen-word s n w l p))
  ((many str-ksplit : (many (String) s) (erased (List (Char)) w) (erased (StrWord s w) p) (many (Nat) n) (erased (Nat) len) (erased (Length (Char) w len) l) (erased (Lt n (Succ len)) le) ->
      (many (String) a) (many (String) b) (erased (List (Char)) wa) (erased (List (Char)) wb) (erased (StrWord a wa) pa) (erased (StrWord b wb) pb)
      (erased (Concat (Char) wa wb w) c) (erased (Length (Char) wa n) la))
    (let ((many a) (many b) (erased ap) (erased la)) (str-split s n len (word-strlen s w len p l) le))
    (let ((erased wa) (erased pa)) (str-word a))
    (let ((erased wb) (erased pb)) (str-word b))
    (values a b wa wb pa pb (append-word a b s wa wb w ap pa pb p) (strlen-word a n wa la pa)))
  ((many str-keq : (many (String) a) (erased (List (Char)) wa) (erased (StrWord a wa) pa) (many (String) b) (erased (List (Char)) wb) (erased (StrWord b wb) pb) ->
      (many (WordEq (Char) CharLt wa wb) e))
    (let-match many (str-eq a b) (Unequal _ _ _ _ d)
      ((Equal _ _ _) (let-match erased (strword-fn a wa wb pa pb) (Refl _ _)) (WESame _ _ wa)))
    (WEApart _ _ wa wb $ match erased d (((WordApart (Char) CharLt wa wb) x))
      ((ApLt _ _ _ _ q) (WALt _ _ wa wb $ strlt-word a b wa wb q pa pb))
      ((ApGt _ _ _ _ q) (WAGt _ _ wa wb $ strlt-word b a wb wa q pb pa))))
  ((many str-kdiverge : (many (String) lab) (many (String) name) -> (many (String) common) (many (String) ra) (many (String) rb))
    (let ((many k) (many lt) (many nt) (erased q) (erased aq) (erased lq)) (common-prefix lab lab name (Zero) (SNil) (AppNil lab) (SLenNil)))
    (let ((erased len) (erased ll)) (str-length lab))
    (let ((many lp) (many _) (erased _) (erased _)) (str-split lab k len ll (prefix-lt q lt lab k len aq lq ll)))
    (values lp lt nt))
  ((many str-scmp : (many (Char) a) (many (Char) b) -> (many (Cmp (Char) CharLt a b) c))
    (char-cmp a b)))

(let ((many str-key-ops)) (MkKeyOps (level-of str-kview) (String) (Char) StrWord CharLt str-kword str-kview str-klen str-ksplit str-keq str-kdiverge str-scmp))
(let ((erased _) (many nm-get) (many nm-set)) (word-map-factory _ _ _ _ _ str-key-ops))

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

(let ((erased sixteen-u62)) (u8-u62 _ (prove-literal-lt 16 u8-modulus)))
(let ((many hex-digits)) "0123456789abcdef")
(let ((many hex-digits-len) (erased hex-digits-sl)) (str-length hex-digits))
(comptime-match many (nat-eq hex-digits-len 16) (Equal _ _ _))

(def-fns _ $ (many hex-chars : (many (Nat) k) (erased (Lt k u8-modulus) q) -> (many (Char) hi) (many (Char) lo))
  (let ((many h) (many l) (erased kk) (erased mm) (erased ad) (erased lt-l) (erased _) (erased _))
    (u62-divmod k 16 (u8-u62 _ q) sixteen-u62 sixteen-positive))
  (let ((many hc) (erased _) (erased _) (erased _) (erased _)) (str-get hex-digits h 16 hex-digits-sl (div-small h 16 kk l k u8-modulus mm ad q sixteen-squared)))
  (let ((many lc) (erased _) (erased _) (erased _) (erased _)) (str-get hex-digits l 16 hex-digits-sl lt-l))
  (values hc lc))

(def-fns _ $ (many hex-byte-rope : (many (Char) c) -> (many (Rope) r))
  (let-match many c (MkChar u))
  (let-match many u (MkU8 k q))
  (let ((many hi) (many lo)) (hex-chars k q))
  (rcat (RChar hi) $ RChar lo))

(def-fns _ $ (many hex-pair : (many (Char) a) (many (Char) b) -> (many (Maybe $ Char) r))
  (match many (and (is-hex a) (is-hex b)) _
    ((BTrue) (Some _ $ byte-of-nibbles (hex-digit a) (hex-digit b)))
    ((BFalse) (None _))))

(def-fns _ $ (many word-char : (many (Char) c) -> (many (Bool) r))
  (and (char-between c #\! #\~) $ not $ or (char-eqb c #\x28) $ or (char-eqb c #\x29) $ char-eqb c #\x3b))

; Bare where the reader's word syntax admits the character, hexadecimal otherwise.
(def-fns _ $ (many lit-char-rope : (many (Char) c) -> (many (Rope) r))
  (let-match many (char-eqb c #\space) (BFalse) ((BTrue) (RStr "#\\space")))
  (let-match many (char-eqb c #\newline) (BFalse) ((BTrue) (RStr "#\\newline")))
  (let-match many (char-eqb c #\tab) (BFalse) ((BTrue) (RStr "#\\tab")))
  (let-match many (word-char c) (BFalse) ((BTrue) (rcat (RStr "#\\") $ RChar c)))
  (rcat (RStr "#\\x") $ hex-byte-rope c))

(def-fns _ $ (many all-word-chars : (subterm many (String) s) -> (many (Bool) r))
  (match many s _
    ((SNil) (BTrue))
    ((SCons c rest) (and (word-char c) $ tail $ all-word-chars rest))))

(def-fns _ $ (many is-plain-name : (many (String) s) -> (many (Bool) r))
  (let-match many s (SCons c _) ((SNil) (BFalse)))
  (and (all-word-chars s) $ and (not $ is-literal-name s) $ and (not $ str-eqb s "_") $ and (not $ str-eqb s "$")
    $ and (not $ char-eqb c #\") $ and (not $ is-reserved-name s) $ not $ str-starts "#\"" s))

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

(def-adts $ (Shown : -> Type)
  enum
  (many ShText : (many (String) s) -> (Shown))
  (many ShNat : (many (Nat) n) -> (Shown))
  (many ShChr : (many (Char) c) -> (Shown))
  (many ShStr : (many (String) s) -> (Shown)))

(def-adts $ (Name : -> Type)
  enum
  (many NSrc : (many (String) s) -> (Name))
  (many NGen : (many (Nat) n) (many (String) s) -> (Name))
  (many NHandle : (many (Nat) id) (many (Reading) rd) (many (Multiplicity) m) (many (Shown) shown) -> (Name)))

(def-fns _ $ (many name-eq : (many (Name) a) (many (Name) b) -> (many (Bool) r))
  (match many a _
    ((NSrc s) (match many b _ ((NSrc t) (str-eqb s t)) (else (BFalse))))
    ((NGen m _) (match many b _ ((NGen n _) (nat-eqb m n)) (else (BFalse))))
    ((NHandle m ra _ _) (match many b _ ((NHandle n rb _ _) (and (nat-eqb m n) $ reading-eq ra rb)) (else (BFalse))))))

(def-fns _ $ (many rlist : (subterm many (List $ Rope) rs) -> (many (Rope) r))
  (match many rs _
    ((Nil _) (REmpty))
    ((Cons _ r rest) (RCat r $ notail $ rlist rest))))

; Every name a string-keyed WordMap holds, with its value.
(def-fns _
  ((many nm-entries : (erased Type V) (subterm many (WordMap (String) (Char) V) m) (many (Rope) path) (many (List $ Pair (String) V) acc) -> (many (List $ Pair (String) V) r))
    (let-match many m (WMNode _ _ _ here kids))
    (let ((many acc2)) $ match many here (((List $ Pair (String) V) _)) ((None _) acc) ((Some _ v) (Cons _ (MkPair _ _ (rope-str path) v) acc)))
    (tail $ nm-kids-entries _ kids path acc2))
  ((many nm-kids-entries : (erased Type V) (subterm many (List $ WMKid (String) (Char) V) kids) (many (Rope) path) (many (List $ Pair (String) V) acc) -> (many (List $ Pair (String) V) r))
    (let-match many kids (Cons _ k rest) ((Nil _) acc))
    (let-match many k (MkWMKid _ _ _ c lab submap))
    (let ((many path2)) (rcat3 path (RChar c) (RStr lab)))
    (match many rest _
      ((Nil _) (tail $ nm-entries _ submap path2 acc))
      ((Cons _ _ _) (tail $ nm-kids-entries _ rest path $ notail $ nm-entries _ submap path2 acc)))))

(def-adts $ (NameIndex : (Type V) -> Type)
  enum
  (many MkNameIndex : (erased Type V) (many (WordMap (String) (Char) V) src) (many (List $ Pair (Name) V) gen) -> (NameIndex V)))

(def-fns _ $ (many name-index-empty : (erased Type V) -> (many (NameIndex V) m))
  (MkNameIndex _ (wm-empty _ _ _) (Nil _)))

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
  (let ((erased _) (erased _) (many r)) (nm-get _ s src))
  (match many r _ ((WHit _ _ _ _ _ _ _ x _) (Some _ x)) ((WMiss _ _ _ _ _ _ _ _) (None _))))

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
