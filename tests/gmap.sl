; expect: (SCons (Succ (Zero)) (SNil))
; Generic over a shape: gmap maps over any type whose constructors have List's, taking the type constructor,
; both constructors and the Matchable as arguments, and runs at the prelude's List and at Seq. The shape is
; spelled out in the signature, so a type with other constructors does not fit it.

(def-adts $ Seq : (Type A) -> Type
  enum
  (many SNil : (erased Type A) -> (Seq A))
  (many SCons : (erased Type A) (many A head) (many (Seq A) tail) -> (Seq A)))

(def-lvl M)
(def-fns M $ many inc : (many (Nat) n) -> (many (Nat) m) (Succ n))

(def-lvl G)
(let (erased mg) (prove-predates M G))
(def-fns G $ many gmap : (erased (TyCtor (Type A) -> Type) F)
    (many (ValCtor (erased Type A) -> (F A)) NilC)
    (many (ValCtor (erased Type A) (many A head) (many (F A) tail) -> (F A)) ConsC)
    (many (Matchable enum F (many NilC) (many ConsC)) m)
    (erased Type A) (erased Type B)
    (many (Fn M (many A x) -> (many B y)) f)
    (subterm many (F A) xs) -> (many (F B) ys)
  (open-adt m)
  (match many xs (((F B) r))
    ((NilC a) (NilC B))
    ((ConsC a hd tl) (ConsC B (f (predates mg) hd) (gmap F NilC ConsC m A B f (subterm (prove-subterm tl xs)) tl)))))

(let (many ys) (gmap List Nil Cons (matchable-of List) (Nat) (Nat) inc (Cons (Nat) (Zero) (Nil (Nat)))))
(gmap Seq SNil SCons (matchable-of Seq) (Nat) (Nat) inc (SCons (Nat) (Zero) (SNil (Nat))))
