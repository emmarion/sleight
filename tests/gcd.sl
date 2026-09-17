; needs: lt_subterm div
; expect: 6
; Euclid's algorithm. nat-mod returns the remainder with an erased proof that it is below the divisor,
; and lt-sub turns that bound into the Subterm proof gcd's recursive call needs.

(def-lvl G)
(let (erased ng) (prove-predates nat-lvl G))
(let (erased sg) (prove-predates S G))
(def-fns G $ many nat-mod : (subterm many (Nat) n) (many (Nat) d1) -> (many (Nat) r) (erased (Lt r (Succ d1)) p)
  (match many (lt-dec (predates ng) n (Succ d1)) _
    ((Yes x y q) (values n q))
    ((No x y q)
      (let (erased lt1) (match erased q (((Lt d1 n) l)) (absurd LtZ) ((LtS a b p1) p1)))
      (let (many r0) (erased sp) (sub-pos (predates sg) n d1 lt1))
      (nat-mod (subterm sp) r0 d1))))

(def-lvl H)
(let (erased gh) (prove-predates G H))
(let (erased lh) (prove-predates L H))
(def-fns H $ many gcd : (many (Nat) a) (subterm many (Nat) b) -> (many (Nat) g)
  (match many b _
    ((Zero) a)
    ((Succ b1)
      (let (many r) (erased p) (nat-mod (predates gh) a b1))
      (gcd b (subterm (lt-sub (predates lh) b r p)) r))))

(gcd 12 18)
