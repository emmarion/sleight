; expect: (MkOut 1 4 0 2 1 500000)
; externs: only
; Matches on nat-cmp and lt-dec, whose extraction templates reach one outcome per constructor: an arm
; holding another such match, an else standing for two outcomes that reads the decision back, a decision
; used as a value, numbers past the host's integers, and a tail loop through an arm a million times, all
; inside a thunk so the extracted program does the work.

(def-adts $ (Out : -> Type)
  enum
  (many MkOut : (many (Nat) a) (many (Nat) b) (many (Nat) c) (many (Nat) d) (many (Nat) e) (many (Nat) f) -> (Out)))

(def-fns _ $ (many cmp-code : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R) (erased T a) (erased T b)
    (many (Cmp T R a b) c) -> (many (Nat) i))
  (match many c _ ((CLt _ _ _ _ _) 0) ((CEq _ _ _) 1) ((CGt _ _ _ _ _) 2)))

(def-fns _ $ (many order3 : (many (Nat) a) (many (Nat) b) (many (Nat) c) -> (many (Nat) r))
  (match many (nat-cmp a b) _
    ((CLt _ _ _ _ _) (match many (nat-cmp b c) _ ((CLt _ _ _ _ _) 0) ((CEq _ _ _) 1) ((CGt _ _ _ _ _) 2)))
    ((CEq _ _ _) 3)
    ((CGt _ _ _ _ _) (match many (lt-dec c a) _ ((Yes _ _ _) 4) ((No _ _ _) 5)))))

(def-fns _ $ (many unequal : (many (Nat) a) (many (Nat) b) -> (many (Nat) r))
  (match many (nat-cmp a b) _
    ((CEq _ _ _) 9)
    (else c (cmp-code _ _ _ _ c))))

(def-fns _ $ (many held : (many (Nat) a) (many (Nat) b) -> (many (Nat) r))
  (cmp-code _ _ _ _ $ nat-cmp a b))

(def-fns _ $ (many count : (subterm many (Nat) n) (many (Nat) acc) -> (many (Nat) r))
  (let-match many n (Succ k) ((Zero) acc))
  (match many (lt-dec k 500000) _
    ((Yes _ _ _) (tail $ count k acc))
    ((No _ _ _) (tail $ count k $ Succ acc))))

(def-fns _ $ (many run : -> (many (Out) o))
  (let ((many big)) (nat-mul (nat-mul 1073741824 1073741824) 1024))
  (MkOut (order3 3 5 5) (order3 (Succ big) big 2) (unequal big (Succ big)) (held (Succ big) big) (held 7 7)
    (count (nat-mul 1000 1000) 0)))

run
