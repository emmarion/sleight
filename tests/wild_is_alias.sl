; expect: 2
; An is return instantiated with an argument of an alias type, then fed to a `_` solved through a
; constructor's is field: the entries' types are read canonically wherever they were computed.

(let (erased Alias) (Nat))

(def-adts $ Box : ((Nat) k) -> Type
  enum
  (many MkBox : (erased (Nat) n) (many n is m) -> (Box n)))

(def-lvl L)
(def-fns L $ many same : (many (Nat) a) -> (many a is r)
  a)
(def-fns L $ many unbox : (erased (Nat) k) (many (Box k) b) -> (many (Nat) r)
  (match many b _
    ((MkBox n m) (Succ m))))

(let (many Alias x) (Succ (Zero)))
(let (many r) (same x))
(unbox _ (MkBox _ r))
