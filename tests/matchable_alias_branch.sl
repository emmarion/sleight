; Two declared types of one shape, and an index that names them: the TF branch equates Feet with Meters
; and their Matchables, which nothing refutes, so a match on a Feet inside it finds its Matchable through
; the alias (section 19).
; expect: 3
(def-adts $ Meters : -> Type
  enum
  (many MkMeters : (many (Nat) n) -> (Meters)))
(def-adts $ Feet : -> Type
  enum
  (many MkFeet : (many (Nat) n) -> (Feet)))
(def-adts $ Tag : (Type A) -> Type
  enum
  (many TM : -> (Tag (Meters)))
  (many TF : -> (Tag (Feet))))
(def-lvl L)
(def-fns L $ many pick : (many (Tag (Meters)) t) (many (Feet) x) -> (many (Nat) n)
  (match many t (((Nat) n))
    ((TM) (match many x (((Nat) n)) ((MkFeet k) k)))
    ((TF) (match many x (((Nat) n)) ((MkFeet k) k)))))
(pick (TM) (MkFeet 3))
