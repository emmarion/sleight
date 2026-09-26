; expect: 7
; A unique let-match on a type with cells: its absurd branch carries the cell binder, as a unique match's does
; (UNIQUE.md U5).

(def-adts $ (Opt : -> Type) enum
  (many Full : (many (Nat) v) -> (Opt))
  (many Empty : (erased (False) f) -> (Opt)))

(def-lvl X)

(def-fns X $ (many get : (unique (Opt) o) -> (many (Nat) n))
  (let-match unique o (Full v u) (absurd (Empty f u) f))
  v)

(get (Full 7))
