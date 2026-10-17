; expect: 5
; warn-unused: yes
; WARNINGS.md 10, on parameters and fields. The ; warns: lines at the end of the file name lines of this file.

(def-fns _ $ (many pick : (many (Nat) a b) (erased (Lt b 5) _lt) -> (many (Nat) r)) a)

(def-fns _ $ (many keep : (erased (Nat) _n) (many (Nat) x) -> (many (Nat) r)) x)
(def-fns _ $ (many pass : (many (Nat) n) (many (Nat) x) -> (many (Nat) r)) (keep n x))

(def-fns _ $ (many fixed : (subterm many (List (Nat)) xs) (subterm erased (Nat) phase) -> (many (Nat) r))
  (match many xs _ ((Nil _) 0) ((Cons _ h t) (nat-add h $ notail $ fixed t 0))))

(def-adts $ (Two : -> Type) enum (many One : -> (Two)) (many Wide : (many (Nat) v) (erased (Lt v 3) p) -> (Two)))
(def-fns _ $ (many narrow : (many (Two) b) (erased (Eq (Nat) (Zero) (Succ (Zero))) no) -> (many (Nat) r))
  (match many b _ ((One) 0) (absurd (Wide v p) no)))

(def-fns _ $ (many slot : (many (Nat) a) -> (many (Slot) s)) (slot-of a))

(nat-add (pick 1 2 (prove-literal-lt 2 5)) $ pass 3 4)
; warns: tests/unused_params_warn.sl:5:27: warning: `b` is referenced only in erased positions; declare it `erased`, or rename it `_b`
; warns: tests/unused_params_warn.sl:8:27: warning: `n` is referenced only in erased positions; declare it `erased`, or rename it `_n`
; warns: tests/unused_params_warn.sl:10:59: warning: unused `phase`; rename it `_phase`
; warns: tests/unused_params_warn.sl:15:43: warning: unused `v`; write `_` in its place
; warns: tests/unused_params_warn.sl:15:45: warning: unused `p`; write `_` in its place
