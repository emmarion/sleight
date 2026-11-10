; A result is judged by its solved term and type: the `_` of `MkAny` is solved by a later entry of the `values`,
; to an entry `sorry` made, and the `Any` it builds is tainted though nothing in its own entry named one. So it
; is through a cell, through a constructor application nested in another, in a `let` and in a function's results,
; and where the term mentions only the slot of such an entry.
; `use` would reach `absurd` code on any of them.
(def-adts $ (Any : -> Type)
  enum
  (many MkAny : (erased (Eq (Bool) (BTrue) (BFalse)) e) (many (Nat) n) -> (Any)))
(def-fns _ $ (many absurd use : (many (Any) a) -> (many (Nat) r))
  (let-match erased a (MkAny k _))
  (match erased k _ (absurd Refl)))
(def-fns _ $ (many in-match : (many (Nat) x) -> (many (Nat) r))
  (let ((unique c)) (cell-alloc MkAny))
  (let ((erased _e) (many a) (erased _b))
    (match many x (((Eq (Bool) (BTrue) (BFalse)) e) ((Any) a) ((Eq (Any) a (MkAny e 7)) b))
      ((Zero) (values (sorry _) (MkAny _ 7) (Refl _ _)))
      ((Succ _p) (values (sorry _) (share (c _ 7)) (Refl _ _)))))
  (use a))
(def-fns _ $ (many in-let : (many (Nat) x) -> (many (Nat) r))
  (let ((erased (Eq (Bool) (BTrue) (BFalse)) e) (many (List (Any)) as) (erased (Eq (List (Any)) as (Cons _ (MkAny e x) (Nil _))) _b))
    (values (sorry _) (Cons _ (MkAny _ x) (Nil _)) (Refl _ _)))
  (let-match many as (Cons _ a _))
  (use a))
(def-fns _ $ (many returned : (many (Nat) x) -> (erased (Eq (Bool) (BTrue) (BFalse)) e) (many (Any) a) (erased (Eq (Any) a (MkAny e x)) b))
  (values (sorry _) (MkAny _ x) (Refl _ _)))
(in-match 0)
;! file "sorry/later-cell.sl"
(in-match 1)
;! file "sorry/later-let.sl"
(in-let 0)
;! file "sorry/later-returned.sl"
(let ((erased _e) (many a) (erased _b)) (returned 1))
(use a)
;! file "sorry/later-run.sl"
(let ((erased (Eq (Bool) (BTrue) (BFalse)) e) (many (Any) a2) (erased (Eq (Any) a2 (MkAny e 7)) _b2))
  (values (sorry _) (MkAny _ 7) (Refl _ _)))
(use a2)
;! file "sorry/later-slot.sl"
(def-adts $ (Placed2 : -> Type)
  enum
  (many MkPlaced2 : (erased (Slot) s) (many (Nat) n) -> (Placed2)))
(let ((many _n) (many p) (erased _b3)) (match many 0 (((Nat) n) ((Placed2) p) ((Eq (Placed2) p (MkPlaced2 (slot-of n) 7)) b))
  ((Zero) (values (sorry _) (MkPlaced2 _ 7) (Refl _ _)))
  ((Succ _k) (values (sorry _) (MkPlaced2 _ 7) (Refl _ _)))))
p
; expect: sorry
; expect: sorry
; expect: sorry
; expect: sorry
; expect: sorry
; expect: sorry
; warns: tests/sorry_later.sl:16:23: warning: this unit uses `sorry` 7 times, first here; nothing that depends on it runs
