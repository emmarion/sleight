; expect: 0
; The companion to cell_subterm_bad: a unique match's field is a subterm of the scrutinee as in any match,
; so structural recursion is unaffected by the extra cell binder.

(def-adts $ (Box : -> Type) enum (many B : (many (Nat) n) -> (Box)))
(def-fns _ $ (many probe : (unique (Box) x) -> (many (Nat) r))
  (match unique x (((Nat) r))
    ((B n c)
      (let ((erased p)) (prove-subterm n x))
      n)))
(probe (B (Zero)))
; warns: tests/cell_subterm.sl:7:4: warning: lopsided `match`; flatten it with a `let-match` on `B`
