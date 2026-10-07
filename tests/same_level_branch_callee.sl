; expect: 0
; The unmarked same-level call warns though its callee is bound inside a branch: by a `let-match` in `g`, by a `let` alias in `h`.
(def-lvl L)
(def-adts $ (Packed : -> Type)
  enum
  (many Pack : (many (Fn L (many (Packed) q) (subterm many (Nat) n) -> (many (Nat) r)) f) -> (Packed)))
(def-fns L
  ((many g : (many (Packed) q) (subterm many (Nat) n) -> (many (Nat) r))
    (match many n _
      ((Zero) 0)
      ((Succ k) (let-match many q (Pack f)) (f q k))))
  ((many h : (many (Packed) q) (subterm many (Nat) n) -> (many (Nat) r))
    (match many n _
      ((Zero) 0)
      ((Succ k) (let ((many h2)) h) (h2 q k)))))
(nat-add (g (Pack g) 2) (h (Pack h) 2))
; warns: tests/same_level_branch_callee.sl:9:6: warning: lopsided `match`; flatten it with a `let-match` on `Succ`
; warns: tests/same_level_branch_callee.sl:11:45: warning: same-level call to `f` is unmarked; mark it `tail`
; warns: tests/same_level_branch_callee.sl:13:6: warning: lopsided `match`; flatten it with a `let-match` on `Succ`
; warns: tests/same_level_branch_callee.sl:15:37: warning: same-level call to `h2` is unmarked; mark it `tail`
