; error: error: the scrutinee contradicts the facts in force (`(Succ _<**>)` vs `(Zero)`)
; As in tests/display_shadow_bad.sl, but in a contradiction: the field n shadows the parameter n that p's
; index mentions, so the parameter is shown by its id.

(def-adts $ (Idx : ((Nat) i) -> Type) enum
  (many IZ : -> (Idx (Zero))))
(def-fns _ $ (many bad : (many (Nat) n) (erased (Idx (Succ n)) p) (many (Nat) m) -> (many (Nat) r))
  (match many m (((Nat) r))
    ((Zero) (Zero))
    ((Succ n) (let-match erased p (IZ)) (Zero))))
(Zero)
; warns: tests/display_contra_shadow_bad.sl:10:12: warning: declaration of `n` shadows a previous binder
; warns: tests/display_contra_shadow_bad.sl:7:26: note: shadowed binder is here
