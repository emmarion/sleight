; error: a is not a strict subterm of (Succ b)
; Lt a (Succ b) alone does not make a a subterm of (Succ b), since a may be b: the case lt_subterm.sl's
; le-split separates.

(def-lvl L)
(def-fns L $ erased claim : (erased (Nat) a) (erased (Nat) b) (erased (Lt a (Succ b)) p) ->
    (erased (Subterm (Nat) a (Nat) (Succ b)) q)
  (prove-subterm a (Succ b)))
