; error: Level has no Matchable open
; A match's results are not in scope for its own branches. The annotation states what the match produces, and
; a branch that fetched one from ambient scope would be reading the result it is there to establish. Here that
; would mint a (Matchable enum Level) listing no constructors, which appears to make (Level) an empty type, so
; an absurd body accepts a level as a proof of (False).

(def-lvl L)

(let ((erased m))
  (match erased (Zero) (((Matchable enum Level) m))
    (else (matchable-of Level))))

(def-fns _ $ (erased absurd forge : -> (erased (False) f))
  L)

(let ((erased f)) (forge))
