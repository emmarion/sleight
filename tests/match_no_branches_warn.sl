; A non-erased match with no branches warns; the same match as an absurd function's body does not.

(def-adts $ (Void : -> Type)
  enum)

(def-lvl L)

(def-fns L $ (many explode : (erased Type A) (many (Void) f) -> (many A a))
  (match many f _))

(def-fns L $ (many absurd explode2 : (erased Type A) (many (Void) f) -> (many (Void) v))
  (match erased f (((Void) w))))

; warns: tests/match_no_branches_warn.sl:9:3: warning: a non-erased `match` with no non-absurd branch compiles to a runtime `absurd`; mark the enclosing branch or function `absurd` instead
