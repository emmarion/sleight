; The certified presentation walks of arities m to hi - 1 and the unavoidability statement they give with cap.sl's
; checks: on a plain cubic pentagonal map every dart of positive dscore has an obligation of the walk of its arity, or a
; cap obligation when the arity is 12 or more, fitting exactly at some dart. Load after cap.sl.

(def-adts $ (Checked : (Type P) -> Type)
  enum
  (many ChkYes : (erased Type P) (erased P p) -> (Checked P))
  (many ChkNo : (erased Type P) -> (Checked P)))
