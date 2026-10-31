(def-adts $ (Checked : (Type P) -> Type)
  enum
  (many ChkYes : (erased Type P) (erased P p) -> (Checked P))
  (many ChkNo : (erased Type P) -> (Checked P)))
