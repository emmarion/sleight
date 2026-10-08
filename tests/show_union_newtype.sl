; expect: _
(def-adts $ (MU : (Type A) -> Type)
  union newtype
  (many MUNone : (erased Type A) (many (Slot) s) -> (MU A))
  (many MUSome : (erased Type A) (unique A value) -> (MU A)))
(let ((many m)) (MUSome _ (Succ (Zero))))
m
