(def-adts
  ((Bool : -> Type)
    enum
    (many True : -> (Bool))
    (many False : -> (Bool))))
(let ((many (Bool) a)) (Zero))
a
