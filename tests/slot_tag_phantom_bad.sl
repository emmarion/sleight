; error: `slot-tag`: `Ghost` is phantom, so it has no tag slot
(def-adts $ (Shade : -> Type)
  enum
  (many Red : -> (Shade))
  (erased Ghost : -> (Shade))
  (many Green : -> (Shade)))
(def-fns _ $ (erased f : (erased (Shade) c) ->)
  (match erased c ()
    ((Red) (values))
    ((Ghost) (slot-tag c) (values))
    ((Green) (values))))
(Zero)
