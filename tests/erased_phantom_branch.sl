; needs: list
; error: only one real branch
; An erased scrutinee may be headed by a phantom constructor, so that branch is real and needs refuting.

(def-adts $ (Opt : -> Type)
  enum
  (many Some : -> (Opt))
  (erased Ghost : -> (Opt)))

(def-adts
  ((P : ((Opt) o) -> Type)
    enum
    (many PSome : -> (P (Some)))
    (many PAny : (erased (Opt) o) -> (P o))))

(def-lvl X)
(def-fns X $ (many prove : (erased (Opt) o) -> (many (P o) p))
  (match erased o (((P o) r))
    ((Some) (PSome))
    ((Ghost) (PAny (Ghost)))))
