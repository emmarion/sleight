; A spec file: it sets the unit's goal and runs as any file does under the default `--goal none`.
(def-adts
  ((Doubler : -> Type)
    enum
    (many MkDoubler : (erased (Level) L) (many (Fn L (many (Nat) n) -> (many (Nat) m)) f) -> (Doubler))))
(goal many (Doubler))
