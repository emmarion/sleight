(def-adts $ (XTree : -> Type)
  enum
  (many XGen : -> (XTree))
  (many XNode : (many (XTree) l r) -> (XTree))
  (many XExpand : (many (Nat) s) -> (XTree)))

(def-adts $ (XEntry : -> Type)
  enum
  (many MkXEntry : (many (Nat) s) (many (XTree) out) -> (XEntry)))

(def-adts $ (XOutcome : -> Type)
  enum
  (many XDone : (many (Nat) v) (many (List (XEntry)) rest) -> (XOutcome))
  (many XNeed : (many (Nat) s) -> (XOutcome))
  (many XTooDeep : -> (XOutcome)))
