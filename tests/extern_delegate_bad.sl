; prelude: none
; error: a function marked `extern` cannot have a `delegate` body
; Without the prelude u62-lt-dec's implementation is unclaimed, so a model of it can be written here, and its
; delegate mark is refused: the Delegate proof would let a coerce run the FFI's native-int comparison under
; lt-dec's signature, which carries no bound.
(def-adts $ (Nat : -> Type) enum (many Zero : -> (Nat)) (many Succ : (many (Nat) pred) -> (Nat)))
(def-adts
  ((Dec : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many Yes : (erased (Nat) a) (erased (Nat) b) -> (Dec a b))
    (many No : (erased (Nat) a) (erased (Nat) b) -> (Dec a b))))
(def-fns _ $ (many lt-dec : (subterm many (Nat) a) (many (Nat) b) -> (many (Dec a b) d))
  (let-match many b (Succ b1)
    ((Zero) (No a b)))
  (let-match many a (Succ a1) ((Zero) (Yes a b)))
  (match many (notail $ lt-dec a1 b1) _ ((Yes _ _) (Yes a b)) ((No _ _) (No a b))))
(def-fns _ $ (many extern u62-lt-dec at lt-dec : (many (Nat) n) (many (Nat) m) -> (many (Dec n m) d))
  (delegate (lt-dec n m)))
(Zero)
