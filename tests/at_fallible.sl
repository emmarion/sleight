; expect: 2
(def-adts $ (Meters : -> Type) enum newtype (many MkMeters : (unique (Nat) n) -> (Meters)))
(def-adts $ (Outcome : (Type T) -> Type) enum
  (many Wrapped : -> (Outcome (Meters)))
  (many Kept : -> (Outcome (Nat))))

(def-fns _ $ (many try-wrap : (unique (Nat) a) (many (Bool) ok) ->
    (erased Type T) (unique T v at a) (many (Outcome T) o))
  (match many ok _
    ((BTrue) (values (Meters) (MkMeters a) (Wrapped)))
    ((BFalse) (values (Nat) a (Kept)))))

(def-fns _ $ (many use : (unique (Nat) a) (many (Bool) ok) -> (many (Nat) r))
  (let ((erased _) (unique v) (many o)) (try-wrap a ok))
  (let-match many o (Wrapped) ((Kept) (share v)))
  (let-match unique v (MkMeters n))
  (share n))

(use (Succ (Succ (Zero))) (BTrue))
