; phantom constructors (DESIGN.md section 21): built only in erased positions, and erased throughout their branches
(def-adts
  ((Opt : -> Type)
    enum
    (many None : -> (Opt))
    (erased Hidden : (erased (Nat) n) -> (Opt))))
(def-lvl L)
(def-fns L $ (many get : (many (Opt) o) (erased (Nat) e) -> (many (Nat) r))
  (match many o (((Nat) r))
    ((None) (Succ (Zero)))
    ((Hidden n) e)))
(def-fns L $ (erased peek : (erased (Opt) o) -> (many (Nat) r))
  (match erased o (((Nat) r))
    ((None) (Zero))
    ((Hidden n) n)))
(let ((erased h)) (Hidden (Succ (Zero))))
(let ((erased k)) (peek h))
(get (None) k)
