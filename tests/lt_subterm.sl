; expect: 0
; Lt a b and Subterm (Nat) a (Nat) b each derive the other as erased functions, so on Nat the subterm
; order is the strict order. lt-sub recurses on b through le-split, which splits Lt a (Succ b1) into
; a = b1 or Lt a b1; sub-lt decides a < b and refutes the other case through loop, whose self-call
; the reflexive proof itself licenses, so the checker accepts Subterm x x as refuting.

(def-adts $ (NatEq : ((Nat) a) ((Nat) b) -> Type)
  enum
  (many NatRefl : (erased (Nat) x) -> (NatEq x x)))

(def-adts $ (Or : (Type A) (Type B) -> Type)
  enum
  (many Left : (erased Type A) (erased Type B) (erased A x) -> (Or A B))
  (many Right : (erased Type A) (erased Type B) (erased B y) -> (Or A B)))

(def-lvl L)
(let ((erased nl)) (prove-predates nat-lvl L))

(def-fns L $ (erased absurd explode : (erased Type A) (erased (False) f) -> (erased A a))
  f)

(def-fns L $ (erased loop : (subterm erased (Nat) x) (erased (Subterm (Nat) x (Nat) x) q) -> (erased (False) f))
  (loop (subterm q) x q))

(def-fns L $ (erased le-split : (subterm erased (Nat) b1) (erased (Nat) a) (erased (Lt a (Succ b1)) p) ->
    (erased (Or (NatEq a b1) (Lt a b1)) r))
  (match erased p _
    ((LtZ b2)
      (match erased b1 _
        ((Zero) (Left (NatEq a b1) (Lt a b1) (NatRefl a)))
        ((Succ b3) (Right (NatEq a b1) (Lt a b1) (LtZ b3)))))
    ((LtS a1 b2 p1)
      (let-match erased b1 (Succ b3) (absurd (Zero) p1))
      (let-match erased (le-split (subterm _) b3 a1 p1) (Left A B e)
        ((Right A B l) (Right (NatEq a b1) (Lt a b1) (LtS a1 b3 l))))
      (match erased e _ ((NatRefl z) (Left (NatEq a b1) (Lt a b1) (NatRefl a)))))))

(def-fns L $ (erased lt-sub : (subterm erased (Nat) b) (erased (Nat) a) (erased (Lt a b) p) ->
    (erased (Subterm (Nat) a (Nat) b) q))
  (let-match erased b (Succ b1) (absurd (Zero) p))
  (let-match erased (le-split (subterm (prove-subterm b1 b)) b1 a p) (Left A B e)
    ((Right A B l) (subterm-trans (lt-sub (subterm _) b1 a l) (prove-subterm b1 b))))
  (match erased e _ ((NatRefl z) (prove-subterm a b))))

(def-lvl M)
(let ((erased nm)) (prove-predates nat-lvl M))
(let ((erased lm)) (prove-predates L M))

(def-fns M $ (erased sub-lt : (erased (Nat) a) (erased (Nat) b) (erased (Subterm (Nat) a (Nat) b) q) ->
    (erased (Lt a b) l))
  (let-match erased (lt-dec (predates nm) a b) (No x y r) ((Yes x y p) p))
  (let-match erased (le-split (predates lm) a b r) (Left A B e)
    ((Right A B l)
      (explode (predates lm) (Lt a b)
        (loop (predates lm) a (subterm-trans q (lt-sub (predates lm) a b l))))))
  (match erased e _
    ((NatRefl z) (explode (predates lm) (Lt a b) (loop (predates lm) a q)))))

(Zero)
; warns: tests/lt_subterm.sl:34:35: warning: unnecessary `(subterm _)`; drop it
; warns: tests/lt_subterm.sl:41:31: warning: unnecessary `(subterm _)`; drop it
; warns: tests/lt_subterm.sl:42:43: warning: unnecessary `(subterm _)`; drop it
; warns: tests/lt_subterm.sl:51:29: warning: unnecessary `(predates _)`; drop it
; warns: tests/lt_subterm.sl:52:31: warning: unnecessary `(predates _)`; drop it
; warns: tests/lt_subterm.sl:57:56: warning: unnecessary `(predates _)`; drop it
; warns: tests/lt_subterm.sl:57:27: warning: unnecessary `(predates _)`; drop it
; warns: tests/lt_subterm.sl:55:56: warning: unnecessary `(predates _)`; drop it
; warns: tests/lt_subterm.sl:55:15: warning: unnecessary `(predates _)`; drop it
; warns: tests/lt_subterm.sl:54:16: warning: unnecessary `(predates _)`; drop it
