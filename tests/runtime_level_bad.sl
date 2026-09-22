; error: was not in scope when level Z was minted
; compose_list_dynamic.sl's composition called from a function at level Z: the composed function's level N is
; minted inside the call, after Z, so prove-predates refuses N against Z and h cannot be called from Z.

(def-lvl M)
(def-fns M $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))

(def-lvl C)
(def-fns C $ (many compose-all : (subterm many (List (Fn M (many (Nat) x) -> (many (Nat) y))) fs) ->
    (erased (Level) N) (many (Fn N (many (Nat) x) -> (many (Nat) y)) g))
  (match many fs _
    ((Nil a)
      (def-lvl N)
      (def-fns N $ (many id : (many (Nat) x) -> (many (Nat) y)) x)
      (values N id))
    ((Cons a f rest)
      (let ((erased N1) (many g1)) (compose-all (subterm (prove-subterm rest fs)) rest))
      (def-lvl N)
      (let ((erased p1)) (prove-predates N1 N))
      (let ((erased pm)) (prove-predates M N))
      (def-fns N $ (many g : (many (Nat) x) -> (many (Nat) y))
        (f (predates pm) (g1 (predates p1) x)))
      (values N g))))

(def-lvl Z)
(let ((erased cz)) (prove-predates C Z))
(def-fns Z $ (many main : -> (many (Nat) r))
  (let ((erased N) (many h)) (compose-all (predates cz) (Cons (Fn M (many (Nat) x) -> (many (Nat) y)) inc (Nil (Fn M (many (Nat) x) -> (many (Nat) y))))))
  (let ((erased nz)) (prove-predates N Z))
  (h (predates nz) 3))
main
