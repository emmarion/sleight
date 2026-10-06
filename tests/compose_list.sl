; expect: 5
; The same composition defunctionalized: the list of functions stays data, one interpreter at level C walks
; it, and the composed function is a closure one level up that hands the list to the interpreter.

(def-lvl M)
(def-fns M $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))

(def-lvl C)
(let ((erased mc)) (prove-predates M C))
(def-fns C $ (many apply-all : (subterm many (List (Fn M (many (Nat) x) -> (many (Nat) y))) fs) (many (Nat) x) -> (many (Nat) y))
  (match many fs _
    ((Nil a) x)
    ((Cons a f rest) (f (predates mc) (notail $ apply-all (subterm (prove-subterm rest fs)) rest x)))))

(def-lvl D)
(let ((erased cd)) (prove-predates C D))
(def-fns D $ (many compose-all : (many (List (Fn M (many (Nat) x) -> (many (Nat) y))) fs) ->
    (many (Fn D (many (Nat) x) -> (many (Nat) y)) g))
  (def-fns D $ (many g : (many (Nat) x) -> (many (Nat) y))
    (apply-all (predates cd) fs x))
  g)

(let ((many h)) (compose-all (Cons (Fn M (many (Nat) x) -> (many (Nat) y)) inc (Cons (Fn M (many (Nat) x) -> (many (Nat) y)) inc (Nil (Fn M (many (Nat) x) -> (many (Nat) y)))))))
(h 3)
; warns: tests/compose_list.sl:13:59: warning: unnecessary `(subterm _)`; drop it
; warns: tests/compose_list.sl:13:25: warning: unnecessary `(predates _)`; drop it
; warns: tests/compose_list.sl:20:16: warning: unnecessary `(predates _)`; drop it
