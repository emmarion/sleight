; eval-fuel: 1000
; error: out of fuel
(def-adts $ (T : -> Type) enum (many Good : -> (T)) (many Bad : (erased (False) p) -> (T)))
(def-fns _ $ (many loop : (subterm many (Nat) n) -> (many (T) r))
  (match many n _ ((Zero) (Good)) ((Succ k) (tail (loop k)))))
(let ((many x)) (loop 2000))
(comptime-match many x (Bad p))
(def-fns _ $ (erased bottom : -> (erased (False) f)) p)
