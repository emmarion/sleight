; stdin: !
; expect: ababab!
; A String -> String program applying a closure a factory returned at the top level: it captures the factory's
; parameter and recurses on itself, so extraction must carry it with its environment (ASSUMPTIONS.md 61).

(def-lvl F)
(def-fns F $ (many rep-factory : (many (String) p) -> (erased (Level) L) (many (Fn L (subterm many (Nat) n) -> (many (String) t)) f))
  (def-lvl L)
  (let ((erased sp)) (prove-predates str-lvl L))
  (def-fns L $ (many rep : (subterm many (Nat) n) -> (many (String) t))
    (match many n _
      ((Zero) (SNil))
      ((Succ k) (str-append (predates sp) p (rep (subterm _) k)))))
  (values L rep))

(let ((erased L) (many rep-ab)) (rep-factory "ab"))
(def-lvl M)
(let ((erased lm)) (prove-predates L M))
(let ((erased sm)) (prove-predates str-lvl M))
(def-fns M $ (many main : (many (String) in) -> (many (String) out))
  (str-append (predates sm) (rep-ab (predates lm) 3) (str-append (predates sm) in "\n")))

main
