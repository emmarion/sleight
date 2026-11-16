(def-fns _ $ (many outcome : (many (Core) program) -> (many (String) line))
  (let ((many stepped) (many steps)) (step-many _ _ 1000 (load program) 0))
  (match many stepped _
    ((Next _ _ _) "still running\n")
    ((Halted _ _ result) (report _ _ result "steps" steps))))

(let ((many unbound-variable)) (CVar 99))
(let ((many atom-called)) (with-walker pred-body (CCall (CVar zero-id) (Nil _))))
(let ((many missing-branch)) (with-walker (CMatch (CVar walker-param-id) (Nil _)) (call-walker zero-core)))
(let ((many wrong-arity)) (with-walker pred-body (CCall (CVar walker-id) (Nil _))))
(let ((many two-values-as-argument)) (with-walker pred-body (call-walker (CValues (Cons _ zero-core (Cons _ zero-core (Nil _)))))))
(str-append (outcome unbound-variable) $ str-append (outcome atom-called) $ str-append (outcome missing-branch)
  $ str-append (outcome wrong-arity) $ str-append (outcome two-values-as-argument) (outcome (with-walker pred-body (call-walker zero-core))))
