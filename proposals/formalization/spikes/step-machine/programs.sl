(let ((many nat-type-id)) 10)
(let ((many zero-id)) 11)
(let ((many succ-id)) 12)
(let ((many walker-id)) 13)
(let ((many walker-param-id)) 14)
(let ((many pred-field-id)) 15)
(let ((many counter-id)) 16)

(def-fns _ $ (many one-core : (many (Core) c) -> (many (List (Core)) cs))
  (Cons _ c (Nil _)))

(def-fns _ $ (many succ-core : (many (Core) c) -> (many (Core) r))
  (CApp (CVar succ-id) (one-core c)))

(let ((many zero-core)) (CApp (CVar zero-id) (Nil _)))

(def-fns _ $ (many numeral-onto : (subterm many (Nat) n) (many (Core) acc) -> (many (Core) c))
  (let-match many n (Succ m) ((Zero) acc))
  (tail $ numeral-onto m (succ-core acc)))

(def-fns _ $ (many let-counter : (many (Core) rhs) (many (Core) rest) -> (many (Core) c))
  (CStmt (SLet (Cons _ counter-id (Nil _)) rhs) rest))

(def-fns _ $ (many count-up-then : (subterm many (Nat) n) (many (Core) rest) -> (many (Core) c))
  (let-match many n (Succ m) ((Zero) rest))
  (tail $ count-up-then m (let-counter (succ-core (CVar counter-id)) rest)))

(def-fns _ $ (many walk-nat : (many (Core) on-zero) (many (Core) on-succ) -> (many (Core) body))
  (CMatch (CVar walker-param-id)
    (Cons _ (MkBranch zero-id (Nil _) on-zero)
      (Cons _ (MkBranch succ-id (Cons _ pred-field-id (Nil _)) on-succ) (Nil _)))))

(def-fns _ $ (many call-walker : (many (Core) argument) -> (many (Core) call))
  (CCall (CVar walker-id) (one-core argument)))

(let ((many recurse-on-pred)) (call-walker (CVar pred-field-id)))
(let ((many pred-body)) (walk-nat zero-core (CVar pred-field-id)))
(let ((many double-body)) (walk-nat zero-core (succ-core (succ-core recurse-on-pred))))
(let ((many drop-body)) (walk-nat zero-core recurse-on-pred))

(def-fns _ $ (many with-walker : (many (Core) body) (many (Core) rest) -> (many (Core) program))
  (CStmt (SDefAdts (Cons _ nat-type-id (Cons _ zero-id (Cons _ succ-id (Nil _)))))
    (CStmt (SDefFns (Cons _ (MkFnDef walker-id (Cons _ walker-param-id (Nil _)) body) (Nil _))) rest)))

(def-fns _ $ (many build : (many (String) shape) (many (Nat) size) -> (many (Core) program))
  (let-match many (str-eq shape "chain-drop") (Unequal _ _ _ _ _)
    ((Equal _ _ _) (with-walker drop-body $ let-counter zero-core $ count-up-then size $ call-walker (CVar counter-id))))
  (let ((many nested)) (call-walker (numeral-onto size zero-core)))
  (let-match many (str-eq shape "double") (Unequal _ _ _ _ _) ((Equal _ _ _) (with-walker double-body nested)))
  (let-match many (str-eq shape "drop") (Unequal _ _ _ _ _) ((Equal _ _ _) (with-walker drop-body nested)))
  (with-walker pred-body nested))

(def-fns _ $ (many arg-or : (subterm many (List (String)) args) (many (Nat) index) (many (String) default) -> (many (String) arg))
  (let-match many args (Cons _ first rest) ((Nil _) default))
  (let-match many index (Succ before) ((Zero) first))
  (tail $ arg-or rest before default))

(def-fns _ $ (many parse-nat-or : (many (String) text) (many (Nat) default) -> (many (Nat) n))
  (match many (str-nat text) _
    ((Some _ n) n)
    ((None _) default)))
