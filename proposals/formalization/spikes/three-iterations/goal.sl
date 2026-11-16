(def-adts $ (OneStepThreeIterations : -> Type)
  enum
  (many MkOneStepThreeIterations : (erased (Level) step-lvl) (erased (Level) counted-lvl) (erased (Level) by-lvl) (erased (Level) total-lvl)
     (many (Fn step-lvl (erased (List (Tok)) src) (many (Scan src) s) -> (many (Stepped Scan src) r) (erased (StepsTo src s r) g)) one-step)
     (many (Fn counted-lvl (subterm many (Nat) count) (erased (List (Tok)) src) (many (Scan src) s) -> (many (Counted src) r)) under-a-counter)
     (many (Fn by-lvl (erased (List (Tok)) src) (many (Scan src) s) (subterm erased (Halts src s) h) -> (many (Verdict (Zero) src) v)) under-a-halting-derivation)
     (many (Fn total-lvl (many (List (Tok)) src) -> (many (Verdict (Zero) src) v)) total-where-halting-is-proved)
     -> (OneStepThreeIterations)))

(goal many (OneStepThreeIterations))
