(def-adts $ (Tok : -> Type)
  enum
  (many Open : -> (Tok))
  (many Close : -> (Tok)))

(def-adts $ (Accepts : ((Nat) depth) ((List (Tok)) src) -> Type)
  enum
  (many AccEnd : -> (Accepts (Zero) (Nil (Tok))))
  (many AccOpen : (erased (Nat) d) (erased (List (Tok)) ts) (erased (Accepts (Succ d) ts) p) -> (Accepts d (Cons (Tok) (Open) ts)))
  (many AccClose : (erased (Nat) d) (erased (List (Tok)) ts) (erased (Accepts d ts) p) -> (Accepts (Succ d) (Cons (Tok) (Close) ts))))

(def-adts $ (Fails : ((Nat) depth) ((List (Tok)) src) -> Type)
  enum
  (many FailUnclosed : (erased (Nat) d) -> (Fails (Succ d) (Nil (Tok))))
  (many FailExtraClose : (erased (List (Tok)) ts) -> (Fails (Zero) (Cons (Tok) (Close) ts)))
  (many FailOpen : (erased (Nat) d) (erased (List (Tok)) ts) (erased (Fails (Succ d) ts) p) -> (Fails d (Cons (Tok) (Open) ts)))
  (many FailClose : (erased (Nat) d) (erased (List (Tok)) ts) (erased (Fails d ts) p) -> (Fails (Succ d) (Cons (Tok) (Close) ts))))

(def-adts $ (Verdict : ((Nat) depth) ((List (Tok)) src) -> Type)
  enum
  (many Accepted : (erased (Nat) d) (erased (List (Tok)) ts) (erased (Accepts d ts) p) -> (Verdict d ts))
  (many Rejected : (erased (Nat) d) (erased (List (Tok)) ts) (erased (Fails d ts) p) -> (Verdict d ts)))

(def-adts $ (EitherAcceptedOrRejected : -> Type)
  enum
  (many MkEither : (erased (Level) L)
     (many (Fn L (many (Nat) d) (subterm many (List (Tok)) ts) -> (many (Verdict d ts) v)) decide)
     -> (EitherAcceptedOrRejected)))

(def-adts $ (NeverBoth : -> Type)
  enum
  (many MkNeverBoth : (erased (Level) L)
     (erased (Fn L (erased (Nat) d) (erased (List (Tok)) ts) (subterm erased (Accepts d ts) p) (erased (Fails d ts) q) -> (erased (False) f)) exclusive)
     -> (NeverBoth)))

(def-adts $ (Theorem : -> Type)
  enum
  (many MkTheorem : (many (EitherAcceptedOrRejected) total) (erased (NeverBoth) exclusive) -> (Theorem)))

(goal many (Theorem))
