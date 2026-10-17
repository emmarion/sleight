; needs: ../std/macro wide_lib
; expect: (Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Cons _ 4 $ Cons _ 5 $ Cons _ 6 $ Nil _)
; The bound is 246 constructors with fields, counting no nullary or phantom one: 246 and those beyond it
; stay below it, and 600 is past it.
(def-adts $ (At : -> Type)
  enum
  (wide ctors At At 246 2 (Nat)))

(def-adts $ (Nullary : -> Type)
  enum
  (wide ctors Nullary Nu 246 1 (Nat))
  (wide ctors Nullary Em 300 0 (Nat)))

(def-adts $ (Phantom : -> Type)
  enum
  (wide ctors Phantom Ph 246 1 (Nat))
  (erased Q0 : (many (Nat) _) -> (Phantom))
  (erased Q1 : (many (Nat) _) -> (Phantom)))

(def-adts $ (Many : -> Type)
  enum
  (wide ctors Many Mn 600 4 (Nat)))

(def-fns _ $ (many from-at : (many (At) x) -> (many (Nat) r))
  (let-match many x (At245 _ y) (else 0))
  y)

(def-fns _ $ (many from-nullary : (many (Nullary) x) -> (many (Nat) r))
  (match many x _ ((Nu245 y) y) ((Em299) 4) (else 0)))

(def-fns _ $ (many from-phantom : (many (Phantom) x) -> (many (Nat) r))
  (let-match many x (Ph245 y) (else 0))
  y)

(def-fns _ $ (many from-many : (many (Many) x) -> (many (Nat) r))
  (let-match many x (Mn599 _ _ _ y) (else 0))
  y)

(def-fns _ $ (many main : -> (many (List (Nat)) r))
  (Cons _ 1 $ Cons _ (from-at (At245 1 2)) $ Cons _ (from-nullary (Nu245 3)) $ Cons _ (from-nullary (Em299))
    $ Cons _ (from-phantom (Ph245 5)) $ Cons _ (from-many (Mn599 1 2 3 6)) $ Nil _))

main
; warns: tests/wide_threshold.sl:17:3: warning: phantom constructor `Q0` has a non-erased field
; warns: tests/wide_threshold.sl:18:3: warning: phantom constructor `Q1` has a non-erased field
