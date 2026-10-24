; needs: ../std/macro wide_lib
; expect: (Cons _ 1 $ Cons _ 2 $ Cons _ 3 $ Cons _ 4 $ Cons _ 5 $ Cons _ 6 $ Cons _ 7 $ Cons _ 8 $ Cons _ 9 $ Cons _ 10 $ Nil _)
; The bound is 244 constructors with fields, counting no nullary or phantom one: 244 and those beyond it
; stay below it, and 245 and 600 are past it.
(def-adts $ (At : -> Type)
  enum
  (wide ctors At At 244 2 (Nat)))

(def-adts $ (Nullary : -> Type)
  enum
  (wide ctors Nullary Nu 244 1 (Nat))
  (wide ctors Nullary Em 300 0 (Nat)))

(def-adts $ (Phantom : -> Type)
  enum
  (wide ctors Phantom Ph 244 1 (Nat))
  (erased Q0 : (many (Nat) _) -> (Phantom))
  (erased Q1 : (many (Nat) _) -> (Phantom)))

(def-adts $ (Past : -> Type)
  enum
  (wide ctors Past Pa 245 2 (Nat)))

(def-adts $ (PastNullary : -> Type)
  enum
  (wide ctors PastNullary Pn 245 1 (Nat))
  (wide ctors PastNullary Pe 300 0 (Nat)))

(def-adts $ (PastPhantom : -> Type)
  enum
  (wide ctors PastPhantom Pp 245 1 (Nat))
  (erased R0 : (many (Nat) _) -> (PastPhantom))
  (erased R1 : (many (Nat) _) -> (PastPhantom)))

(def-adts $ (Many : -> Type)
  enum
  (wide ctors Many Mn 600 4 (Nat)))

(def-fns _ $ (many from-at : (many (At) x) -> (many (Nat) r))
  (let-match many x (At243 _ y) (else 0))
  y)

(def-fns _ $ (many from-nullary : (many (Nullary) x) -> (many (Nat) r))
  (match many x _ ((Nu243 y) y) ((Em299) 4) (else 0)))

(def-fns _ $ (many from-phantom : (many (Phantom) x) -> (many (Nat) r))
  (let-match many x (Ph243 y) (else 0))
  y)

(def-fns _ $ (many from-past : (many (Past) x) -> (many (Nat) r))
  (let-match many x (Pa244 y) (else 0))
  y)

(def-fns _ $ (many from-past-nullary : (many (PastNullary) x) -> (many (Nat) r))
  (match many x _ ((Pn244 y) y) ((Pe299) 9) (else 0)))

(def-fns _ $ (many from-past-phantom : (many (PastPhantom) x) -> (many (Nat) r))
  (let-match many x (Pp244 y) (else 0))
  y)

(def-fns _ $ (many from-many : (many (Many) x) -> (many (Nat) r))
  (let-match many x (Mn599 _ _ _ y) (else 0))
  y)

(def-fns _ $ (many main : -> (many (List (Nat)) r))
  (Cons _ 1 $ Cons _ (from-at (At243 1 2)) $ Cons _ (from-nullary (Nu243 3)) $ Cons _ (from-nullary (Em299))
    $ Cons _ (from-phantom (Ph243 5)) $ Cons _ (from-many (Mn599 1 2 3 6))
    $ Cons _ (from-past (Pa244 7)) $ Cons _ (from-past-nullary (Pn244 8)) $ Cons _ (from-past-nullary (Pe299))
    $ Cons _ (from-past-phantom (Pp244 10)) $ Nil _))

main
; warns: tests/wide_threshold.sl:17:3: warning: phantom constructor `Q0` has a non-erased field
; warns: tests/wide_threshold.sl:18:3: warning: phantom constructor `Q1` has a non-erased field
; warns: tests/wide_threshold.sl:32:3: warning: phantom constructor `R0` has a non-erased field
; warns: tests/wide_threshold.sl:33:3: warning: phantom constructor `R1` has a non-erased field
