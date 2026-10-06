; needs: list
; expect: 5
; A small expression evaluator over Nats with an environment: 2 * 2 + 1 with x = 2.

(def-fns _ $ (many plus : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (match many a _
    ((Zero) b)
    ((Succ k) (Succ (notail $ plus (subterm _) k b)))))

(def-fns _ $ (many times : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) c))
  (match many a _
    ((Zero) (Zero))
    ((Succ k) (plus (predates _) b (notail $ times (subterm _) k b)))))

(def-adts $ (Expr : -> Type)
  enum
  (many Lit : (many (Nat) n) -> (Expr))
  (many Var0 : -> (Expr))
  (many EAdd : (many (Expr) a) (many (Expr) b) -> (Expr))
  (many EMul : (many (Expr) a) (many (Expr) b) -> (Expr)))

(def-fns _ $ (many eval : (subterm many (Expr) e) (many (Nat) x) -> (many (Nat) v))
  (match many e _
    ((Lit n) n)
    ((Var0) x)
    ((EAdd a b) (plus (predates _) (notail $ eval (subterm _) a x) (notail $ eval (subterm _) b x)))
    ((EMul a b) (times (predates _) (notail $ eval (subterm _) a x) (notail $ eval (subterm _) b x)))))

(let ((many two)) (Succ (Succ (Zero))))
(eval (EAdd (EMul (Var0) (Var0)) (Lit (Succ (Zero)))) two)
; warns: tests/interp.sl:8:36: warning: unnecessary `(subterm _)`; drop it
; warns: tests/interp.sl:13:52: warning: unnecessary `(subterm _)`; drop it
; warns: tests/interp.sl:13:21: warning: unnecessary `(predates _)`; drop it
; warns: tests/interp.sl:26:51: warning: unnecessary `(subterm _)`; drop it
; warns: tests/interp.sl:26:83: warning: unnecessary `(subterm _)`; drop it
; warns: tests/interp.sl:26:23: warning: unnecessary `(predates _)`; drop it
; warns: tests/interp.sl:27:52: warning: unnecessary `(subterm _)`; drop it
; warns: tests/interp.sl:27:84: warning: unnecessary `(subterm _)`; drop it
; warns: tests/interp.sl:27:24: warning: unnecessary `(predates _)`; drop it
