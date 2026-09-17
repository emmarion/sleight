; needs: list
; expect: 5
; A small expression evaluator over Nats with an environment: 2 * 2 + 1 with x = 2.

(def-fns _ $ many add : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) c)
  (match many a _
    ((Zero) b)
    ((Succ k) (Succ (add (subterm _) k b)))))

(def-fns _ $ many mul : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) c)
  (match many a _
    ((Zero) (Zero))
    ((Succ k) (add (predates _) b (mul (subterm _) k b)))))

(def-adts $ Expr : -> Type
  enum
  (many Lit : (many (Nat) n) -> (Expr))
  (many Var0 : -> (Expr))
  (many Add : (many (Expr) a) (many (Expr) b) -> (Expr))
  (many Mul : (many (Expr) a) (many (Expr) b) -> (Expr)))

(def-fns _ $ many eval : (subterm many (Expr) e) (many (Nat) x) -> (many (Nat) v)
  (match many e _
    ((Lit n) n)
    ((Var0) x)
    ((Add a b) (add (predates _) (eval (subterm _) a x) (eval (subterm _) b x)))
    ((Mul a b) (mul (predates _) (eval (subterm _) a x) (eval (subterm _) b x)))))

(let (many two) (Succ (Succ (Zero))))
(eval (Add (Mul (Var0) (Var0)) (Lit (Succ (Zero)))) two)
