(let ((erased b1)) (prove-literal-lt 1 5))
(let ((erased b2)) (prove-literal-lt 2 5))
(let ((erased b3)) (prove-literal-lt 3 5))
(let ((erased b4)) (prove-literal-lt 4 5))
(let ((erased b0)) (prove-literal-lt 0 5))
(let ((many srows))
  (Cons _ (MkRow 5 (Go 5 (Sym1) (Right) 1 b1) (Go 5 (Sym1) (Left) 2 b2)) $
   Cons _ (MkRow 5 (Go 5 (Sym1) (Right) 2 b2) (Go 5 (Sym1) (Right) 1 b1)) $
   Cons _ (MkRow 5 (Go 5 (Sym1) (Right) 3 b3) (Go 5 (Sym0) (Left) 4 b4)) $
   Cons _ (MkRow 5 (Go 5 (Sym1) (Left) 0 b0) (Go 5 (Sym1) (Left) 3 b3)) $
   Cons _ (MkRow 5 (Halt 5) (Go 5 (Sym0) (Left) 0 b0)) $ Nil (Row 5)))
(let ((many nr) (erased len)) (list-count _ srows))
(comptime-match many (nat-eq nr 5) (Equal _ _ _))

(def-fns _ $ (many run-champ : -> (many (Res (HaltsIn 5 (MkMachine 5 srows len) blank 47176870)) r))
  (spec-sim 5 srows len 47176870 47176870 blank (Zero) (Nil (Sym)) (Sym0) (Nil (Sym)) (LdNil 5 (MkMachine 5 srows len) blank 47176870)))
(let ((many spec-res)) (native-compute run-champ))
(comptime-match many spec-res (ROk _ champ-h))

(def-fns _ $ (erased spec-bound : (erased (Machine 5) mm) (erased (Nat) k) (erased (HaltsIn 5 mm blank k) h) -> (erased (NatLe k 47176870) le))
  (let-match erased mm (MkMachine _ rows ln))
  (let ((erased m) (erased rt)) (rt-of 5 rows))
  (MkNatLe k 47176870 (bound m (rt-rows 5 5 rows m rt ln) k
    (halts-tr 5 rows ln m rt (Zero) k (Nil (Sym)) (Nil (Sym)) (Sym0) (Nil (Bool)) (Nil (Bool)) (BFalse) (LBNil) (SB0) (LBNil) h))))

(qed (MkBusyBeaver 5 47176870 (MkMachine 5 srows len) champ-h (level-of spec-bound) spec-bound))
