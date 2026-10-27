(let ((erased b1)) (prove-literal-lt 1 4))
(let ((erased b2)) (prove-literal-lt 2 4))
(let ((erased b3)) (prove-literal-lt 3 4))
(let ((erased b0)) (prove-literal-lt 0 4))
(let ((many srows))
  (Cons _ (MkRow 4 (Go 4 (Sym1) (Right) 1 b1) (Go 4 (Sym1) (Left) 1 b1)) $
   Cons _ (MkRow 4 (Go 4 (Sym1) (Left) 0 b0) (Go 4 (Sym0) (Left) 2 b2)) $
   Cons _ (MkRow 4 (Halt 4) (Go 4 (Sym1) (Left) 3 b3)) $
   Cons _ (MkRow 4 (Go 4 (Sym1) (Right) 3 b3) (Go 4 (Sym0) (Right) 0 b0)) $ Nil (Row 4)))
(let ((many nr) (erased len)) (list-count _ srows))
(comptime-match many (nat-eq nr 4) (Equal _ _ _))

(def-fns _ $ (many run-champ : -> (many (Res (HaltsIn 4 (MkMachine 4 srows len) blank 107)) r))
  (let-match many (spec-sim 4 srows len 200 (Zero) (Nil (Sym)) (Sym0) (Nil (Sym))) (SSHalt _ _ _ k hs) ((SSNo _ _ _) (RFail _)))
  (let-match many (nat-eq k 107) (Equal _ _ _) (else (RFail _)))
  (ROk _ hs))
(let ((many cres)) (native-compute run-champ))
(comptime-match many cres (ROk _ champ-h))

(def-fns _ $ (erased spec-bound : (erased (Machine 4) mm) (erased (Nat) k) (erased (HaltsIn 4 mm blank k) h) -> (erased (NatLe k 107) le))
  (let-match erased mm (MkMachine _ rows ln))
  (let ((erased m) (erased rt)) (rt-of 4 rows))
  (MkNatLe k 107 (bound m (rt-rows 4 4 rows m rt ln) k
    (halts-tr 4 rows ln m rt (Zero) k (Nil (Sym)) (Nil (Sym)) (Sym0) (Nil (Bool)) (Nil (Bool)) (BFalse) (LBNil) (SB0) (LBNil) h))))

(qed (MkBusyBeaver 4 107 (MkMachine 4 srows len) champ-h (level-of spec-bound) spec-bound))
