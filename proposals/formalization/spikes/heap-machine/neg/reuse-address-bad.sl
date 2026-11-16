(let ((erased b0)) (MkBlock 0 (Nil (Word))))
(let ((erased h1)) (HCons 7 b0 (HNil)))
(let ((erased reuse))
  (MkAlloc h1 7 b0 (FreshCons 7 7 b0 (HNil) (NeqLt 7 7 (prove-literal-lt 7 7)) (FreshNil 7))))
