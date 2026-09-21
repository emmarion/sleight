; error: expected VCons, got (VNil _)
; A comptime-match mismatch on an indexed type prints the value through its type, the constructors' return
; types unified with it and the opened objects merged as entering a branch does.

(def-adts
  (Vec : (Type A) ((Nat) n) -> Type
    enum
    (many VNil : (erased Type A) -> (Vec A (Zero)))
    (many VCons : (erased Type A) (erased (Nat) n) (many A x) (many (Vec A n) rest) -> (Vec A (Succ n)))))

(let (many v) (VNil (Nat)))
(comptime-match many v (VCons a n x rest))
