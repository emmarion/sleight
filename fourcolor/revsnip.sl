; Rings of plain planar maps, after revsnip.v: the reverse ring rev (map e r), and the edges out of a proper ring. Load after
; snip.sl.

; r is a proper ring: it has more than two darts, or two darts x and y with e x other than y (proper_ring).
(def-adts $ (Proper : ((List (Nat)) e r) -> Type)
  enum
  (many ProperBig : (erased (List (Nat)) e r1) (erased (Nat) x y z) -> (Proper e (Cons (Nat) x (Cons (Nat) y (Cons (Nat) z r1)))))
  (many ProperTwo : (erased (List (Nat)) e) (erased (Nat) x y ex) (erased (Nth (Nat) e x ex) pe) (erased (Apart (Nat) Lt ex y) ne)
      -> (Proper e (Cons (Nat) x (Cons (Nat) y (Nil (Nat)))))))

(def-fns _ $ (erased map-distinct : (erased (Nat) d) (erased (List (Nat)) h hi ys) (erased (HPerm d h hi) pm) (subterm erased (List (Nat)) xs) (erased (Distinct xs) dx)
    (erased (Respects h xs ys) rp) -> (erased (Distinct ys) r))
  (let-match erased rp (RespCons _ xs1 ys1 j l pj rp1) ((RespNil _) (DistNil)))
  (let-match erased dx (DistCons _ _ oj dx1))
  (DistCons l ys1
    (match erased (in-dec l ys1) _
      (absurd (OrL _ _ il)
        (let ((erased j2) (erased ij2) (erased pj2)) (respects-in h xs1 ys1 l rp1 il))
        (let-match erased (perm-inj d j j2 l h hi pm pj pj2) (Refl _ _))
        (apart-irrefl j (notin-in j j xs1 oj ij2)))
      ((OrR _ _ o) o))
    (map-distinct d h hi ys1 pm xs1 dx1 rp1)))

(def-fns _ $ (erased some-sym : (erased (Nat) d a b) (erased (List (Nat)) f fi) (erased (HPerm d f fi) pf) (erased (SomePath f (Nil (Nat)) a b) sp) (erased (Lt a d) la)
    -> (erased (SomePath f (Nil (Nat)) b a) r))
  (let-match erased sp (MkSomePath _ _ ws _ _ w))
  (walk-back d a b f fi (Nil _) ws pf w la))

; The ring path from c through P to b, read backwards along e from e b, after the reverse Acc of what came before c, as the tail
; of RR = rev (e c :: map e P) ++ Acc.
(def-fns _ $ (erased rpath-rev : (erased (Nat) d c b ec ea) (erased (List (Nat)) e f fi mP Acc RR) (subterm erased (List (Nat)) P) (erased (HPerm d f fi) pf)
    (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (Length (Nat) e d) le) (erased (RPath e f c P b) rp) (erased (Respects e P mP) rm)
    (erased (Nth (Nat) e c ec) pc) (erased (RevApp (Nat) (Cons (Nat) ec mP) Acc RR) ra) (erased (RPath e f ec Acc ea) racc)
    -> (erased (Nat) eb) (erased (List (Nat)) Q) (erased (Eq (List (Nat)) RR (Cons (Nat) eb Q)) eq) (erased (RPath e f eb Q ea) rq))
  (let-match erased rp (RPCons _ _ P1 _ ec2 z _ pc2 sp rp1)
    ((RPNil _ _ _) (let-match erased rm (RespNil _)) (let-match erased ra (RACons _ _ _ _ _ ra1)) (let-match erased ra1 (RANil _ _))
      (values ec Acc (Refl _ RR) racc)))
  (let-match erased (nth-fn _ e c ec ec2 pc pc2) (Refl _ _))
  (let-match erased rm (RespCons _ _ mP1 _ ez pz rm1))
  (let-match erased ra (RACons _ _ _ _ _ ra1))
  (let ((erased lz)) (nth-lt-length _ e z d ez pz le))
  (let ((erased pec) (erased nec)) (plain-eq d c ec e pl (nth-lt-length _ e c d ec pc le) pc))
  (let ((erased pez) (erased nez)) (plain-eq d z ez e pl lz pz))
  (rpath-rev d z b ez ea e f fi mP1 (Cons _ ec Acc) RR P1 pf pl le rp1 rm1 pz ra1
    (RPCons e f Acc ez z ec ea pez (some-sym d ec z f fi pf sp (nth-lt-length _ e ec d c pec le)) racc)))
