; needs: ../std/macro ../std/nat ../std/tactics
; error: lt-lemma: no chain of hypotheses reaches the goal
(lt-lemma (erased not-strict : (erased (Nat) a b c) (erased (NatLe a b) p) (erased (NatLe b c) q) -> (erased (Lt a c) r)))
