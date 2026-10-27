; needs: ../std/macro ../std/nat ../std/tactics
; error: lt-lemma: no chain of hypotheses reaches the goal
(lt-lemma (erased le-cycle : (erased (Nat) a b) (erased (NatLe a b) p) (erased (NatLe b a) q) -> (erased (False) r)))
