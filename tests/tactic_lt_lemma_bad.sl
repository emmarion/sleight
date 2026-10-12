; needs: ../std/macro ../std/tactics
; error: lt-lemma: no chain of hypotheses reaches the goal
(lt-lemma (erased needs-lts : (erased (Nat) a b) (erased (Lt a b) h) -> (erased (Lt (Succ a) (Succ b)) r)))
