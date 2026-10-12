; needs: ../std/macro ../std/tactics
; error: lt-lemma: the goal's head is not the prelude's `Lt`
(lt-lemma (erased not-lt : (erased (Nat) a b c) (erased (Add a b c) h) -> (erased (Add a b c) r)))
