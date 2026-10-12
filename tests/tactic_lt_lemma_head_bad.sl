; needs: ../std/macro ../std/nat ../std/tactics
; error: lt-lemma: the goal's head is neither the prelude's `Lt` nor std's `Le`
(lt-lemma (erased not-lt : (erased (Nat) a b c) (erased (Add a b c) h) -> (erased (Add a b c) r)))
