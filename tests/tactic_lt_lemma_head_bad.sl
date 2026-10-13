; needs: ../std/macro ../std/nat ../std/tactics
; error: lt-lemma: the goal's head is not the prelude's `Lt` or `False`, or std's `Le` or `Ne`
(lt-lemma (erased not-lt : (erased (Nat) a b c) (erased (Add a b c) h) -> (erased (Add a b c) r)))
