; needs: ../mini/base ../mini/term ../mini/canon ../mini/ctx ../mini/unify ../mini/core ../mini/elab ../mini/preserve
; expect: (BTrue)
; mini/preserve.sl is groundwork the elaborator does not need, so no other test names it and nothing
; elaborated it -- test/dune's glob copies mini/*.sl without loading them. This file loads it and asks
; nothing of it, its three functions being erased; the check is that the load succeeds, here and under slc.
(BTrue)
