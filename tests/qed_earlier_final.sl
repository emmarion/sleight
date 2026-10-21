; needs: adt_sibling_param
; goal: proved
(goal many (Nat))
(qed 3)
(nat-add 2 3)
; expect: --goal proved: PASS
; stderr: tests/qed_earlier_final.sl:3:1: note: proved `(goal many (Nat))`
; stderr: tests/qed_earlier_final.sl:4:1: note: by this `qed`
