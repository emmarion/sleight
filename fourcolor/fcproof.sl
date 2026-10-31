; FourColor of defs.sl, with no hypotheses, as four-color-proof: four-color-open of fcopen.sl on the unav-proof,
; all-red-proof, birkhoff-proof and cfcerts-proof that native-run computes in one native-compute. Load after embed4proof.sl, in the chain PLAN.md gives.

(native-run)
(let ((erased four-color-proof)) (four-color-open unav-proof all-red-proof birkhoff-proof cfcerts-proof))
