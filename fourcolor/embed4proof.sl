; cfcerts-proof: notembed.sl's CfCerts for the cfs of fcopen.sl, from embed4.sl's AllGc of each chunk of red/chunks.sl's
; css, one native.sl job per chunk, after native-run. Load after embed4.sl, fcopen.sl and native.sl.

(native-each cfcerts-gcc css (x t r) (Checked (AllGc x)) (allgc-c x) (ChkYes _ a) (AgcCons x t a r) (AgcNil))
(native-jobs cfcerts-proof (cfcerts-of cfs (allgc-concat css cfs cl cfcerts-gcc)))
