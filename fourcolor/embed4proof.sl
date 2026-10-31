; cfcerts-proof: notembed.sl's CfCerts for the cfs of fcopen.sl, from embed4.sl's AllGc, decided by one native.sl job, after native-run.
; Load after embed4.sl, fcopen.sl and native.sl.

(def-fns _ $ (many embed4-run : -> (many (Checked (AllGc cfs)) r)) (allgc-c cfs))

(native-jobs cfcerts-proof (cfcerts-of cfs a) (embed4-run (ChkYes _ a)))
