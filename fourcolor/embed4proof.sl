; cfcerts-proof: notembed.sl's CfCerts for the cfs of fcopen.sl, from embed4.sl's AllGc, decided by one compiled run. Load
; after embed4.sl and fcopen.sl.

(def-fns _ $ (many embed4-run : -> (many (Checked (AllGc cfs)) r)) (allgc-c cfs))

(let ((many res)) (native-compute embed4-run))
(comptime-match many res (ChkYes _ a))
(let ((erased cfcerts-proof)) (cfcerts-of cfs a))
