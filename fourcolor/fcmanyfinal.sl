; The goal FourColorM of fcmany.sl, by paint.sl's four-color-m on fcproof.sl's four-color-proof. Load after fcproof.sl,
; paint.sl and fcmany.sl.

(let ((erased L) (many thm)) (four-color-m four-color-proof))
(qed (MkFourColorM L thm))
