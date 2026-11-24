# Session notes (local agent: L0, AX, FRAME, TRAIN, TRAING, CONTACT, CONTACT0, ITER, IDENT, SWEEP3, BIGJ, BIGJC)

Working files: bb/l3c10-local.sl (macros), bb/l3c10-local-tbl.sl (generated frame table, notes-local/gen-tbl.py
from the drvL `frames` dump), bb/l3c10-local-h.sl (oracle harness `mmain`: kind-3 records carry Rocq's macro index).
Scratch: /tmp/claude-0/local (drvL in oc/, bld.sh, hm.txt = `drvL hm 0 40035 hm.txt 0,1,12,...`).

Status:
- L0, AX, FRAME: framed simulator (sim6 port) + certificates by native-compute; 3141/3141 in-situ instances match.
- SWEEP3: proven (start3 cell episode + c-sw0 trips); 769/769 match.
- ITER, IDENT: proven (RdK chains via rd-run, c-apply; IDENT adds wtk/tokz re-tokenization); 641/641 and 168/168.
- CONTACT: proven (contact-round cell episodes c-m1, c-m11*, c-m011* + l3round merge/tturn/sw-push/desc/walk); 805/805.
