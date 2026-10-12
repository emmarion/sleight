; needs: ../std/macro ../std/nat ../std/tactics
; expect: "ok"
(lt-lemma (erased refl : (erased (Nat) a) -> (erased (Le a a) r)))
(lt-lemma (erased le-then-le : (erased (Nat) a b c) (erased (Le a b) p) (erased (Le b c) q) -> (erased (Le a c) r)))
(lt-lemma (erased lt-then-le : (erased (Nat) a b c) (erased (Lt a b) p) (erased (Le b c) q) -> (erased (Lt a c) r)))
(lt-lemma (erased le-then-lt : (erased (Nat) a b c) (erased (Le a b) p) (erased (Lt b c) q) -> (erased (Lt a c) r)))
(lt-lemma (erased weaken : (erased (Nat) a b) (erased (Lt a b) p) -> (erased (Le a b) r)))
(lt-lemma (erased le-succ : (erased (Nat) a) -> (erased (Le a (Succ a)) r)))
(lt-lemma (erased succ-le : (erased (Nat) a b) (erased (Le (Succ a) b) p) -> (erased (Lt a b) r)))
(lt-lemma (erased le-shift : (erased (Nat) a b) (erased (Le (Succ a) (Succ b)) p) -> (erased (Le a b) r)))
(lt-lemma (erased le-mixed : (erased (Nat) a b c) (erased (Le a (Succ b)) p) (erased (Lt (Succ b) c) q) -> (erased (Le (Succ a) c) r)))
(lt-lemma (erased long : (erased (Nat) a b c d e)
    (erased (Le d e) p4) (erased (Le a b) p1) (erased (Lt b c) p2) (erased (Le c d) p3) -> (erased (Lt a (Succ e)) r)))
(lt-lemma (erased hygienic : (erased (Nat) a b c) (erased (Le a b) p) (erased (Le b c) q)
    (erased (Nat) lt-le-trans lt-weaken LtS MkLe le-lt lt-pred lt-succ-left) -> (erased (Le a c) r)))
(def-fns _ $ (erased use : (erased (Nat) x y z) (erased (Le x y) u) (erased (Lt y z) v) -> (erased (Lt x z) r))
  (le-then-lt x y z u v))
"ok"
; warns: tests/tactic_le_lemma.sl:15:5: warning: declaration of `lt-le-trans` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/tactic_le_lemma.sl:15:5: warning: declaration of `lt-weaken` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/tactic_le_lemma.sl:15:5: warning: declaration of `LtS` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/tactic_le_lemma.sl:15:5: warning: declaration of `MkLe` shadows a previous binder
; warns: <**>std/nat.sl:<**>: note: shadowed binder is here
; warns: tests/tactic_le_lemma.sl:15:5: warning: declaration of `le-lt` shadows a previous binder
; warns: <**>std/nat.sl:<**>: note: shadowed binder is here
; warns: tests/tactic_le_lemma.sl:15:5: warning: declaration of `lt-pred` shadows a previous binder
; warns: <**>std/nat.sl:<**>: note: shadowed binder is here
; warns: tests/tactic_le_lemma.sl:15:5: warning: declaration of `lt-succ-left` shadows a previous binder
; warns: <**>std/nat.sl:<**>: note: shadowed binder is here
