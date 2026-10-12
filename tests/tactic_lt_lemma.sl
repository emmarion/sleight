; needs: ../std/macro ../std/tactics
; expect: "ok"
(lt-lemma (erased chain3 : (erased (Nat) a b c d e)
    (erased (Lt c d) h3) (erased (Lt a e) junk) (erased (Lt a b) h1 h2) (erased (Lt b c) h4) -> (erased (Lt a d) r)))
(lt-lemma (erased succ-goal : (erased (Nat) a b) (erased (Lt a b) h) -> (erased (Lt a (Succ b)) r)))
(lt-lemma (erased succ-hyp : (erased (Nat) a b) (erased (Lt (Succ a) b) h) -> (erased (Lt a b) r)))
(lt-lemma (erased succ-only : (erased (Nat) a) -> (erased (Lt a (Succ (Succ a))) r)))
(lt-lemma (erased mixed : (erased (Nat) a b c) (erased (Lt (Succ a) b) h1) (erased (Lt b c) h2) -> (erased (Lt a (Succ c)) r)))
(lt-lemma (erased hygienic : (erased (Nat) a b) (erased (Lt a b) h) (erased (Nat) lt-succ lt-trans def-fns compile-error) ->
    (erased (Lt a (Succ (Succ b))) r)))
(let ((many S)) Succ)
(lt-lemma (erased aliased : (erased (Nat) a b) (erased (Lt a b) h) -> (erased (Lt a (S b)) r)))
(def-fns _ $ (erased use-chain3 : (erased (Nat) a b c d) (erased (Lt a b) x) (erased (Lt b c) y) (erased (Lt c d) z) ->
    (erased (Lt a d) r))
  (chain3 a b c d b z x x x y))
"ok"
; warns: tests/tactic_lt_lemma.sl:9:69: warning: declaration of `lt-succ` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/tactic_lt_lemma.sl:9:69: warning: declaration of `lt-trans` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: tests/tactic_lt_lemma.sl:9:69: warning: declaration of `def-fns` shadows a built-in
; warns: tests/tactic_lt_lemma.sl:9:69: warning: declaration of `compile-error` shadows a built-in
