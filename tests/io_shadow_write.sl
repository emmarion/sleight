; expect: (W "no-such-dir/shadowed" "hi" _)
(def-lvl l)
(def-adts ((Program : -> Type) enum (many E : (many (Nat) c) -> (Program)) (many B : (many (Nat) x) -> (Program))
  (many C : (many (Nat) x) -> (Program)) (many D : (many (Nat) x) -> (Program)) (many F : (many (Nat) x) -> (Program))
  (many G : (many (Nat) x) -> (Program)) (many W : (many (String) p) (many (String) t) (many (Fn l (many (Nat) r) -> (many (Program) n)) k) -> (Program))))
(def-fns l ((many k : (many (Nat) _r) -> (many (Program) n)) (E 0)))
(W "no-such-dir/shadowed" "hi" k)
; warns: tests/io_shadow_write.sl:3:12: warning: declaration of `Program` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
