; warns: tests/io_shadow_write.sl:5:12: warning: declaration of `IO` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; expect: (W "no-such-dir/shadowed" "hi" _)
(def-lvl l)
(def-adts ((IO : -> Type) enum (many E : (many (Nat) c) -> (IO)) (many B : (many (Nat) x) -> (IO))
  (many C : (many (Nat) x) -> (IO)) (many D : (many (Nat) x) -> (IO)) (many F : (many (Nat) x) -> (IO))
  (many G : (many (Nat) x) -> (IO)) (many W : (many (String) p) (many (String) t) (many (Fn l (many (Nat) r) -> (many (IO) n)) k) -> (IO))))
(def-fns l ((many k : (many (Nat) r) -> (many (IO) n)) (E 0)))
(W "no-such-dir/shadowed" "hi" k)
