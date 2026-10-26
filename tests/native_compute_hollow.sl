; expect: (MkDone _)
; host-path: yes
(def-adts $ (Done : -> Type) enum (erased Never : -> (Done)) (many MkDone : (erased (Nat) n) -> (Done)))
(def-fns _ $ (many finish : -> (many (Done) t)) (MkDone (Zero)))
(native-compute finish)
