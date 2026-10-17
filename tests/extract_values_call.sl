; expect: 5
; A `values` entry that is a call to a function holding a dead one-field block. The OCaml written out
; binds the call before the tuple: ocamlopt 4.14.1 fails on the tuple built around the call with
; `Selection.size_expr`. The tests are compiled with ocamlc, which does not, so this one does not
; itself meet that failure (https://github.com/ocaml/ocaml/issues/15154).
(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (Nat) v) -> (Box)))

(def-fns _ $ (many g : (many (Nat) a) -> (many (Nat) r))
  (let ((many _)) (MkBox a))
  a)

(def-fns _ $ (many f : (many (Nat) a) -> (many (Nat) x) (many (Nat) y))
  (values (g a) a))

(def-fns _ $ (many main : -> (many (Nat) r))
  (let ((many x) (many _)) (f 5))
  x)

main
