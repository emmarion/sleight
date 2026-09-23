; expect: 2
; A same-level call in a non-erased position that carries neither tail nor notail warns, naming the mark
; that fits where it stands: count's recursion is under Succ, count-onto's is its body's last call. A
; call in an erased position, as in the erased length-proof below, does not warn. The ; warns: lines
; are at the end of the file because each names a line of it.

(def-fns _ $ (many count : (subterm many (List (Nat)) xs) -> (many (Nat) n))
  (match many xs _
    ((Nil _) (Zero))
    ((Cons _ _ rest) (Succ (count rest)))))

(def-fns _ $ (many count-onto : (subterm many (List (Nat)) xs) (many (Nat) acc) -> (many (Nat) n))
  (match many xs _
    ((Nil _) acc)
    ((Cons _ _ rest) (count-onto rest (Succ acc)))))

(def-fns _ $ (erased same : (subterm many (List (Nat)) xs) -> (erased (List (Nat)) ys))
  (match erased xs _
    ((Nil _) (Nil (Nat)))
    ((Cons _ h rest) (Cons (Nat) h (same rest)))))

(let ((many xs)) (Cons (Nat) 1 $ Nil (Nat)))
(nat-add (count xs) (count-onto xs (Zero)))
; warns: tests/same_level_warn.sl:10:28: warning: same-level call to `count` is unmarked; mark it `notail`
; warns: tests/same_level_warn.sl:15:22: warning: same-level call to `count-onto` is unmarked; mark it `tail`
