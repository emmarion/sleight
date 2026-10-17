; expect: 1
; A shadowing binder the shadowed one covers earns a further note that `_` would do in its place. A binder
; covers another when it can stand for it at every use: the two canonicalize equal, so share a type, and its
; multiplicity, and where that matters its location, serve wherever the other's are needed. It is recognized
; where the new binder is erased, or where both are many and at one location. Each binder below shadows; the
; ; warns: lines at the end say which earn the note.

(def-adts $ (Sing : ((Nat) k) -> Type)
  enum
  (many MkSing : (many (Nat) k) -> (Sing k)))

(def-adts $ (B : -> Type)
  enum
  (many T : -> (B))
  (many F : -> (B)))

(def-fns _ $ (many len : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n))
  (match many xs _
    ((Nil A) (Zero))
    ((Cons A _ tl) (Succ $ notail $ len A tl))))

(def-fns _ $ (many get : (erased (Nat) n) (many (Sing n) s) -> (many n is r))
  (match many s _
    ((MkSing n) n)))

(def-fns _ $ (many keep : (unique (B) x) -> (unique (B) r))
  (match unique x _
    ((T c) (at (c)))
    (else x x)))

(def-fns _ $ (many unwrap : (many (Nat) v) (many (MkCopy (Nat) v) is c) -> (many (Nat) r at c))
  (let-match many c (MkCopy _ v))
  v)

(let ((many q)) (Zero))
(let ((many q)) (Succ q))
(let ((many q)) q)
(let ((many w)) (Zero))
(let ((erased w)) w)

(len _ (Cons _ (get _ (MkSing q)) $ Nil _))
; warns: tests/shadow_covered_warn.sl:19:11: warning: declaration of `A` shadows a previous binder
; warns: tests/shadow_covered_warn.sl:17:26: note: shadowed binder is here
; warns: tests/shadow_covered_warn.sl:19:11: note: using `_` here instead would be equivalent
; warns: tests/shadow_covered_warn.sl:20:12: warning: declaration of `A` shadows a previous binder
; warns: tests/shadow_covered_warn.sl:17:26: note: shadowed binder is here
; warns: tests/shadow_covered_warn.sl:20:12: note: using `_` here instead would be equivalent
; warns: tests/shadow_covered_warn.sl:19:11: warning: unused `A`; write `_` in its place
; warns: tests/shadow_covered_warn.sl:24:14: warning: declaration of `n` shadows a previous binder
; warns: tests/shadow_covered_warn.sl:22:26: note: shadowed binder is here
; warns: tests/shadow_covered_warn.sl:29:11: warning: declaration of `x` shadows a previous binder
; warns: tests/shadow_covered_warn.sl:26:27: note: shadowed binder is here
; warns: tests/shadow_covered_warn.sl:32:31: warning: declaration of `v` shadows a previous binder
; warns: tests/shadow_covered_warn.sl:31:29: note: shadowed binder is here
; warns: tests/shadow_covered_warn.sl:31:29: warning: `v` is referenced only in erased positions; declare it `erased`, or rename it `_v`
; warns: tests/shadow_covered_warn.sl:36:7: warning: declaration of `q` shadows a previous binder
; warns: tests/shadow_covered_warn.sl:35:7: note: shadowed binder is here
; warns: tests/shadow_covered_warn.sl:37:7: warning: declaration of `q` shadows a previous binder
; warns: tests/shadow_covered_warn.sl:36:7: note: shadowed binder is here
; warns: tests/shadow_covered_warn.sl:37:7: note: using `_` here instead would be equivalent
; warns: tests/shadow_covered_warn.sl:39:7: warning: declaration of `w` shadows a previous binder
; warns: tests/shadow_covered_warn.sl:38:7: note: shadowed binder is here
; warns: tests/shadow_covered_warn.sl:39:7: note: using `_` here instead would be equivalent
