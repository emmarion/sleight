; expect: piped: exit 3 out=[out in!] err=[err]
; expect: path: exit 0 out=[bar /] err=[]
; expect: no path: Fail sh: not found on the PATH it was given
; expect: killed: Fail /bin/sh: killed by signal SIGKILL
; expect: no dir: Fail /bin/sh: /no/such/dir: No such file or directory
; expect: no file: Fail /no/such/prog: /no/such/prog: No such file or directory
; expect: big: exit 0 out=[300000] err=[]
; expect: confine ok
; expect: fenced: Fail /bin/sh: exec needs the whole filesystem writable, which the fence does not allow
; An Exec request runs a program with exactly the arguments, environment, directory and standard input it
; names, and answers its exit code and what it wrote; a program it cannot start, or one a signal kills,
; answers Fail, and so does every Exec once the fence is narrowed.

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns _ $ (many shown : (many (Result (Exited)) r) -> (many (String) s))
  (let-match many r (Ok _ x) ((Fail _ m) (str-append "Fail " m)))
  (let-match many x (MkExited code out err))
  (let-match many code (MkU8 n _))
  (str-append "exit " $ str-append (nat-str n) $ str-append " out=[" $ str-append out $ str-append "] err=[" $ str-append err "]"))

(def-fns _ $ (many run : (many (String) label) (unique (World) w at vacant-slot) (unique (Request (Result (Exited))) req) -> (unique (World) w2 at w))
  (let ((unique w1) (many r)) (world-do _ w req))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteOut $ str-append label $ str-append ": " $ str-append (shown r) "\n")))
  w2)

(def-fns _ $ (many sh : (many (String) script) -> (many (List $ String) r))
  (Cons _ "-c" $ Cons _ script $ Nil _))

(def-fns _ $ (many var : (many (String) n) (many (String) v) -> (many (Pair (String) (String)) r))
  (MkPair _ _ n v))

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1)) (run "piped" w (Exec "/bin/sh" (sh "printf 'out '; printf err >&2; cat; exit 3") (Nil _) (None _) "in!")))
  (let ((unique w2)) (run "path" w1 (Exec "sh" (sh "printf '%s ' \"$FOO\"; pwd | tr -d '\\n'") (Cons _ (var "PATH" "/usr/bin:/bin") $ Cons _ (var "FOO" "bar") $ Nil _) (Some _ "/") "")))
  (let ((unique w3)) (run "no path" w2 (Exec "sh" (sh "true") (Nil _) (None _) "")))
  (let ((unique w4)) (run "killed" w3 (Exec "/bin/sh" (sh "kill -9 $$") (Nil _) (None _) "")))
  (let ((unique w5)) (run "no dir" w4 (Exec "/bin/sh" (sh "true") (Nil _) (Some _ "/no/such/dir") "")))
  (let ((unique w6)) (run "no file" w5 (Exec "/no/such/prog" (Nil _) (Nil _) (None _) "")))
  (let ((unique w7)) (run "big" w6 (Exec "/bin/sh" (sh "head -c 300000 /dev/zero | cat - - | head -c 300000 | wc -c | tr -d ' \\n'") (Nil _) (None _) "")))
  (let ((unique w8) (many c)) (world-do _ w7 (ConfinePaths (Cons _ "." $ Nil _) (Cons _ "." $ Nil _))))
  (let ((unique w9) (many _)) (world-do _ w8 (WriteOut $ match many c (((String) _)) ((Ok _ _) "confine ok\n") ((Fail _ m) m))))
  (let ((unique w10)) (run "fenced" w9 (Exec "/bin/sh" (sh "true") (Nil _) (None _) "")))
  (values w10 (Exit P code0)))

(Continue P start)
