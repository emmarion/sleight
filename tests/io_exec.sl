; expect: piped: exit 3 out=[out in!] err=[err]
; expect: path: exit 0 out=[bar /] err=[]
; expect: no path: Fail sh: not found on the PATH it was given
; expect: killed: Fail /bin/sh: killed by signal SIGKILL
; expect: no dir: Fail /bin/sh: /no/such/dir: No such file or directory
; expect: no file: Fail /no/such/prog: /no/such/prog: No such file or directory
; expect: big: exit 0 out=[300000] err=[]
; expect: order: exit 0 out=[a] err=[]
; expect: order: Fail sh: not found on the PATH it was given
; expect: order: exit 0 out=[b] err=[]
; expect: order: exit 0 out=[c] err=[]
; expect: serial: exit 0 out=[] err=[]
; expect: serial: exit 0 out=[12] err=[]
; expect: parallel: exit 0 out=[met] err=[]
; expect: parallel: exit 0 out=[met] err=[]
; expect: cleanup: exit 0 out=[] err=[]
; expect: zero: Fail /bin/sh: max-parallel is 0
; expect: zero: Fail /no/such/prog: max-parallel is 0
; expect: empty: no results
; expect: confine ok
; expect: fenced: Fail /bin/sh: exec needs the whole filesystem writable, which the fence does not allow
; An Exec request runs each job with exactly the arguments, environment, directory and standard input it
; names, at most max-parallel at once, and answers each job's exit code and what it wrote, in the order of
; the jobs; a job it cannot start, or one a signal kills, answers Fail, and so does every job when
; max-parallel is 0 or once the fence is narrowed.

(let ((many d0)) (lt-dec 0 u8-modulus))
(comptime-match many d0 (Yes _ _ za0 zb0 zp0))
(let ((many code0)) (MkU8 0 zp0))

(def-fns _ $ (many shown : (many (Result (Exited)) r) -> (many (String) s))
  (let-match many r (Ok _ x) ((Fail _ m) (str-append "Fail " m)))
  (let-match many x (MkExited code out err))
  (let-match many code (MkU8 n _))
  (str-append "exit " $ str-append (nat-str n) $ str-append " out=[" $ str-append out $ str-append "] err=[" $ str-append err "]"))

(def-fns _ $ (many say-all : (many (String) label) (subterm many (List (Result (Exited))) rs) (unique (World) w at vacant-slot) -> (unique (World) w2 at w))
  (let-match many rs (Cons _ r rest) ((Nil _) w))
  (let ((unique w1) (many _)) (world-do _ w (WriteOut $ str-append label $ str-append ": " $ str-append (shown r) "\n")))
  (tail $ say-all label rest w1))

(def-fns _ $ (many run : (many (String) label) (many (Maybe (Nat)) most) (many (List (ExecJob)) jobs) (unique (World) w at vacant-slot) -> (unique (World) w2 at w))
  (let ((unique w1) (many done)) (world-do _ w (Exec most jobs)))
  (let-match many done (MkExecResults _ rs _ _ _))
  (let-match many rs (Cons _ _ _) ((Nil _) (let ((unique w2) (many _)) (world-do _ w1 (WriteOut $ str-append label ": no results\n"))) w2))
  (say-all label rs w1))

(def-fns _ $ (many sh : (many (String) script) -> (many (List $ String) r))
  (Cons _ "-c" $ Cons _ script $ Nil _))

(def-fns _ $ (many var : (many (String) n) (many (String) v) -> (many (Pair (String) (String)) r))
  (MkPair _ _ n v))

(def-fns _ $ (many job : (many (String) script) -> (many (ExecJob) j))
  (MkExecJob "/bin/sh" (sh script) (Nil _) (None _) ""))

(def-fns _ $ (many one : (many (ExecJob) j) -> (many (List (ExecJob)) r))
  (Cons _ j $ Nil _))

(let ((many meet)) "touch /tmp/sleight-exec-$PPID.$0; i=0; while [ ! -e /tmp/sleight-exec-$PPID.$1 ] && [ $i -lt 200 ]; do sleep 0.05; i=$((i+1)); done; [ -e /tmp/sleight-exec-$PPID.$1 ] && printf met")
(let ((many log)) "/tmp/sleight-exec-$PPID.log")

(def-lvl P)

(def-unique P $ (unique start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program P) p))
  (let ((unique w1)) (run "piped" (None _) (one $ MkExecJob "/bin/sh" (sh "printf 'out '; printf err >&2; cat; exit 3") (Nil _) (None _) "in!") w))
  (let ((unique w2)) (run "path" (None _) (one $ MkExecJob "sh" (sh "printf '%s ' \"$FOO\"; pwd | tr -d '\\n'") (Cons _ (var "PATH" "/usr/bin:/bin") $ Cons _ (var "FOO" "bar") $ Nil _) (Some _ "/") "") w1))
  (let ((unique w3)) (run "no path" (None _) (one $ MkExecJob "sh" (sh "true") (Nil _) (None _) "") w2))
  (let ((unique w4)) (run "killed" (None _) (one $ job "kill -9 $$") w3))
  (let ((unique w5)) (run "no dir" (None _) (one $ MkExecJob "/bin/sh" (sh "true") (Nil _) (Some _ "/no/such/dir") "") w4))
  (let ((unique w6)) (run "no file" (None _) (one $ MkExecJob "/no/such/prog" (Nil _) (Nil _) (None _) "") w5))
  (let ((unique w7)) (run "big" (None _) (one $ job "head -c 300000 /dev/zero | cat - - | head -c 300000 | wc -c | tr -d ' \\n'") w6))
  (let ((unique w8)) (run "order" (Some _ 3) (Cons _ (job "sleep 0.3; printf a") $ Cons _ (MkExecJob "sh" (Nil _) (Nil _) (None _) "") $ Cons _ (job "printf b") $ Cons _ (job "sleep 0.1; printf c") $ Nil _) w7))
  (let ((unique w9)) (run "serial" (Some _ 1) (Cons _ (job $ str-append "rm -f " $ str-append log $ str-append "; sleep 0.3; printf 1 >> " log)
    $ Cons _ (job $ str-append "printf 2 >> " $ str-append log $ str-append "; cat " $ str-append log $ str-append "; rm -f " log) $ Nil _) w8))
  (let ((unique w10)) (run "parallel" (Some _ 2) (Cons _ (MkExecJob "/bin/sh" (Cons _ "-c" $ Cons _ meet $ Cons _ "a" $ Cons _ "b" $ Nil _) (Nil _) (None _) "")
    $ Cons _ (MkExecJob "/bin/sh" (Cons _ "-c" $ Cons _ meet $ Cons _ "b" $ Cons _ "a" $ Nil _) (Nil _) (None _) "") $ Nil _) w9))
  (let ((unique w11)) (run "cleanup" (None _) (one $ job "rm -f /tmp/sleight-exec-$PPID.a /tmp/sleight-exec-$PPID.b") w10))
  (let ((unique w12)) (run "zero" (Some _ 0) (Cons _ (job "true") $ Cons _ (MkExecJob "/no/such/prog" (Nil _) (Nil _) (None _) "") $ Nil _) w11))
  (let ((unique w13)) (run "empty" (Some _ 0) (Nil _) w12))
  (let ((unique w14) (many c)) (world-do _ w13 (ConfinePaths (Cons _ "." $ Nil _) (Cons _ "." $ Nil _))))
  (let ((unique w15) (many _)) (world-do _ w14 (WriteOut $ match many c (((String) _)) ((Ok _ _) "confine ok\n") ((Fail _ m) m))))
  (let ((unique w16)) (run "fenced" (None _) (one $ job "true") w15))
  (values w16 (Exit P code0)))

(Continue P start)
