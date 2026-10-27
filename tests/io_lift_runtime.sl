; stdin: a
; stdin: bb
; expect: starting
; expect: > bb
; exit: 3
; The same embedding done at runtime, without coercion: lift rewraps every continuation in a level-B closure
; that lifts the program the callee returns, one closure per step. The closures sit at B, above lift's own
; level. The walk takes each step apart at unique, which is what lets it consume the continuation it holds
; into the closure that calls it; the extra binder in each pattern is the step's cell.
(def-lvl C)
(def-fns C $ (many lift : (erased (Level) A) (erased (Level) B) (erased (Predates (Level) A B) ab) (erased (Predates (Level) C B) cb)
    (unique (Program A) pa) -> (unique (Program B) out))
  (let-match unique pa (Continue _ k _) ((Exit _ c _) (Exit B c)))
  (def-unique B $ (unique o : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program B) p))
    (let ((unique w1) (unique next)) (k (predates ab) w))
    (values w1 (lift (predates cb) A B ab cb next)))
  (Continue B o))

(def-lvl A0)
(def-lvl A)
(let ((many d3)) (lt-dec 3 u8-modulus))
(comptime-match many d3 (Yes _ _ za3 zb3 zp3))
(let ((many code3)) (MkU8 3 zp3))
(def-fns A0 $ (many lib-echo : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program A) p))
  (let ((unique w1) (many line)) (world-do _ w (ReadLine)))
  (let-match many line (Some _ s) ((None _) (values w1 (Exit A code3))))
  (let ((unique w3) (many _)) (world-do _ w1 (WriteOut (str-append "> " (str-append s "\n")))))
  (def-unique A $ (unique again : (unique (World) v at vacant-slot) -> (unique (World) v2 at v) (unique (Program A) p)) (lib-echo v))
  (values w3 (Continue A again)))
(def-unique A $ (unique echo-start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program A) p)) (lib-echo w))

(def-lvl B)
(let ((erased a-b)) (prove-predates A B))
(let ((erased c-b)) (prove-predates C B))
(def-unique B $ (unique user-start : (unique (World) w at vacant-slot) -> (unique (World) w2 at w) (unique (Program B) p))
  (let ((unique w1) (many _)) (world-do _ w (ReadLine)))
  (let ((unique w2) (many _)) (world-do _ w1 (WriteOut "starting\n")))
  (values w2 (lift A B a-b c-b (Continue A echo-start))))

(Continue B user-start)
