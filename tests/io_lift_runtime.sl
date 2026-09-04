; stdin: a
; stdin: bb
; expect: starting
; expect: > bb
; exit: 3
; The same embedding done at runtime, without coercion: lift rewraps every continuation in a level-B closure
; that lifts the callee's answer, one closure per request. The closures sit at B, above lift's own level.
(def-lvl C)
(def-fns C $ many lift : (erased (Level) A) (erased (Level) B) (erased (Predates (Level) A B) ab) (erased (Predates (Level) C B) cb)
    (subterm many (IO A) io) -> (many (IO B) out)
  (match many io _
    ((Exit l c) (Exit B c))
    ((WriteOut l t n) (WriteOut B t (lift A B ab cb (subterm _) n)))
    ((WriteErr l t n) (WriteErr B t (lift A B ab cb (subterm _) n)))
    ((ReadLine l k)
      (def-fns B $ many w : (many (Maybe (String)) line) -> (many (IO B) next)
        (lift (predates cb) A B ab cb (k (predates ab) line)))
      (ReadLine B w))
    ((ReadFile l p k)
      (def-fns B $ many w : (many (Result (String)) r) -> (many (IO B) next)
        (lift (predates cb) A B ab cb (k (predates ab) r)))
      (ReadFile B p w))
    ((WriteFile l p t k)
      (def-fns B $ many w : (many (Result (Unit)) r) -> (many (IO B) next)
        (lift (predates cb) A B ab cb (k (predates ab) r)))
      (WriteFile B p t w))
    ((GetArgs l k)
      (def-fns B $ many w : (many (List (String)) r) -> (many (IO B) next)
        (lift (predates cb) A B ab cb (k (predates ab) r)))
      (GetArgs B w))))

(def-lvl A)
(let (many d3) (lt-dec 3 u8-modulus))
(comptime-match d3 (Yes za3 zb3 zp3))
(let (many code3) (MkU8 3 zp3))
(let (erased str-a) (prove-predates str-lvl A))
(def-fns A $ many lib-echo : (many (Maybe (String)) line) -> (many (IO A) next)
  (match many line _
    ((None a) (Exit A code3))
    ((Some a s) (WriteOut A (str-append (predates str-a) "> " (str-append (predates str-a) s "\n")) (ReadLine A lib-echo)))))

(def-lvl B)
(let (erased a-b) (prove-predates A B))
(let (erased c-b) (prove-predates C B))
(def-fns B $ many user-start : (many (Maybe (String)) line) -> (many (IO B) next)
  (WriteOut B "starting\n" (lift (predates c-b) A B a-b c-b (ReadLine A lib-echo))))

(ReadLine B user-start)
