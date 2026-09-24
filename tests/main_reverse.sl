; stdin: abc
; expect: cba!
; A String -> String program: the final expression is a function the driver runs over stdin.
; Matching a String is structural, so reversal recurses with a subterm proof.

(def-lvl R)
(def-fns R $ (many rev-onto : (subterm many (String) s) (many (String) acc) -> (many (String) t))
  (match many s _
    ((SNil) acc)
    ((SCons c rest) (tail $ rev-onto (subterm _) rest (SCons c acc)))))

(def-lvl M)
(let ((erased rev-m)) (prove-predates R M))
(let ((erased str-m)) (prove-predates str-lvl M))
(def-fns M $ (many main : (many (String) in) -> (many (String) out))
  (let ((many r)) (rev-onto (predates rev-m) in (SNil)))
  (str-append (predates str-m) (trim (predates str-m) r) (SCons #\! (SCons #\newline (SNil)))))

main
; warns: tests/main_reverse.sl:10:56: warning: application of `SCons`: copies the whole string, O(n); build a `Rope` and `flatten` it once
; warns: lib/prelude.sl:681:1: note: `;! warn` for `SCons` is here
; warns: tests/main_reverse.sl:17:59: warning: application of `SCons`: copies the whole string, O(n); build a `Rope` and `flatten` it once
; warns: lib/prelude.sl:681:1: note: `;! warn` for `SCons` is here
; warns: tests/main_reverse.sl:17:70: warning: application of `SCons`: copies the whole string, O(n); build a `Rope` and `flatten` it once
; warns: lib/prelude.sl:681:1: note: `;! warn` for `SCons` is here
