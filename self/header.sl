; self/header.sl -- the OCaml runtime every compiled program starts with: lib/ffi_core.ml and lib/driver_core.ml
; wrapped as modules, then self/runtime.ml, all read by lib/embed.sl's embed when slc is compiled.
(let ((many runtime-header))
  $ str-cat3 "[@@@warning \"-a\"]\nmodule Ffi_core = struct\n" ffi-core
  $ str-cat3 "end\nmodule Driver_core = struct\n" driver-core
  $ str-cat "end\n" $ embed "runtime.ml")
