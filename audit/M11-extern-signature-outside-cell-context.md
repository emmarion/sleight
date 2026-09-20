# M11. An extern's signature is elaborated outside the extern body's cell context

Status: observation; consistent with U12 as written.

UNIQUE.md U12: inside an extern function's body no type counts as marked
`extern` for U8's `at` rules and U9's cells. `elab_def_fns` elaborates a
function's header, its signature, from the outer environment, and only
`define` sets the in-extern flag for the body. So a `Cell` of the extern's
own type cannot appear in its telescope even though its body may build
one. U12 speaks only of the body, and no current model needs a cell in
its signature, so this looks consistent; recorded in case a future model
wants to pass a cell between externs.

Related, mild: the flag is lexical and inherited by a nested `def-fns`
inside an extern body (ASSUMPTIONS 165), confirmed by a temporary
experiment. A nested function is not itself an extern, so cells there
mint values in the model's representation rather than the FFI's; that is
unobservable only because such a function is unreachable once the FFI
implementation replaces the body enclosing it.
