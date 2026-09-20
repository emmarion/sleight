# M10. Stripped-extern `array-new` is quadratic

Status: observation; U14 does not ask for complexity to be preserved.

With externs stripped, `array-new` runs its model: `n` `ACons`
constructions, each of which the FFI's `array_of` implements as an
`Array.make` plus a blit of the tail, so O(n^2) for a length-`n` array,
where the FFI does one `Array.make`. Fine for a prototype and the tests'
small arrays; a large-array test would need `; externs: only`, as
`tests/extern_comptime.sl` already does for a different reason.
