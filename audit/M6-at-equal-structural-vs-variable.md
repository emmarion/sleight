# M6. `at_equal` structural in ML, variable-only in self

Status: observation, unreachable after F3.

`lib/env.ml`'s `at_equal` compares two location terms with full
structural `Term.equal` after taking each through the at-database.
`self/core.sl`'s `location-same` compares only `TVar`/`TBound` identity.
They differ exactly on two identical non-variable location terms. Before
F3 the newtype `place` could be a non-variable term; after it every
surviving location is a variable, and no reachable case was constructed.
The two should probably be made to agree so that a future non-variable
place cannot split them again.
