# Q5. Slot-indexed user types reach DESIGN.md section 38's class merge, OPEN.md 3's deferred question

Status: open question, ASSUMPTIONS 183. Spec-faithful; nothing found that
exploits it.

## The rule

DESIGN.md section 38: a forcing unification of two `SlotHolds` "merges the
classes, `(SlotVacant)` against `(SlotHolds v)` merging `v`'s with
`null`'s, so nothing is ever refuted between two slots". OPEN.md 16 and 17 defer
`at-coercible` and `slot-eq`, which mint at-class merges from evidence,
"after a more thorough investigation of their soundness".

## The observation

An ordinary user type indexed by `(Slot)` reaches the same merge without
OPEN.md 16 and 17:

```scheme
(def-adts $ Holder : ((Slot) s) -> Type
  enum
  (many HVacant : -> (Holder (SlotVacant)))
  (many HFull : (erased (Slot) s) -> (Holder s)))

(def-fns _ $ many trick : (many (Holder (SlotHolds v)) a) (many (Holder (SlotHolds w)) b) ->
    (many (Nat) r at v)
  (match many a (((Nat) r at v))
    ((HVacant)
      (match many b (((Nat) r at v))
        ((HVacant) w)
        ((HFull _) v)))
    ((HFull _) v)))
```

is accepted: entering an `HVacant` branch under a `(Holder (SlotHolds v))`
scrutinee is not refuted, so inside the two branches `v`, `w` and `null`
share one class and `w` satisfies a promise of `at v`. To reach the branch
a program needs a value of `(Holder (SlotHolds v))` headed by `HVacant`,
and building one needs the non-forcing check, which only asks whether the
classes already coincide, so no exploit was constructed;
`tests/at_slots_force.sl` does the same through an `Eq (Slot)` parameter
that nothing can supply.

## The question

The soundness question OPEN.md 3 states, whether an at-class merge licensed by
a branch is sound in the branch's reachability, is already live for
slot-indexed types in the implemented subset. Does the argument that
justifies section 7's forced `is` facts, that a branch's facts hold in
exactly the branch that runs, carry over to at-class merges, whose
consequence is a skipped store rather than a rewrite?
