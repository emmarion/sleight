; error: SlotHolds cannot name a telescope binder
(def-fns _ $ many bad : (many (Nat) x) (erased (Eq (Slot) (SlotHolds x) (SlotVacant)) p) -> (many (Nat) r) x)
