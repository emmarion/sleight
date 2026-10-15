import Minimal.Strip

namespace Minimal

mutual
def Core.beq : Core → Core → Bool
  | .ret a, .ret b => a == b
  | .call f d a e m v r, .call f' d' a' e' m' v' r' =>
    f == f' && d == d' && a == a' && e == e' && m == m' && v == v' && r.beq r'
  | .mtch s R bs el e r, .mtch s' R' bs' el' e' r' =>
    s == s' && R == R' && Core.brsBeq bs bs' && Core.optBeq el el' && e == e' && r.beq r'
  | .prim p e r, .prim p' e' r' => p == p' && e == e' && r.beq r'
  | .defLvl r, .defLvl r' => r.beq r'
  | .defFns g r, .defFns g' r' => g == g' && r.beq r'
  | .chk k a b r, .chk k' a' b' r' => k == k' && a == a' && b == b' && r.beq r'
  | .case s bs el e n, .case s' bs' el' e' n' =>
    s == s' && Core.brsBeq bs bs' && Core.optBeq el el' && e == e' && n == n'
  | .seq R b r, .seq R' b' r' => R == R' && b.beq b' && r.beq r'
  | .absurd b, .absurd b' => b.beq b'
  | .dead, .dead => true
  | _, _ => false

def Core.brsBeq : List Br → List Br → Bool
  | [], [] => true
  | (n, c, k, b) :: t, (n', c', k', b') :: t' => n == n' && c == c' && k == k' && b.beq b' && Core.brsBeq t t'
  | _, _ => false

def Core.optBeq : Option Core → Option Core → Bool
  | none, none => true
  | some a, some b => a.beq b
  | _, _ => false
end

mutual
theorem Core.beq_eq : ∀ {a b : Core}, a.beq b = true → a = b
  | .ret _, b, h => by cases b <;> simp_all [Core.beq]
  | .call .., b, h => by
    cases b <;> simp only [Core.beq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, h⟩ := h
    rw [Core.beq_eq h]
  | .mtch .., b, h => by
    cases b <;> simp only [Core.beq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩, rfl⟩, h3⟩ := h
    rw [Core.brsBeq_eq h1, Core.optBeq_eq h2, Core.beq_eq h3]
  | .prim .., b, h => by
    cases b <;> simp only [Core.beq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    rw [Core.beq_eq h]
  | .defLvl _, b, h => by
    cases b <;> simp only [Core.beq, Bool.false_eq_true] at h
    rw [Core.beq_eq h]
  | .defFns .., b, h => by
    cases b <;> simp only [Core.beq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    obtain ⟨rfl, h⟩ := h
    rw [Core.beq_eq h]
  | .chk .., b, h => by
    cases b <;> simp only [Core.beq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, h⟩ := h
    rw [Core.beq_eq h]
  | .case .., b, h => by
    cases b <;> simp only [Core.beq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    obtain ⟨⟨⟨⟨rfl, h1⟩, h2⟩, rfl⟩, rfl⟩ := h
    rw [Core.brsBeq_eq h1, Core.optBeq_eq h2]
  | .seq .., b, h => by
    cases b <;> simp only [Core.beq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    obtain ⟨⟨rfl, h1⟩, h2⟩ := h
    rw [Core.beq_eq h1, Core.beq_eq h2]
  | .absurd _, b, h => by
    cases b <;> simp only [Core.beq, Bool.false_eq_true] at h
    rw [Core.beq_eq h]
  | .dead, b, h => by cases b <;> simp_all [Core.beq]

theorem Core.brsBeq_eq : ∀ {a b : List Br}, Core.brsBeq a b = true → a = b
  | [], b, h => by cases b <;> simp_all [Core.brsBeq]
  | (_, _, _, _) :: _, b, h => by
    rcases b with _ | ⟨⟨_, _, _, _⟩, _⟩ <;> simp only [Core.brsBeq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, h1⟩, h2⟩ := h
    rw [Core.beq_eq h1, Core.brsBeq_eq h2]

theorem Core.optBeq_eq : ∀ {a b : Option Core}, Core.optBeq a b = true → a = b
  | none, b, h => by cases b <;> simp_all [Core.optBeq]
  | some _, b, h => by
    cases b <;> simp only [Core.optBeq, Bool.false_eq_true] at h
    rw [Core.beq_eq h]
end

def addBody (s p d e : Nat) : Core :=
  .case (.fv p)
    [(1, 1, .vc d 1 .nil,
      .call (.fv s) .none (.ofList [.fv (p + 2), .fv (p + 1)]) false [false, true] (some [false, false, false, true])
        (.chk .rt (.fv (p + 3)) .nil
          (.ret (.ofList [.app (.vc d 1 .nil) (.ofList [.fv (p + 3)]),
            .app (.vc e 1 .nil) (.ofList [.fv (p + 2), .fv (p + 1), .fv (p + 3), .fv (p + 4)])])))),
     (0, 0, .vc d 0 .nil, .ret (.ofList [.fv (p + 1), .app (.vc e 0 .nil) (.ofList [.fv (p + 1)])]))]
    none false false

def addProof (s p d : Nat) : Core → Option Nat
  | .case (.fv p0) [(1, 1, .vc d1 1 .nil, .call (.fv s0) .none args false [false, true] (some [false, false, false, true])
        (.chk .rt q .nil (.ret ts))), (0, 0, .vc d0 0 .nil, .ret ts0)] none false false =>
    match ts0 with
    | .cons b (.cons (.app (.vc e 0 .nil) pb) .nil) =>
      if p0 = p ∧ d1 = d ∧ s0 = s ∧ args = .ofList [.fv (p + 2), .fv (p + 1)] ∧ q = .fv (p + 3) ∧
        ts = .ofList [.app (.vc d 1 .nil) (.ofList [.fv (p + 3)]),
          .app (.vc e 1 .nil) (.ofList [.fv (p + 2), .fv (p + 1), .fv (p + 3), .fv (p + 4)])] ∧
        d0 = d ∧ b = .fv (p + 1) ∧ pb = .ofList [.fv (p + 1)] then some e else none
    | _ => none
  | _ => none

theorem addProof_spec {s p d e : Nat} {c : Core} (h : addProof s p d c = some e) : c = addBody s p d e := by
  unfold addProof at h
  split at h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h
        rename_i hc; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
        rfl
      · cases h
    · cases h
  · cases h

def FnDef.isAdd (F : FnDef) (s p d : Nat) : Bool :=
  F.np == 2 && F.tele.ers == [false, false, false, true] && F.dele.isNone && (addProof s p d F.body).isSome

-- cmp: group 14, env 40, np 2, fns 1
def cmpModel : Core :=
  Core.mtch
              (Tm.fv 41)
              (Tm.bind
                (Ent.ty false false false)
                (Tm.app
                  (Tm.tyc 15 (Tm.nil))
                  (Tm.cons
                    (Tm.app (Tm.tyc 6 (Tm.nil)) (Tm.nil))
                    (Tm.cons
                      (Tm.tyc 10 (Tm.nil))
                      (Tm.cons (Tm.fv 41) (Tm.cons (Tm.fv 42) (Tm.nil))))))
                (Tm.nil))
              [(0,
                0,
                Tm.vc 6 0 (Tm.nil),
                Core.mtch
                  (Tm.fv 42)
                  (Tm.bind
                    (Ent.ty false false false)
                    (Tm.app
                      (Tm.tyc 15 (Tm.nil))
                      (Tm.cons
                        (Tm.app (Tm.tyc 6 (Tm.nil)) (Tm.nil))
                        (Tm.cons
                          (Tm.tyc 10 (Tm.nil))
                          (Tm.cons (Tm.fv 41) (Tm.cons (Tm.fv 42) (Tm.nil))))))
                    (Tm.nil))
                  [(0,
                    0,
                    Tm.vc 6 0 (Tm.nil),
                    Core.ret
                      (Tm.cons
                        (Tm.app
                          (Tm.vc 15 1 (Tm.nil))
                          (Tm.cons
                            (Tm.app (Tm.tyc 6 (Tm.nil)) (Tm.nil))
                            (Tm.cons
                              (Tm.tyc 10 (Tm.nil))
                              (Tm.cons (Tm.fv 41) (Tm.nil)))))
                        (Tm.nil))),
                   (1,
                    1,
                    Tm.vc 6 1 (Tm.nil),
                    Core.ret
                      (Tm.cons
                        (Tm.app
                          (Tm.vc 15 0 (Tm.nil))
                          (Tm.cons
                            (Tm.app (Tm.tyc 6 (Tm.nil)) (Tm.nil))
                            (Tm.cons
                              (Tm.tyc 10 (Tm.nil))
                              (Tm.cons
                                (Tm.fv 41)
                                (Tm.cons
                                  (Tm.fv 42)
                                  (Tm.cons
                                    (Tm.app
                                      (Tm.vc 10 0 (Tm.nil))
                                      (Tm.cons (Tm.fv 43) (Tm.nil)))
                                    (Tm.nil)))))))
                        (Tm.nil)))]
                  none
                  false
                  (Core.ret (Tm.cons (Tm.fv 43) (Tm.nil)))),
               (1,
                1,
                Tm.vc 6 1 (Tm.nil),
                Core.case
                  (Tm.fv 42)
                  [(1,
                    1,
                    Tm.vc 6 1 (Tm.nil),
                    Core.call
                      (Tm.fv 40)
                      (Dec.none)
                      (Tm.cons (Tm.fv 43) (Tm.cons (Tm.fv 44) (Tm.nil)))
                      false
                      [false]
                      (some [false, false, false])
                      (Core.mtch
                        (Tm.fv 45)
                        (Tm.bind
                          (Ent.ty false false false)
                          (Tm.app
                            (Tm.tyc 15 (Tm.nil))
                            (Tm.cons
                              (Tm.app (Tm.tyc 6 (Tm.nil)) (Tm.nil))
                              (Tm.cons
                                (Tm.tyc 10 (Tm.nil))
                                (Tm.cons
                                  (Tm.fv 41)
                                  (Tm.cons (Tm.fv 42) (Tm.nil))))))
                          (Tm.nil))
                        [(5,
                          0,
                          Tm.vc 15 0 (Tm.nil),
                          Core.ret
                            (Tm.cons
                              (Tm.app
                                (Tm.vc 15 0 (Tm.nil))
                                (Tm.cons
                                  (Tm.app (Tm.tyc 6 (Tm.nil)) (Tm.nil))
                                  (Tm.cons
                                    (Tm.tyc 10 (Tm.nil))
                                    (Tm.cons
                                      (Tm.fv 41)
                                      (Tm.cons
                                        (Tm.fv 42)
                                        (Tm.cons
                                          (Tm.app
                                            (Tm.vc 10 1 (Tm.nil))
                                            (Tm.cons
                                              (Tm.fv 43)
                                              (Tm.cons
                                                (Tm.fv 44)
                                                (Tm.cons (Tm.fv 50) (Tm.nil)))))
                                          (Tm.nil)))))))
                              (Tm.nil))),
                         (3,
                          1,
                          Tm.vc 15 1 (Tm.nil),
                          Core.ret
                            (Tm.cons
                              (Tm.app
                                (Tm.vc 15 1 (Tm.nil))
                                (Tm.cons
                                  (Tm.app (Tm.tyc 6 (Tm.nil)) (Tm.nil))
                                  (Tm.cons
                                    (Tm.tyc 10 (Tm.nil))
                                    (Tm.cons (Tm.fv 41) (Tm.nil)))))
                              (Tm.nil))),
                         (5,
                          2,
                          Tm.vc 15 2 (Tm.nil),
                          Core.ret
                            (Tm.cons
                              (Tm.app
                                (Tm.vc 15 2 (Tm.nil))
                                (Tm.cons
                                  (Tm.app (Tm.tyc 6 (Tm.nil)) (Tm.nil))
                                  (Tm.cons
                                    (Tm.tyc 10 (Tm.nil))
                                    (Tm.cons
                                      (Tm.fv 41)
                                      (Tm.cons
                                        (Tm.fv 42)
                                        (Tm.cons
                                          (Tm.app
                                            (Tm.vc 10 1 (Tm.nil))
                                            (Tm.cons
                                              (Tm.fv 44)
                                              (Tm.cons
                                                (Tm.fv 43)
                                                (Tm.cons (Tm.fv 50) (Tm.nil)))))
                                          (Tm.nil)))))))
                              (Tm.nil)))]
                        none
                        false
                        (Core.ret (Tm.cons (Tm.fv 46) (Tm.nil))))),
                   (0,
                    0,
                    Tm.vc 6 0 (Tm.nil),
                    Core.ret
                      (Tm.cons
                        (Tm.app
                          (Tm.vc 15 2 (Tm.nil))
                          (Tm.cons
                            (Tm.app (Tm.tyc 6 (Tm.nil)) (Tm.nil))
                            (Tm.cons
                              (Tm.tyc 10 (Tm.nil))
                              (Tm.cons
                                (Tm.fv 41)
                                (Tm.cons
                                  (Tm.fv 42)
                                  (Tm.cons
                                    (Tm.app
                                      (Tm.vc 10 0 (Tm.nil))
                                      (Tm.cons (Tm.fv 43) (Tm.nil)))
                                    (Tm.nil)))))))
                        (Tm.nil)))]
                  none
                  false
                  false)]
              none
              false
              (Core.ret (Tm.cons (Tm.fv 43) (Tm.nil)))

-- mul: group 16, env 45, np 2, fns 1
def mulModel : Core :=
  Core.case
              (Tm.fv 46)
              [(1,
                1,
                Tm.vc 6 1 (Tm.nil),
                Core.call
                  (Tm.fv 45)
                  (Dec.none)
                  (Tm.cons (Tm.fv 48) (Tm.cons (Tm.fv 47) (Tm.nil)))
                  false
                  [false, true]
                  (some [false, false, false, true])
                  (Core.chk
                    (Chk.rt)
                    (Tm.fv 49)
                    (Tm.nil)
                    (Core.call
                      (Tm.fv 34)
                      (Dec.none)
                      (Tm.cons (Tm.fv 47) (Tm.cons (Tm.fv 49) (Tm.nil)))
                      false
                      [false, true]
                      (some [false, false, false, true])
                      (Core.chk
                        (Chk.rt)
                        (Tm.fv 51)
                        (Tm.nil)
                        (Core.call
                          (Tm.fv 43)
                          (Dec.none)
                          (Tm.cons
                            (Tm.fv 47)
                            (Tm.cons
                              (Tm.fv 49)
                              (Tm.cons (Tm.fv 51) (Tm.cons (Tm.fv 52) (Tm.nil)))))
                          true
                          [true]
                          (some [true, true, true, true, true])
                          (Core.ret
                            (Tm.cons
                              (Tm.fv 51)
                              (Tm.cons
                                (Tm.app
                                  (Tm.vc 17 1 (Tm.nil))
                                  (Tm.cons
                                    (Tm.fv 48)
                                    (Tm.cons
                                      (Tm.fv 47)
                                      (Tm.cons
                                        (Tm.fv 49)
                                        (Tm.cons
                                          (Tm.fv 51)
                                          (Tm.cons
                                            (Tm.fv 50)
                                            (Tm.cons (Tm.fv 53) (Tm.nil))))))))
                                (Tm.nil))))))))),
               (0,
                0,
                Tm.vc 6 0 (Tm.nil),
                Core.ret
                  (Tm.cons
                    (Tm.app (Tm.vc 6 0 (Tm.nil)) (Tm.nil))
                    (Tm.cons
                      (Tm.app
                        (Tm.vc 17 0 (Tm.nil))
                        (Tm.cons (Tm.fv 47) (Tm.nil)))
                      (Tm.nil))))]
              none
              false
              false

-- sub: group 17, env 47, np 3, fns 1
def subModel : Core :=
  Core.case
              (Tm.fv 49)
              [(1,
                1,
                Tm.vc 6 1 (Tm.nil),
                Core.case
                  (Tm.fv 48)
                  [(1,
                    1,
                    Tm.vc 6 1 (Tm.nil),
                    Core.mtch
                      (Tm.fv 50)
                      (Tm.bind
                        (Ent.ty false true false)
                        (Tm.app
                          (Tm.tyc 10 (Tm.nil))
                          (Tm.cons
                            (Tm.fv 51)
                            (Tm.cons
                              (Tm.app
                                (Tm.vc 6 1 (Tm.nil))
                                (Tm.cons (Tm.fv 52) (Tm.nil)))
                              (Tm.nil))))
                        (Tm.nil))
                      [(1, 0, Tm.vc 10 0 (Tm.nil), Core.dead),
                       (3,
                        1,
                        Tm.vc 10 1 (Tm.nil),
                        Core.ret (Tm.cons (Tm.fv 55) (Tm.nil)))]
                      none
                      true
                      (Core.call
                        (Tm.fv 47)
                        (Dec.none)
                        (Tm.cons
                          (Tm.fv 52)
                          (Tm.cons (Tm.fv 51) (Tm.cons (Tm.fv 53) (Tm.nil))))
                        false
                        [false, true]
                        (some [false, false, true, false, true])
                        (Core.chk
                          (Chk.rt)
                          (Tm.fv 54)
                          (Tm.nil)
                          (Core.ret
                            (Tm.cons
                              (Tm.fv 54)
                              (Tm.cons
                                (Tm.app
                                  (Tm.vc 9 1 (Tm.nil))
                                  (Tm.cons
                                    (Tm.fv 51)
                                    (Tm.cons
                                      (Tm.fv 54)
                                      (Tm.cons
                                        (Tm.fv 52)
                                        (Tm.cons (Tm.fv 55) (Tm.nil))))))
                                (Tm.nil))))))),
                   (0,
                    0,
                    Tm.vc 6 0 (Tm.nil),
                    Core.absurd
                      (Core.case
                        (Tm.fv 50)
                        [(3,
                          1,
                          Tm.vc 10 1 (Tm.nil),
                          Core.case (Tm.fv 54) [] none true false)]
                        none
                        true
                        false))]
                  none
                  false
                  false),
               (0,
                0,
                Tm.vc 6 0 (Tm.nil),
                Core.ret
                  (Tm.cons
                    (Tm.fv 48)
                    (Tm.cons
                      (Tm.app
                        (Tm.vc 9 0 (Tm.nil))
                        (Tm.cons (Tm.fv 48) (Tm.nil)))
                      (Tm.nil))))]
              none
              false
              false

-- succDiv: group 18, env 49, np 8, fns 1
def succDivModel : Core :=
  Core.call
              (Tm.fv 40)
              (Dec.none)
              (Tm.cons
                (Tm.app
                  (Tm.vc 6 1 (Tm.nil))
                  (Tm.cons (Tm.fv 51) (Tm.nil)))
                (Tm.cons (Tm.fv 52) (Tm.nil)))
              false
              [false]
              (some [false, false, false])
              (Core.mtch
                (Tm.fv 58)
                (Tm.bind
                  (Ent.ty false false false)
                  (Tm.app (Tm.tyc 6 (Tm.nil)) (Tm.nil))
                  (Tm.bind
                    (Ent.ty false false false)
                    (Tm.app (Tm.tyc 6 (Tm.nil)) (Tm.nil))
                    (Tm.bind
                      (Ent.ty false true false)
                      (Tm.app (Tm.tyc 6 (Tm.nil)) (Tm.nil))
                      (Tm.bind
                        (Ent.ty false true false)
                        (Tm.app
                          (Tm.tyc 17 (Tm.nil))
                          (Tm.cons
                            (Tm.bv 2)
                            (Tm.cons (Tm.fv 52) (Tm.cons (Tm.bv 0) (Tm.nil)))))
                        (Tm.bind
                          (Ent.ty false true false)
                          (Tm.app
                            (Tm.tyc 9 (Tm.nil))
                            (Tm.cons
                              (Tm.bv 1)
                              (Tm.cons
                                (Tm.bv 2)
                                (Tm.cons
                                  (Tm.app
                                    (Tm.vc 6 1 (Tm.nil))
                                    (Tm.cons (Tm.fv 54) (Tm.nil)))
                                  (Tm.nil)))))
                          (Tm.bind
                            (Ent.ty false true false)
                            (Tm.app
                              (Tm.tyc 10 (Tm.nil))
                              (Tm.cons (Tm.bv 3) (Tm.cons (Tm.fv 52) (Tm.nil))))
                            (Tm.nil)))))))
                [(5,
                  0,
                  Tm.vc 15 0 (Tm.nil),
                  Core.call
                    (Tm.fv 17)
                    (Dec.none)
                    (Tm.cons
                      (Tm.fv 53)
                      (Tm.cons
                        (Tm.fv 51)
                        (Tm.cons (Tm.fv 54) (Tm.cons (Tm.fv 56) (Tm.nil)))))
                    true
                    [true]
                    (some [true, true, true, true, true])
                    (Core.ret
                      (Tm.cons
                        (Tm.fv 50)
                        (Tm.cons
                          (Tm.app
                            (Tm.vc 6 1 (Tm.nil))
                            (Tm.cons (Tm.fv 51) (Tm.nil)))
                          (Tm.cons
                            (Tm.fv 53)
                            (Tm.cons
                              (Tm.fv 55)
                              (Tm.cons
                                (Tm.fv 64)
                                (Tm.cons (Tm.fv 63) (Tm.nil))))))))),
                 (3,
                  1,
                  Tm.vc 15 1 (Tm.nil),
                  Core.call
                    (Tm.fv 17)
                    (Dec.none)
                    (Tm.cons
                      (Tm.fv 53)
                      (Tm.cons
                        (Tm.fv 51)
                        (Tm.cons (Tm.fv 54) (Tm.cons (Tm.fv 56) (Tm.nil)))))
                    true
                    [true]
                    (some [true, true, true, true, true])
                    (Core.call
                      (Tm.fv 15)
                      (Dec.none)
                      (Tm.cons
                        (Tm.app
                          (Tm.vc 6 1 (Tm.nil))
                          (Tm.cons (Tm.fv 54) (Tm.nil)))
                        (Tm.nil))
                      true
                      [true]
                      (some [true, true])
                      (Core.ret
                        (Tm.cons
                          (Tm.app
                            (Tm.vc 6 1 (Tm.nil))
                            (Tm.cons (Tm.fv 50) (Tm.nil)))
                          (Tm.cons
                            (Tm.app (Tm.vc 6 0 (Tm.nil)) (Tm.nil))
                            (Tm.cons
                              (Tm.app
                                (Tm.vc 6 1 (Tm.nil))
                                (Tm.cons (Tm.fv 54) (Tm.nil)))
                              (Tm.cons
                                (Tm.app
                                  (Tm.vc 17 1 (Tm.nil))
                                  (Tm.cons
                                    (Tm.fv 50)
                                    (Tm.cons
                                      (Tm.fv 52)
                                      (Tm.cons
                                        (Tm.fv 53)
                                        (Tm.cons
                                          (Tm.app
                                            (Tm.vc 6 1 (Tm.nil))
                                            (Tm.cons (Tm.fv 54) (Tm.nil)))
                                          (Tm.cons
                                            (Tm.fv 55)
                                            (Tm.cons (Tm.fv 62) (Tm.nil))))))))
                                (Tm.cons
                                  (Tm.fv 63)
                                  (Tm.cons
                                    (Tm.app
                                      (Tm.vc 10 0 (Tm.nil))
                                      (Tm.cons (Tm.fv 51) (Tm.nil)))
                                    (Tm.nil)))))))))),
                 (5,
                  2,
                  Tm.vc 15 2 (Tm.nil),
                  Core.absurd
                    (Core.call
                      (Tm.fv 25)
                      (Dec.none)
                      (Tm.cons
                        (Tm.fv 51)
                        (Tm.cons
                          (Tm.fv 52)
                          (Tm.cons (Tm.fv 57) (Tm.cons (Tm.fv 63) (Tm.nil)))))
                      true
                      [true]
                      (some [true, true, true, true, true])
                      (Core.case (Tm.fv 64) [] none true false)))]
                none
                false
                (Core.ret
                  (Tm.cons
                    (Tm.fv 59)
                    (Tm.cons
                      (Tm.fv 60)
                      (Tm.cons
                        (Tm.fv 61)
                        (Tm.cons
                          (Tm.fv 62)
                          (Tm.cons
                            (Tm.fv 63)
                            (Tm.cons (Tm.fv 64) (Tm.nil)))))))))

-- divmod: group 19, env 51, np 3, fns 1
def divmodModel : Core :=
  Core.case
              (Tm.fv 52)
              [(1,
                1,
                Tm.vc 6 1 (Tm.nil),
                Core.call
                  (Tm.fv 51)
                  (Dec.none)
                  (Tm.cons
                    (Tm.fv 55)
                    (Tm.cons (Tm.fv 53) (Tm.cons (Tm.fv 54) (Tm.nil))))
                  false
                  [false, false, true, true, true, true]
                  (some [false, false, true, false, false, true, true, true, true])
                  (Core.chk
                    (Chk.rt)
                    (Tm.fv 56)
                    (Tm.nil)
                    (Core.chk
                      (Chk.rt)
                      (Tm.fv 57)
                      (Tm.nil)
                      (Core.call
                        (Tm.fv 49)
                        (Dec.none)
                        (Tm.cons
                          (Tm.fv 56)
                          (Tm.cons
                            (Tm.fv 57)
                            (Tm.cons
                              (Tm.fv 53)
                              (Tm.cons
                                (Tm.fv 58)
                                (Tm.cons
                                  (Tm.fv 55)
                                  (Tm.cons
                                    (Tm.fv 59)
                                    (Tm.cons
                                      (Tm.fv 60)
                                      (Tm.cons (Tm.fv 61) (Tm.nil)))))))))
                        false
                        [false, false, true, true, true, true]
                        (some [false, false, false, true, true, true, true, true, false, false, true, true, true, true])
                        (Core.ret
                          (Tm.cons
                            (Tm.fv 62)
                            (Tm.cons
                              (Tm.fv 63)
                              (Tm.cons
                                (Tm.fv 64)
                                (Tm.cons
                                  (Tm.fv 65)
                                  (Tm.cons
                                    (Tm.fv 66)
                                    (Tm.cons (Tm.fv 67) (Tm.nil)))))))))))),
               (0,
                0,
                Tm.vc 6 0 (Tm.nil),
                Core.ret
                  (Tm.cons
                    (Tm.app (Tm.vc 6 0 (Tm.nil)) (Tm.nil))
                    (Tm.cons
                      (Tm.app (Tm.vc 6 0 (Tm.nil)) (Tm.nil))
                      (Tm.cons
                        (Tm.app (Tm.vc 6 0 (Tm.nil)) (Tm.nil))
                        (Tm.cons
                          (Tm.app
                            (Tm.vc 17 0 (Tm.nil))
                            (Tm.cons (Tm.fv 53) (Tm.nil)))
                          (Tm.cons
                            (Tm.app
                              (Tm.vc 9 0 (Tm.nil))
                              (Tm.cons
                                (Tm.app (Tm.vc 6 0 (Tm.nil)) (Tm.nil))
                                (Tm.nil)))
                            (Tm.cons (Tm.fv 54) (Tm.nil))))))))]
              none
              false
              false

-- succMod: group 32, env 78, np 5, fns 1
def succModModel : Core :=
  Core.call
              (Tm.fv 40)
              (Dec.none)
              (Tm.cons
                (Tm.app
                  (Tm.vc 6 1 (Tm.nil))
                  (Tm.cons (Tm.fv 79) (Tm.nil)))
                (Tm.cons (Tm.fv 80) (Tm.nil)))
              false
              [false]
              (some [false, false, false])
              (Core.mtch
                (Tm.fv 84)
                (Tm.bind
                  (Ent.ty false false false)
                  (Tm.app (Tm.tyc 6 (Tm.nil)) (Tm.nil))
                  (Tm.bind
                    (Ent.ty false true false)
                    (Tm.app
                      (Tm.tyc 10 (Tm.nil))
                      (Tm.cons (Tm.bv 0) (Tm.cons (Tm.fv 80) (Tm.nil))))
                    (Tm.bind
                      (Ent.ty false true false)
                      (Tm.app
                        (Tm.tyc 13 (Tm.nil))
                        (Tm.cons
                          (Tm.app
                            (Tm.vc 6 1 (Tm.nil))
                            (Tm.cons (Tm.fv 81) (Tm.nil)))
                          (Tm.cons (Tm.fv 80) (Tm.cons (Tm.bv 1) (Tm.nil)))))
                      (Tm.nil))))
                [(5,
                  0,
                  Tm.vc 15 0 (Tm.nil),
                  Core.call
                    (Tm.fv 27)
                    (Dec.none)
                    (Tm.cons
                      (Tm.fv 81)
                      (Tm.cons
                        (Tm.fv 80)
                        (Tm.cons
                          (Tm.fv 79)
                          (Tm.cons (Tm.fv 83) (Tm.cons (Tm.fv 89) (Tm.nil))))))
                    true
                    [true]
                    (some [true, true, true, true, true, true])
                    (Core.ret
                      (Tm.cons
                        (Tm.app
                          (Tm.vc 6 1 (Tm.nil))
                          (Tm.cons (Tm.fv 79) (Tm.nil)))
                        (Tm.cons (Tm.fv 89) (Tm.cons (Tm.fv 90) (Tm.nil)))))),
                 (3,
                  1,
                  Tm.vc 15 1 (Tm.nil),
                  Core.call
                    (Tm.fv 29)
                    (Dec.none)
                    (Tm.cons
                      (Tm.fv 81)
                      (Tm.cons (Tm.fv 79) (Tm.cons (Tm.fv 83) (Tm.nil))))
                    true
                    [true]
                    (some [true, true, true, true])
                    (Core.ret
                      (Tm.cons
                        (Tm.app (Tm.vc 6 0 (Tm.nil)) (Tm.nil))
                        (Tm.cons
                          (Tm.app
                            (Tm.vc 10 0 (Tm.nil))
                            (Tm.cons (Tm.fv 79) (Tm.nil)))
                          (Tm.cons (Tm.fv 88) (Tm.nil)))))),
                 (5,
                  2,
                  Tm.vc 15 2 (Tm.nil),
                  Core.absurd
                    (Core.call
                      (Tm.fv 25)
                      (Dec.none)
                      (Tm.cons
                        (Tm.fv 79)
                        (Tm.cons
                          (Tm.fv 80)
                          (Tm.cons (Tm.fv 82) (Tm.cons (Tm.fv 89) (Tm.nil)))))
                      true
                      [true]
                      (some [true, true, true, true, true])
                      (Core.case (Tm.fv 90) [] none true false)))]
                none
                false
                (Core.ret
                  (Tm.cons
                    (Tm.fv 85)
                    (Tm.cons (Tm.fv 86) (Tm.cons (Tm.fv 87) (Tm.nil))))))

-- natMod: group 33, env 80, np 3, fns 1
def natModModel : Core :=
  Core.case
              (Tm.fv 81)
              [(1,
                1,
                Tm.vc 6 1 (Tm.nil),
                Core.call
                  (Tm.fv 80)
                  (Dec.none)
                  (Tm.cons
                    (Tm.fv 84)
                    (Tm.cons (Tm.fv 82) (Tm.cons (Tm.fv 83) (Tm.nil))))
                  false
                  [false, true, true]
                  (some [false, false, true, false, true, true])
                  (Core.chk
                    (Chk.rt)
                    (Tm.fv 85)
                    (Tm.nil)
                    (Core.call
                      (Tm.fv 78)
                      (Dec.none)
                      (Tm.cons
                        (Tm.fv 85)
                        (Tm.cons
                          (Tm.fv 82)
                          (Tm.cons
                            (Tm.fv 84)
                            (Tm.cons (Tm.fv 86) (Tm.cons (Tm.fv 87) (Tm.nil))))))
                      false
                      [false, true, true]
                      (some [false, false, true, true, true, false, true, true])
                      (Core.ret
                        (Tm.cons
                          (Tm.fv 88)
                          (Tm.cons (Tm.fv 89) (Tm.cons (Tm.fv 90) (Tm.nil)))))))),
               (0,
                0,
                Tm.vc 6 0 (Tm.nil),
                Core.ret
                  (Tm.cons
                    (Tm.app (Tm.vc 6 0 (Tm.nil)) (Tm.nil))
                    (Tm.cons
                      (Tm.fv 83)
                      (Tm.cons
                        (Tm.app
                          (Tm.vc 13 0 (Tm.nil))
                          (Tm.cons
                            (Tm.app (Tm.vc 6 0 (Tm.nil)) (Tm.nil))
                            (Tm.cons (Tm.fv 82) (Tm.cons (Tm.fv 83) (Tm.nil)))))
                        (Tm.nil)))))]
              none
              false
              false

theorem env_right {L xs : List Tm} {n m : Nat} (h : L.length = n) (hm : n ≤ m) :
    Tm.env (L ++ xs) m = xs.getD (m - n) .nil := by
  simp only [Tm.env, List.getD_eq_getElem?_getD]; rw [List.getElem?_append_right (by omega), h]

structure NatFacts (P : Prog) : Prop where
  nat : P.natD = some 6
  w60 : P.wrapField 6 0 = none
  w61 : P.wrapField 6 1 = none
  e60 : P.ctorErs 6 0 = [false]
  e61 : P.ctorErs 6 1 = [false, false]
  w150 : P.wrapField 15 0 = none
  w151 : P.wrapField 15 1 = none
  w152 : P.wrapField 15 2 = none
  e150 : P.ctorErs 15 0 = [true, true, true, true, true, false]
  e151 : P.ctorErs 15 1 = [true, true, true, false]
  e152 : P.ctorErs 15 2 = [true, true, true, true, true, false]

instance (P : Prog) : Decidable (NatFacts P) :=
  decidable_of_iff (P.natD = some 6 ∧ P.wrapField 6 0 = none ∧ P.wrapField 6 1 = none ∧ P.ctorErs 6 0 = [false] ∧
      P.ctorErs 6 1 = [false, false] ∧ P.wrapField 15 0 = none ∧ P.wrapField 15 1 = none ∧ P.wrapField 15 2 = none ∧
      P.ctorErs 15 0 = [true, true, true, true, true, false] ∧ P.ctorErs 15 1 = [true, true, true, false] ∧
      P.ctorErs 15 2 = [true, true, true, true, true, false])
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩⟩

def cmpCode (a b : Nat) : Nat := if a < b then 0 else if a = b then 1 else 2

def cmpVal (a b : Nat) : Tm :=
  .app (.vc 15 (cmpCode a b) .nil) (.ofList (List.replicate (if a = b then 3 else 5) .tok))

def Prog.nativeAdd (P : Prog) (env : List Tm) (G : Group) (j : Nat) (F : FnDef) : List Tm → Option (List Tm)
  | [.nat a, .nat b] => match P.natD with
    | some d => if P.wrapField d 1 = none ∧ P.ctorErs d 1 = [false, false] ∧ F.isAdd (env.length + j) (env.length + G.fns.length) d = true then
        some [.nat (a + b), .tok] else none
    | none => none
  | _ => none

def Prog.isModel (P : Prog) (env : List Tm) (G : Group) (j : Nat) (F : FnDef) (n np : Nat) (ers : List Bool) (M : Core) : Bool :=
  env.length == n && j == 0 && G.fns.length == 1 && F.np == np && F.tele.ers == ers && F.dele.isNone && F.body.beq M &&
    decide (NatFacts P)

def Prog.nativeCmp (P : Prog) (env : List Tm) (G : Group) (j : Nat) (F : FnDef) : List Tm → Option (List Tm)
  | [.nat a, .nat b] => if P.isModel env G j F 40 2 [false, false, false] cmpModel then some [cmpVal a b] else none
  | _ => none

theorem foldl_snoc (g : List Tm → FnDef → Tm) : ∀ (Fs : List FnDef) (acc : List Tm),
    (Fs.foldl (fun acc F => acc ++ [g acc F]) acc).length = acc.length + Fs.length ∧
    (Fs.foldl (fun acc F => acc ++ [g acc F]) acc).take acc.length = acc ∧
    ∀ i (h : i < Fs.length), (Fs.foldl (fun acc F => acc ++ [g acc F]) acc)[acc.length + i]? =
      some (g ((Fs.foldl (fun acc F => acc ++ [g acc F]) acc).take (acc.length + i)) Fs[i])
  | [], acc => by simp
  | F :: Fs, acc => by
    obtain ⟨h1, h2, h3⟩ := foldl_snoc g Fs (acc ++ [g acc F])
    show (Fs.foldl _ (acc ++ [g acc F])).length = _ ∧ (Fs.foldl _ (acc ++ [g acc F])).take _ = _ ∧
      ∀ i (h : i < (F :: Fs).length), (Fs.foldl _ (acc ++ [g acc F]))[acc.length + i]? =
        some (g ((Fs.foldl _ (acc ++ [g acc F])).take (acc.length + i)) (F :: Fs)[i])
    generalize Fs.foldl (fun acc F => acc ++ [g acc F]) (acc ++ [g acc F]) = R at h1 h2 h3 ⊢
    simp only [List.length_append, List.length_singleton] at h1 h2 h3
    have ht : R.take acc.length = acc := by
      have := congrArg (List.take acc.length) h2
      rwa [List.take_take, Nat.min_eq_left (by omega), List.take_left' rfl] at this
    refine ⟨by simp; omega, ht, fun i hi => ?_⟩
    cases i with
    | zero =>
      have : R[acc.length]? = (R.take (acc.length + 1))[acc.length]? := by rw [List.getElem?_take]; simp
      rw [Nat.add_zero, this, h2, ht]; simp
    | succ i =>
      have := h3 i (by simpa using hi)
      rw [show acc.length + (i + 1) = acc.length + 1 + i by omega, this]; simp

theorem closuresS_length (env : List Tm) (gid : Nat) (G : Group) : (closuresS env gid G).length = G.fns.length := by
  simpa [closuresS] using (foldl_snoc (cval env gid) G.fns []).1

theorem Tm.ofList_toList' : ∀ (t : Tm), t.isList = true → Tm.ofList t.toList = t := by
  intro t; induction t <;> simp_all [Tm.ofList, Tm.toList, Tm.isList]

theorem RunS.ret' {P : Prog} {ρ out : List Tm} {ts : Tm} (h : out = ts.toList.map (P.sub ρ)) :
    RunS P ρ (.ret ts) out := h ▸ .ret

theorem closuresS_self {env : List Tm} {gid j : Nat} {G : Group} {F : FnDef} (hF : G.fns[j]? = some F)
    (hd : F.dele = none) : (closuresS env gid G).getD j .nil = .clo (.ofList env) gid j := by
  have hj : j < G.fns.length := (List.getElem?_eq_some_iff.mp hF).1
  have hFj : G.fns[j] = F := (List.getElem?_eq_some_iff.mp hF).2
  obtain ⟨h1, -, h3⟩ := foldl_snoc (cval env gid) G.fns []
  have := h3 j hj
  simp only [List.length_nil, Nat.zero_add] at this h1
  unfold closuresS
  generalize List.foldl (fun acc F => acc ++ [cval env gid acc F]) [] G.fns = R at h1 this ⊢
  rw [List.getD_eq_getElem?_getD, this]
  simp only [Option.getD_some, cval, hFj, hd, List.length_take]
  congr 1; omega

theorem add_run {P : Prog} {d e gid j : Nat} {G : Group} {F : FnDef} {env : List Tm} (hd : P.natD = some d)
    (hw : P.wrapField d 1 = none) (hfe : P.ctorErs d 1 = [false, false]) (hG : P.groups[gid]? = some G) (hF : G.fns[j]? = some F) (hdl : F.dele = none)
    (hers : F.tele.ers = [false, false, false, true]) (hnp : F.np = 2)
    (hb : F.body = addBody (env.length + j) (env.length + G.fns.length) d e) :
    ∀ a b, ∃ pf, RunS P (env ++ closuresS env gid G ++ [.nat a, .nat b]) F.body [.nat (a + b), pf] := by
  have hcl := closuresS_self (env := env) (gid := gid) hF hdl
  have hL : (env ++ closuresS env gid G).length = env.length + G.fns.length := by simp [closuresS_length]
  have get : ∀ (xs : List Tm) i, Tm.env (env ++ (closuresS env gid G ++ xs)) (env.length + G.fns.length + i) = xs.getD i .nil := by
    intro xs i; simp only [Tm.env, List.getD_eq_getElem?_getD]
    rw [← List.append_assoc, List.getElem?_append_right (by omega)]; congr 2; omega
  have get0 : ∀ (xs : List Tm), Tm.env (env ++ (closuresS env gid G ++ xs)) (env.length + G.fns.length) = xs.getD 0 .nil := by
    intro xs; simpa using get xs 0
  have hj : j < G.fns.length := (List.getElem?_eq_some_iff.mp hF).1
  have self : ∀ (xs : List Tm), Tm.env (env ++ (closuresS env gid G ++ xs)) (env.length + j) = .clo (.ofList env) gid j := by
    intro xs; simp only [Tm.env, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_append_left (by simp [closuresS_length]; omega)]
    simpa [List.getD_eq_getElem?_getD] using hcl
  intro a b
  induction a with
  | zero =>
    refine ⟨P.sub (env ++ closuresS env gid G ++ [.nat 0, .nat b])
      (.app (.vc e 0 .nil) (.ofList [.fv (env.length + G.fns.length + 1)])), ?_⟩
    rw [hb]; unfold addBody
    exact RunS.case (d := d) (c := 0) (ls := .nil) (vs := .nil) (by simp [Prog.sub, Prog.subU, get0, Prog.view, hd]) rfl
      (RunS.ret' (by simp [Tm.ofList, Tm.toList, Prog.sub, Prog.subU, get]))
  | succ k ih =>
    obtain ⟨pf, hk⟩ := ih
    refine ⟨P.sub (env ++ closuresS env gid G ++ [.nat (k + 1), .nat b] ++ [.nat k] ++ [.nat (k + b), .tok])
      (.app (.vc e 1 .nil) (.ofList [.fv (env.length + G.fns.length + 2), .fv (env.length + G.fns.length + 1),
        .fv (env.length + G.fns.length + 3), .fv (env.length + G.fns.length + 4)])), ?_⟩
    rw [hb]; unfold addBody
    refine RunS.case (d := d) (c := 1) (ls := .nil) (vs := .cons (.nat k) .nil)
      (by simp [Prog.sub, Prog.subU, get0, Prog.view, hd]) rfl ?_
    refine RunS.call (env := .ofList env) (G := G) (F := F) (outs := [.nat (k + b), pf]) ?_ hG hF ?_ ?_
    · simp [Prog.sub, Prog.subU, self]
    · rw [Tm.toList_ofList]
      have hs : F.spreadIn (some [false, false, false, true])
          (List.map (P.sub (env ++ closuresS env gid G ++ [Tm.nat (k + 1), Tm.nat b] ++ ((Tm.nat k).cons Tm.nil).toList))
            (Tm.ofList [Tm.fv (env.length + G.fns.length + 2), Tm.fv (env.length + G.fns.length + 1)]).toList) =
          [.nat k, .nat b] := by
        simp [FnDef.spreadIn, hers, hnp, filt, spread, Tm.ofList, Tm.toList, Prog.sub, Prog.subU, get]
      rw [hs]; exact hk
    · have hso : F.spreadOut (some [false, false, false, true])
          (Tm.ofList [Tm.fv (env.length + G.fns.length + 2), Tm.fv (env.length + G.fns.length + 1)]).toList.length
          [Tm.nat (k + b), pf] = [.nat (k + b), .tok] := by
        simp [FnDef.spreadOut, hers, hnp, filt, spread, Tm.toList_ofList]
      have hpre : ((Tm.nat k).cons Tm.nil).toList = [.nat k] := rfl
      rw [hso, hpre]
      refine RunS.chk (RunS.ret' ?_)
      rw [Tm.toList_ofList]
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      have h3 : P.sub (env ++ closuresS env gid G ++ [Tm.nat (k + 1), Tm.nat b] ++ [Tm.nat k] ++ [Tm.nat (k + b), Tm.tok])
          (.fv (env.length + G.fns.length + 3)) = .nat (k + b) := by
        simp only [Prog.sub, Prog.subU, List.append_assoc, List.cons_append, List.nil_append]
        rw [get]; rfl
      have h3' : P.subU (Tm.env (env ++ closuresS env gid G ++ [Tm.nat (k + 1), Tm.nat b] ++ [Tm.nat k] ++
          [Tm.nat (k + b), Tm.tok])) (.fv (env.length + G.fns.length + 3)) = .nat (k + b) := h3
      simp only [Prog.sub, Prog.subU]
      rw [hw]
      simp only [Tm.ofList, Prog.subUArgs, h3', Tm.subst, hfe, maskArgs]
      simp [Prog.norm, hd]; omega

theorem RunS.ret2 {P : Prog} {ρ : List Tm} {t1 t2 x : Tm} (h : P.sub ρ t1 = x) :
    RunS P ρ (.ret (.cons t1 (.cons t2 .nil))) [x, P.sub ρ t2] := by
  have := RunS.ret (P := P) (ρ := ρ) (ts := .cons t1 (.cons t2 .nil)); simpa [Tm.toList, h] using this

theorem closuresS_one {env : List Tm} {gid : Nat} {G : Group} {F : FnDef} (hGf : G.fns = [F]) (hd : F.dele = none) :
    closuresS env gid G = [.clo (.ofList env) gid 0] := by
  simp [closuresS, hGf, cval, hd]

theorem RunS.mtch' {P : Prog} {ρ pre outs out : List Tm} {s R : Tm} {brs : List Br} {els : Option Core} {rest body : Core}
    {d c : Nat} {vs : Tm} (hs : P.view (P.sub ρ s) = .app (.vc d c .nil) vs) (hsel : selectBr brs els c vs.toList = some (pre, body))
    (hb : RunS P (ρ ++ pre) body outs) (hr : RunS P (ρ ++ outs) rest out) : RunS P ρ (.mtch s R brs els false rest) out :=
  .mtch hs hsel hb hr

theorem cmp_run {P : Prog} (hN : NatFacts P) {env : List Tm} {gid : Nat} {G : Group} {F : FnDef} (hlen : env.length = 40)
    (hG : P.groups[gid]? = some G) (hGf : G.fns = [F]) (hb : F.body = cmpModel) (hers : F.tele.ers = [false, false, false])
    (hnp : F.np = 2) (hdl : F.dele = none) :
    ∀ a b, RunS P (env ++ [.clo (.ofList env) gid 0] ++ [.nat a, .nat b]) F.body [cmpVal a b] := by
  have hF : G.fns[0]? = some F := by simp [hGf]
  have hN1 := hN.nat
  intro a; induction a with
  | zero =>
    intro b; rw [hb]; unfold cmpModel
    cases b with
    | zero =>
      refine RunS.mtch' (pre := []) (vs := .nil) (c := 0) (d := 6) (outs := [cmpVal 0 0]) ?_ rfl
        (RunS.mtch' (pre := []) (vs := .nil) (c := 0) (d := 6) (outs := [cmpVal 0 0]) ?_ rfl (RunS.ret' ?_) (RunS.ret' ?_))
        (RunS.ret' ?_)
      all_goals simp [Prog.sub, Prog.subU, Prog.subUArgs, Prog.view, Prog.norm, env_right hlen, hN1, hN.w151, hN.e151,
        maskArgs, Tm.ofList, Tm.toList, Tm.subst, cmpVal, cmpCode]
    | succ k =>
      refine RunS.mtch' (pre := []) (vs := .nil) (c := 0) (d := 6) (outs := [cmpVal 0 (k + 1)]) ?_ rfl
        (RunS.mtch' (pre := [.nat k]) (vs := .cons (.nat k) .nil) (c := 1) (d := 6) (outs := [cmpVal 0 (k + 1)]) ?_ rfl
          (RunS.ret' ?_) (RunS.ret' ?_))
        (RunS.ret' ?_)
      all_goals simp [Prog.sub, Prog.subU, Prog.subUArgs, Prog.view, Prog.norm, env_right hlen, hN1, hN.w150, hN.e150,
        maskArgs, Tm.ofList, Tm.toList, Tm.subst, cmpVal, cmpCode]
  | succ k ih =>
    intro b
    have hS := ih
    rw [hb] at ih ⊢; unfold cmpModel
    cases b with
    | zero =>
      refine RunS.mtch' (pre := [.nat k]) (vs := .cons (.nat k) .nil) (c := 1) (d := 6) (outs := [cmpVal (k + 1) 0]) ?_ rfl
        (RunS.case (d := 6) (c := 0) (ls := .nil) (vs := .nil) (pre := []) ?_ rfl (RunS.ret' ?_)) (RunS.ret' ?_)
      all_goals simp [Prog.sub, Prog.subU, Prog.subUArgs, Prog.view, Prog.norm, env_right hlen, hN1, hN.w152, hN.e152,
        maskArgs, Tm.ofList, Tm.toList, Tm.subst, cmpVal, cmpCode]
    | succ m =>
      have hcall : (Tm.ofList env).toList ++ closuresS (Tm.ofList env).toList gid G ++
          F.spreadIn (some [false, false, false])
            ((Tm.cons (.fv 43) (.cons (.fv 44) .nil)).toList.map
              (P.sub (env ++ [.clo (.ofList env) gid 0] ++ [.nat (k + 1), .nat (m + 1)] ++
                (Tm.cons (.nat k) .nil).toList ++ (Tm.cons (.nat m) .nil).toList))) =
          env ++ [.clo (.ofList env) gid 0] ++ [.nat k, .nat m] := by
        simp [Tm.toList_ofList, closuresS_one hGf hdl, FnDef.spreadIn, hers, hnp, filt, spread, Tm.toList, Prog.sub,
          Prog.subU, env_right hlen]
      have hrec := hS m
      rw [← hcall] at hrec
      refine RunS.mtch' (pre := [.nat k]) (vs := .cons (.nat k) .nil) (c := 1) (d := 6) (outs := [cmpVal (k + 1) (m + 1)])
        ?_ rfl (RunS.case (d := 6) (c := 1) (ls := .nil) (vs := .cons (.nat m) .nil) ?_ rfl
          (RunS.call (env := .ofList env) (G := G) (F := F) (outs := [cmpVal k m]) ?_ hG hF hrec ?hrest)) (RunS.ret' ?_)
      case hrest =>
        simp [FnDef.spreadOut, hers, hnp, filt, spread, Tm.toList]
        rcases Nat.lt_trichotomy k m with h | h | h
        · apply RunS.mtch' (pre := List.replicate 5 .tok) (vs := .ofList (List.replicate 5 .tok)) (c := 0) (d := 15)
            (outs := [cmpVal (k + 1) (m + 1)])
          · simp [Prog.sub, Prog.subU, Prog.view, env_right hlen, Tm.ofList, cmpVal, cmpCode, h, Nat.ne_of_lt h]
          · rfl
          all_goals refine RunS.ret' ?_
          all_goals simp [Prog.sub, Prog.subU, Prog.subUArgs, Prog.view, Prog.norm, env_right hlen, hN1, hN.w150, hN.e150,
            maskArgs, Tm.ofList, Tm.toList, Tm.subst, cmpVal, cmpCode, h, Nat.ne_of_lt h]
        · subst h
          apply RunS.mtch' (pre := List.replicate 3 .tok) (vs := .ofList (List.replicate 3 .tok)) (c := 1) (d := 15)
            (outs := [cmpVal (k + 1) (k + 1)])
          · simp [Prog.sub, Prog.subU, Prog.view, env_right hlen, Tm.ofList, cmpVal, cmpCode]
          · rfl
          all_goals refine RunS.ret' ?_
          all_goals simp [Prog.sub, Prog.subU, Prog.subUArgs, Prog.view, Prog.norm, env_right hlen, hN1, hN.w151, hN.e151,
            maskArgs, Tm.ofList, Tm.toList, Tm.subst, cmpVal, cmpCode]
        · apply RunS.mtch' (pre := List.replicate 5 .tok) (vs := .ofList (List.replicate 5 .tok)) (c := 2) (d := 15)
            (outs := [cmpVal (k + 1) (m + 1)])
          · simp [Prog.sub, Prog.subU, Prog.view, env_right hlen, Tm.ofList, cmpVal, cmpCode, Nat.not_lt.mpr (Nat.le_of_lt h), Nat.ne_of_gt h]
          · rfl
          all_goals refine RunS.ret' ?_
          all_goals simp [Prog.sub, Prog.subU, Prog.subUArgs, Prog.view, Prog.norm, env_right hlen, hN1, hN.w152, hN.e152,
            maskArgs, Tm.ofList, Tm.toList, Tm.subst, cmpVal, cmpCode, Nat.not_lt.mpr (Nat.le_of_lt h), Nat.ne_of_gt h]
      all_goals simp [Prog.sub, Prog.subU, Prog.subUArgs, Prog.view, Prog.norm, env_right hlen, hN1,
        maskArgs, Tm.ofList, Tm.toList, Tm.subst, cmpVal, cmpCode]

theorem env_left {L xs : List Tm} {m : Nat} (hm : m < L.length) : Tm.env (L ++ xs) m = L.getD m .nil := by
  simp only [Tm.env, List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left hm]

def Prog.isAddClo (P : Prog) : Tm → Bool
  | .clo e gid 0 => match P.groups[gid]? with
    | some G => match G.fns with
      | [F] => e.isList && P.wrapField 6 1 == none && P.ctorErs 6 1 == [false, false] && P.natD == some 6 &&
          F.isAdd e.toList.length (e.toList.length + 1) 6
      | _ => false
    | none => false
  | _ => false

theorem Prog.isAddClo_run {P : Prog} {v : Tm} (h : P.isAddClo v = true) : ∃ envA gidA GA FA,
    v = .clo (.ofList envA) gidA 0 ∧ P.groups[gidA]? = some GA ∧ GA.fns[0]? = some FA ∧ FA.np = 2 ∧
    FA.tele.ers = [false, false, false, true] ∧
    ∀ a b, ∃ pf, RunS P (envA ++ closuresS envA gidA GA ++ [.nat a, .nat b]) FA.body [.nat (a + b), pf] := by
  unfold Prog.isAddClo at h
  split at h
  · rename_i e gid
    split at h
    · rename_i G hG
      split at h
      · rename_i F hGf
        simp only [Bool.and_eq_true, beq_iff_eq, FnDef.isAdd, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at h
        obtain ⟨⟨⟨⟨he, hw⟩, hfe⟩, hd⟩, ⟨⟨hnp, hers⟩, hdl⟩, ep, hep⟩ := h
        have hF : G.fns[0]? = some F := by simp [hGf]
        refine ⟨e.toList, gid, G, F, by rw [Tm.ofList_toList' _ he], hG, hF, hnp, hers, fun a b => ?_⟩
        have hlen : e.toList.length + 0 = e.toList.length := rfl
        have hfl : e.toList.length + G.fns.length = e.toList.length + 1 := by simp [hGf]
        exact add_run hd hw hfe hG hF hdl hers hnp (by rw [addProof_spec hep, hlen, hfl]) a b
      · cases h
    · cases h
  · cases h

def mulVal : Nat → Nat → Nat := (· * ·)

theorem mul_run {P : Prog} (hN : NatFacts P) {env : List Tm} {gid : Nat} {G : Group} {F : FnDef} (hlen : env.length = 45)
    (hG : P.groups[gid]? = some G) (hGf : G.fns = [F]) (hb : F.body = mulModel) (hers : F.tele.ers = [false, false, false, true])
    (hnp : F.np = 2) (hdl : F.dele = none) (hadd : P.isAddClo (env.getD 34 .nil) = true) :
    ∀ a b, ∃ pf, RunS P (env ++ [.clo (.ofList env) gid 0] ++ [.nat a, .nat b]) F.body [.nat (a * b), pf] := by
  have hF : G.fns[0]? = some F := by simp [hGf]
  have hN1 := hN.nat
  obtain ⟨envA, gidA, GA, FA, hv, hGA, hFA, hnpA, hersA, hrunA⟩ := Prog.isAddClo_run hadd
  intro a; induction a with
  | zero =>
    intro b; rw [hb]; unfold mulModel
    refine ⟨P.sub (env ++ [.clo (.ofList env) gid 0] ++ [.nat 0, .nat b] ++ []) (.app (.vc 17 0 .nil) (.cons (.fv 47) .nil)),
      RunS.case (d := 6) (c := 0) (ls := .nil) (vs := .nil) (pre := []) ?_ rfl (RunS.ret' ?_)⟩
    all_goals simp [Prog.sub, Prog.subU, Prog.subUArgs, Prog.view, Prog.norm, env_right hlen, hN1, hN.w60, hN.e60,
      maskArgs, Tm.ofList, Tm.toList, Tm.subst]
  | succ k ih =>
    intro b
    obtain ⟨pf1, h1⟩ := ih b
    obtain ⟨pf2, h2⟩ := hrunA b (k * b)
    have hsc : (Tm.ofList env).toList ++ closuresS (Tm.ofList env).toList gid G ++
        F.spreadIn (some [false, false, false, true])
          ((Tm.cons (.fv 48) (.cons (.fv 47) .nil)).toList.map
            (P.sub (env ++ [.clo (.ofList env) gid 0] ++ [.nat (k + 1), .nat b] ++ (Tm.cons (.nat k) .nil).toList))) =
        env ++ [.clo (.ofList env) gid 0] ++ [.nat k, .nat b] := by
      simp [Tm.toList_ofList, closuresS_one hGf hdl, FnDef.spreadIn, hers, hnp, filt, spread, Tm.toList, Prog.sub,
        Prog.subU, env_right hlen]
    rw [← hsc] at h1
    rw [hb]; unfold mulModel
    rw [show (k + 1) * b = b + k * b by rw [Nat.succ_mul, Nat.add_comm]]
    apply Exists.intro
    refine RunS.case (d := 6) (c := 1) (ls := .nil) (vs := .cons (.nat k) .nil) ?_ rfl ?_
    · simp [Prog.sub, Prog.subU, Prog.view, env_right hlen, hN1]
    refine RunS.call (env := .ofList env) (G := G) (F := F) (outs := [.nat (k * b), pf1]) ?_ hG hF h1 (RunS.chk ?_)
    · simp [Prog.sub, Prog.subU, env_right hlen]
    have hso : F.spreadOut (some [false, false, false, true]) ((Tm.fv 48).cons ((Tm.fv 47).cons Tm.nil)).toList.length
        [Tm.nat (k * b), pf1] = [.nat (k * b), .tok] := by simp [FnDef.spreadOut, hers, hnp, filt, spread, Tm.toList]
    rw [hso]
    have hspA : FA.spreadIn (some [false, false, false, true])
        (((Tm.fv 47).cons ((Tm.fv 49).cons Tm.nil)).toList.map
          (P.sub (env ++ [(Tm.ofList env).clo gid 0] ++ [Tm.nat (k + 1), Tm.nat b] ++ ((Tm.nat k).cons Tm.nil).toList ++
            [.nat (k * b), .tok]))) = [.nat b, .nat (k * b)] := by
      simp [FnDef.spreadIn, hersA, hnpA, filt, spread, Tm.toList, Prog.sub, Prog.subU, env_right hlen]
    refine RunS.call (env := .ofList envA) (G := GA) (F := FA) (outs := [.nat (b + k * b), pf2]) ?_ hGA hFA
      (by rw [hspA, Tm.toList_ofList]; exact h2) (RunS.chk ?_)
    · simp [Prog.sub, Prog.subU, env_left (show 34 < env.length by omega), ← hv]
    have hsoA : FA.spreadOut (some [false, false, false, true]) ((Tm.fv 47).cons ((Tm.fv 49).cons Tm.nil)).toList.length
        [Tm.nat (b + k * b), pf2] = [.nat (b + k * b), .tok] := by simp [FnDef.spreadOut, hersA, hnpA, filt, spread, Tm.toList]
    rw [hsoA]
    refine RunS.callE (RunS.ret2 ?_)
    simp [Prog.sub, Prog.subU, env_right hlen, Tm.toList]

theorem nativeAdd_run {P : Prog} {env : List Tm} {gid j : Nat} {G : Group} {F : FnDef} {xs outs : List Tm}
    {ve : Option (List Bool)} {n : Nat} (hG : P.groups[gid]? = some G) (hF : G.fns[j]? = some F)
    (h : P.nativeAdd env G j F xs = some outs) :
    ∃ outs', RunS P (env ++ closuresS env gid G ++ xs) F.body outs' ∧ F.spreadOut ve n outs' = F.spreadOut ve n outs := by
  unfold Prog.nativeAdd at h
  split at h
  · rename_i a b
    split at h
    · rename_i d hd
      split at h
      · rename_i hc
        obtain ⟨hw, hfe, hadd⟩ := hc
        simp only [FnDef.isAdd, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hadd
        obtain ⟨⟨⟨hnp, hers⟩, hdl⟩, e, he⟩ := hadd
        cases h
        obtain ⟨pf, hr⟩ := add_run hd hw hfe hG hF hdl hers hnp (addProof_spec he) a b
        exact ⟨_, hr, by simp [FnDef.spreadOut, hers, hnp, filt]⟩
      · cases h
    · cases h
  · cases h

theorem Prog.isModel_spec {P : Prog} {env : List Tm} {G : Group} {j : Nat} {F : FnDef} {n np : Nat} {ers : List Bool}
    {M : Core} (h : P.isModel env G j F n np ers M = true) (hF : G.fns[j]? = some F) :
    env.length = n ∧ j = 0 ∧ G.fns = [F] ∧ F.np = np ∧ F.tele.ers = ers ∧ F.dele = none ∧ F.body = M ∧ NatFacts P := by
  simp only [Prog.isModel, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, rfl⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, rfl, ?_, h4, h5, h6, Core.beq_eq h7, h8⟩
  match hg : G.fns, h3 with
  | [F'], _ => rw [hg] at hF; simp at hF; rw [hF]

theorem nativeCmp_run {P : Prog} {env : List Tm} {gid j : Nat} {G : Group} {F : FnDef} {xs outs : List Tm}
    {ve : Option (List Bool)} {n : Nat} (hG : P.groups[gid]? = some G) (hF : G.fns[j]? = some F)
    (h : P.nativeCmp env G j F xs = some outs) :
    ∃ outs', RunS P (env ++ closuresS env gid G ++ xs) F.body outs' ∧ F.spreadOut ve n outs' = F.spreadOut ve n outs := by
  unfold Prog.nativeCmp at h
  split at h
  · rename_i a b
    split at h
    · rename_i hc
      obtain ⟨hl, rfl, hGf, hnp, hers, hdl, hb, hN⟩ := Prog.isModel_spec hc hF
      cases h
      rw [closuresS_one hGf hdl]
      exact ⟨_, cmp_run hN hl hG hGf hb hers hnp hdl a b, rfl⟩
    · cases h
  · cases h

theorem sub_run {P : Prog} (hN : NatFacts P) {env : List Tm} {gid : Nat} {G : Group} {F : FnDef} (hlen : env.length = 47)
    (hG : P.groups[gid]? = some G) (hGf : G.fns = [F]) (hb : F.body = subModel)
    (hers : F.tele.ers = [false, false, true, false, true]) (hnp : F.np = 3) (hdl : F.dele = none) :
    ∀ b a, b ≤ a → ∃ pf, RunS P (env ++ [.clo (.ofList env) gid 0] ++ [.nat a, .nat b, .tok]) F.body [.nat (a - b), pf] := by
  have hF : G.fns[0]? = some F := by simp [hGf]
  have hN1 := hN.nat
  intro b; induction b with
  | zero =>
    intro a _; rw [hb]; unfold subModel
    apply Exists.intro
    refine RunS.case (d := 6) (c := 0) (ls := .nil) (vs := .nil) (pre := []) ?_ rfl (RunS.ret2 ?_)
    all_goals simp [Prog.sub, Prog.subU, Prog.view, env_right hlen, hN1]
  | succ k ih =>
    intro a hle
    obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
    obtain ⟨pf1, h1⟩ := ih m (by omega)
    have hsc : (Tm.ofList env).toList ++ closuresS (Tm.ofList env).toList gid G ++
        F.spreadIn (some [false, false, true, false, true])
          ((Tm.cons (.fv 52) (.cons (.fv 51) (.cons (.fv 53) .nil))).toList.map
            (P.sub (env ++ [.clo (.ofList env) gid 0] ++ [.nat (m + 1), .nat (k + 1), .tok] ++
              (Tm.cons (.nat k) .nil).toList ++ (Tm.cons (.nat m) .nil).toList ++ List.replicate 1 .tok))) =
        env ++ [.clo (.ofList env) gid 0] ++ [.nat m, .nat k, .tok] := by
      simp [Tm.toList_ofList, closuresS_one hGf hdl, FnDef.spreadIn, hers, hnp, filt, spread, Tm.toList, Prog.sub,
        Prog.subU, env_right hlen]
    rw [← hsc] at h1
    rw [hb]; unfold subModel
    rw [show m + 1 - (k + 1) = m - k by omega]
    apply Exists.intro
    refine RunS.case (d := 6) (c := 1) (ls := .nil) (vs := .cons (.nat k) .nil) ?_ rfl ?_
    · simp [Prog.sub, Prog.subU, Prog.view, env_right hlen, hN1]
    refine RunS.case (d := 6) (c := 1) (ls := .nil) (vs := .cons (.nat m) .nil) ?_ rfl ?_
    · simp [Prog.sub, Prog.subU, Prog.view, env_right hlen, hN1]
    refine RunS.mtchE (RunS.call (env := .ofList env) (G := G) (F := F) (outs := [.nat (m - k), pf1]) ?_ hG hF h1
      (RunS.chk ?_))
    · simp [Prog.sub, Prog.subU, env_right hlen]
    have hso : F.spreadOut (some [false, false, true, false, true])
        ((Tm.fv 52).cons ((Tm.fv 51).cons ((Tm.fv 53).cons Tm.nil))).toList.length [Tm.nat (m - k), pf1] =
        [.nat (m - k), .tok] := by simp [FnDef.spreadOut, hers, hnp, filt, spread, Tm.toList]
    rw [hso]
    refine RunS.ret2 ?_
    simp [Prog.sub, Prog.subU, env_right hlen, Tm.toList, Tm.len]

def Prog.nativeMul (P : Prog) (env : List Tm) (G : Group) (j : Nat) (F : FnDef) : List Tm → Option (List Tm)
  | [.nat a, .nat b] =>
    if P.isModel env G j F 45 2 [false, false, false, true] mulModel && P.isAddClo (env.getD 34 .nil) then
      some [.nat (a * b), .tok] else none
  | _ => none

theorem nativeMul_run {P : Prog} {env : List Tm} {gid j : Nat} {G : Group} {F : FnDef} {xs outs : List Tm}
    {ve : Option (List Bool)} {n : Nat} (hG : P.groups[gid]? = some G) (hF : G.fns[j]? = some F)
    (h : P.nativeMul env G j F xs = some outs) :
    ∃ outs', RunS P (env ++ closuresS env gid G ++ xs) F.body outs' ∧ F.spreadOut ve n outs' = F.spreadOut ve n outs := by
  unfold Prog.nativeMul at h
  split at h
  · rename_i a b
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hl, rfl, hGf, hnp, hers, hdl, hb, hN⟩ := Prog.isModel_spec hc.1 hF
      cases h
      rw [closuresS_one hGf hdl]
      obtain ⟨pf, hr⟩ := mul_run hN hl hG hGf hb hers hnp hdl hc.2 a b
      exact ⟨_, hr, by simp [FnDef.spreadOut, hers, hnp, filt]⟩
    · cases h
  · cases h

def Prog.cloModel (P : Prog) (v : Tm) (n np : Nat) (ers : List Bool) (M : Core) : Option (List Tm × Nat × Group × FnDef) :=
  match v with
  | .clo e gid 0 => match P.groups[gid]? with
    | some G => match G.fns with
      | [F] => if e.isList = true ∧ P.isModel e.toList G 0 F n np ers M = true then some (e.toList, gid, G, F) else none
      | _ => none
    | none => none
  | _ => none

theorem Prog.cloModel_spec {P : Prog} {v : Tm} {n np : Nat} {ers : List Bool} {M : Core} {envA : List Tm} {gidA : Nat}
    {GA : Group} {FA : FnDef} (h : P.cloModel v n np ers M = some (envA, gidA, GA, FA)) :
    v = .clo (.ofList envA) gidA 0 ∧ P.groups[gidA]? = some GA ∧ GA.fns = [FA] ∧ envA.length = n ∧ FA.np = np ∧
      FA.tele.ers = ers ∧ FA.dele = none ∧ FA.body = M ∧ NatFacts P := by
  cases v with
  | clo e gid j =>
    cases j with
    | succ _ => simp [Prog.cloModel] at h
    | zero =>
      cases hG : P.groups[gid]? with
      | none => simp [Prog.cloModel, hG] at h
      | some G =>
        cases hGf : G.fns with
        | nil => simp [Prog.cloModel, hG, hGf] at h
        | cons F rest =>
          cases rest with
          | cons _ _ => simp [Prog.cloModel, hG, hGf] at h
          | nil =>
            simp only [Prog.cloModel, hG, hGf] at h
            split at h
            · rename_i hc
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              have hF : G.fns[0]? = some F := by simp [hGf]
              obtain ⟨hl, -, hGf', hnp, hers, hdl, hb, hN⟩ := Prog.isModel_spec hc.2 hF
              exact ⟨by rw [Tm.ofList_toList' _ hc.1], hG, hGf', hl, hnp, hers, hdl, hb, hN⟩
            · cases h
  | _ => simp [Prog.cloModel] at h

theorem filt6 {o : List Tm} (hl : o.length = 6) : filt [false, false, true, true, true, true] o = o.take 2 := by
  match o, hl with
  | [_, _, _, _, _, _], _ => rfl

theorem succdiv_run {P : Prog} (hN : NatFacts P) {env : List Tm} {gid : Nat} {G : Group} {F : FnDef} (hlen : env.length = 49)
    (hG : P.groups[gid]? = some G) (hGf : G.fns = [F]) (hb : F.body = succDivModel)
    {envC : List Tm} {gidC : Nat} {GC : Group} {FC : FnDef}
    (hcmp : P.cloModel (env.getD 40 .nil) 40 2 [false, false, false] cmpModel = some (envC, gidC, GC, FC)) :
    ∀ q r c, r < c → ∃ outs, RunS P (env ++ [.clo (.ofList env) gid 0] ++
      [.nat q, .nat r, .nat c, .tok, .tok, .tok, .tok, .tok]) F.body outs ∧ outs.length = 6 ∧
      outs.take 2 = [.nat (if r + 1 < c then q else q + 1), .nat (if r + 1 < c then r + 1 else 0)] := by
  have hN1 := hN.nat
  obtain ⟨hv, hGC, hGCf, hlC, hnpC, hersC, hdlC, hbC, -⟩ := Prog.cloModel_spec hcmp
  have hFC : GC.fns[0]? = some FC := by simp [hGCf]
  intro q r c hrc
  have hcr := cmp_run hN hlC hGC hGCf hbC hersC hnpC hdlC (r + 1) c
  rw [← closuresS_one (env := envC) hGCf hdlC] at hcr
  have hsp : (Tm.ofList envC).toList ++ closuresS (Tm.ofList envC).toList gidC GC ++
      FC.spreadIn (some [false, false, false])
        ((Tm.cons (.app (.vc 6 1 .nil) (.cons (.fv 51) .nil)) (.cons (.fv 52) .nil)).toList.map
          (P.sub (env ++ [.clo (.ofList env) gid 0] ++ [.nat q, .nat r, .nat c, .tok, .tok, .tok, .tok, .tok]))) =
      envC ++ closuresS envC gidC GC ++ [.nat (r + 1), .nat c] := by
    simp [Tm.toList_ofList, FnDef.spreadIn, hersC, hnpC, filt, spread, Tm.toList, Prog.sub, Prog.subU, Prog.subUArgs,
      env_right hlen, hN.w61, hN.e61, maskArgs, Prog.norm, hN1, Tm.subst]
  rw [← hsp] at hcr
  rw [hb]; unfold succDivModel
  rcases Nat.lt_or_ge (r + 1) c with h | h
  · apply Exists.intro
    constructor
    · apply RunS.call (env := .ofList envC) (G := GC) (F := FC) (outs := [cmpVal (r + 1) c]) ?hf hGC hFC hcr ?rest
      case hf => simp [Prog.sub, Prog.subU, env_left (show 40 < env.length by omega), ← hv]
      case rest =>
      have hso : FC.spreadOut (some [false, false, false])
          (Tm.cons (.app (.vc 6 1 .nil) (.cons (.fv 51) .nil)) (.cons (.fv 52) .nil)).toList.length [cmpVal (r + 1) c] =
          [cmpVal (r + 1) c] := by simp [FnDef.spreadOut, hersC, hnpC, filt, spread, Tm.toList]
      rw [hso]
      apply RunS.mtch' (pre := List.replicate 5 .tok) (vs := .ofList (List.replicate 5 .tok)) (c := 0) (d := 15)
      · simp [Prog.sub, Prog.subU, Prog.view, env_right hlen, cmpVal, cmpCode, h, Nat.ne_of_lt h, Tm.ofList]
      · rfl
      · exact RunS.callE RunS.ret
      · exact RunS.ret
    all_goals simp [Tm.toList, Prog.sub, Prog.subU, Prog.subUArgs, env_right hlen, h, hN.w61, hN.e61, maskArgs, Prog.norm,
      hN1, Tm.subst]
  · have he : r + 1 = c := by omega
    subst he
    apply Exists.intro
    constructor
    · apply RunS.call (env := .ofList envC) (G := GC) (F := FC) (outs := [cmpVal (r + 1) (r + 1)]) ?hf hGC hFC hcr ?rest
      case hf => simp [Prog.sub, Prog.subU, env_left (show 40 < env.length by omega), ← hv]
      case rest =>
      have hso : FC.spreadOut (some [false, false, false])
          (Tm.cons (.app (.vc 6 1 .nil) (.cons (.fv 51) .nil)) (.cons (.fv 52) .nil)).toList.length
          [cmpVal (r + 1) (r + 1)] = [cmpVal (r + 1) (r + 1)] := by
        simp [FnDef.spreadOut, hersC, hnpC, filt, spread, Tm.toList]
      rw [hso]
      apply RunS.mtch' (pre := List.replicate 3 .tok) (vs := .ofList (List.replicate 3 .tok)) (c := 1) (d := 15)
      · simp [Prog.sub, Prog.subU, Prog.view, env_right hlen, cmpVal, cmpCode, Tm.ofList]
      · rfl
      · exact RunS.callE (RunS.callE RunS.ret)
      · exact RunS.ret
    all_goals simp [Tm.toList, Prog.sub, Prog.subU, Prog.subUArgs, env_right hlen, hN.w61, hN.e61, hN.w60, hN.e60,
      maskArgs, Prog.norm, hN1, Tm.subst]

theorem succ_divmod (s c : Nat) (hc : 0 < c) :
    (if s % c + 1 < c then s / c else s / c + 1) = (s + 1) / c ∧
      (if s % c + 1 < c then s % c + 1 else 0) = (s + 1) % c := by
  have h1 := Nat.mod_add_div s c
  have h2 := Nat.mod_lt s hc
  split
  · have := ((Nat.div_mod_unique (a := s + 1) (d := s / c) (c := s % c + 1) hc).mpr ⟨by omega, by omega⟩)
    exact ⟨this.1.symm, this.2.symm⟩
  · have := ((Nat.div_mod_unique (a := s + 1) (d := s / c + 1) (c := 0) hc).mpr ⟨by rw [Nat.mul_add]; omega, hc⟩)
    exact ⟨this.1.symm, this.2.symm⟩

theorem spread6 {o : List Tm} (hl : o.length = 6) {x y : Tm} (ht : o.take 2 = [x, y]) :
    spread [false, false, true, true, true, true] (filt [false, false, true, true, true, true] o) =
      [x, y, .tok, .tok, .tok, .tok] := by
  match o, hl with
  | [_, _, _, _, _, _], _ => simp at ht; obtain ⟨rfl, rfl⟩ := ht; rfl

theorem divmod_run {P : Prog} (hN : NatFacts P) {env : List Tm} {gid : Nat} {G : Group} {F : FnDef} (hlen : env.length = 51)
    (hG : P.groups[gid]? = some G) (hGf : G.fns = [F]) (hb : F.body = divmodModel)
    (hers : F.tele.ers = [false, false, true, false, false, true, true, true, true]) (hnp : F.np = 3) (hdl : F.dele = none)
    {envS : List Tm} {gidS : Nat} {GS : Group} {FS : FnDef}
    (hsd : P.cloModel (env.getD 49 .nil) 49 8 [false, false, false, true, true, true, true, true, false, false, true, true,
      true, true] succDivModel = some (envS, gidS, GS, FS))
    {envC : List Tm} {gidC : Nat} {GC : Group} {FC : FnDef}
    (hcmp : P.cloModel (envS.getD 40 .nil) 40 2 [false, false, false] cmpModel = some (envC, gidC, GC, FC))
    {c : Nat} (hc : 0 < c) :
    ∀ s, ∃ outs, RunS P (env ++ [.clo (.ofList env) gid 0] ++ [.nat s, .nat c, .tok]) F.body outs ∧ outs.length = 6 ∧
      outs.take 2 = [.nat (s / c), .nat (s % c)] := by
  have hF : G.fns[0]? = some F := by simp [hGf]
  have hN1 := hN.nat
  obtain ⟨hvS, hGS, hGSf, hlS, hnpS, hersS, hdlS, hbS, -⟩ := Prog.cloModel_spec hsd
  have hFS : GS.fns[0]? = some FS := by simp [hGSf]
  intro s; induction s with
  | zero =>
    rw [hb]; unfold divmodModel
    apply Exists.intro
    constructor
    · exact RunS.case (d := 6) (c := 0) (ls := .nil) (vs := .nil) (pre := []) (by simp [Prog.sub, Prog.subU, Prog.view,
        env_right hlen, hN1]) rfl RunS.ret
    all_goals simp [Tm.toList, Prog.sub, Prog.subU, Prog.subUArgs, env_right hlen, hN.w60, hN.e60, maskArgs, Prog.norm,
      hN1, Tm.subst]
  | succ k ih =>
    obtain ⟨o1, h1, hl1, ht1⟩ := ih
    have hsc : (Tm.ofList env).toList ++ closuresS (Tm.ofList env).toList gid G ++
        F.spreadIn (some [false, false, true, false, false, true, true, true, true])
          ((Tm.cons (.fv 55) (.cons (.fv 53) (.cons (.fv 54) .nil))).toList.map
            (P.sub (env ++ [.clo (.ofList env) gid 0] ++ [.nat (k + 1), .nat c, .tok] ++ (Tm.cons (.nat k) .nil).toList))) =
        env ++ [.clo (.ofList env) gid 0] ++ [.nat k, .nat c, .tok] := by
      simp [Tm.toList_ofList, closuresS_one hGf hdl, FnDef.spreadIn, hers, hnp, filt, spread, Tm.toList, Prog.sub,
        Prog.subU, env_right hlen]
    rw [← hsc] at h1
    obtain ⟨o2, h2, hl2, ht2⟩ := succdiv_run hN hlS hGS hGSf hbS hcmp (k / c) (k % c) c (Nat.mod_lt k hc)
    rw [← closuresS_one (env := envS) hGSf hdlS] at h2
    obtain ⟨eq1, eq2⟩ := succ_divmod k c hc
    rw [eq1, eq2] at ht2
    rw [hb]; unfold divmodModel
    apply Exists.intro
    constructor
    · apply RunS.case (d := 6) (c := 1) (ls := .nil) (vs := .cons (.nat k) .nil) ?hs rfl ?body
      case hs => simp [Prog.sub, Prog.subU, Prog.view, env_right hlen, hN1]
      case body =>
      apply RunS.call (env := .ofList env) (G := G) (F := F) (outs := o1) ?hf hG hF h1 ?rest
      case hf => simp [Prog.sub, Prog.subU, env_right hlen]
      case rest =>
      have hso : F.spreadOut (some [false, false, true, false, false, true, true, true, true])
          ((Tm.cons (.fv 55) (.cons (.fv 53) (.cons (.fv 54) .nil)))).toList.length o1 =
          [.nat (k / c), .nat (k % c), .tok, .tok, .tok, .tok] := by
        simp only [FnDef.spreadOut, hers, hnp, Option.getD_some, Tm.toList, List.length]
        exact spread6 hl1 ht1
      rw [hso]
      apply RunS.chk; apply RunS.chk
      have hsp : (Tm.ofList envS).toList ++ closuresS (Tm.ofList envS).toList gidS GS ++
          FS.spreadIn (some [false, false, false, true, true, true, true, true, false, false, true, true, true, true])
            ((Tm.cons (.fv 56) (.cons (.fv 57) (.cons (.fv 53) (.cons (.fv 58) (.cons (.fv 55) (.cons (.fv 59)
              (.cons (.fv 60) (.cons (.fv 61) .nil)))))))).toList.map
              (P.sub (env ++ [.clo (.ofList env) gid 0] ++ [.nat (k + 1), .nat c, .tok] ++ (Tm.cons (.nat k) .nil).toList ++
                [.nat (k / c), .nat (k % c), .tok, .tok, .tok, .tok]))) =
          envS ++ closuresS envS gidS GS ++ [.nat (k / c), .nat (k % c), .nat c, .tok, .tok, .tok, .tok, .tok] := by
        simp [Tm.toList_ofList, FnDef.spreadIn, hersS, hnpS, filt, spread, Tm.toList, Prog.sub, Prog.subU, env_right hlen]
      apply RunS.call (env := .ofList envS) (G := GS) (F := FS) (outs := o2) ?hf2 hGS hFS (by rw [hsp]; exact h2) ?rest2
      case hf2 => simp [Prog.sub, Prog.subU, env_left (show 49 < env.length by omega), ← hvS]
      case rest2 =>
      have hso2 : FS.spreadOut (some [false, false, false, true, true, true, true, true, false, false, true, true, true, true])
          ((Tm.cons (.fv 56) (.cons (.fv 57) (.cons (.fv 53) (.cons (.fv 58) (.cons (.fv 55) (.cons (.fv 59)
              (.cons (.fv 60) (.cons (.fv 61) .nil))))))))).toList.length o2 =
          [.nat ((k + 1) / c), .nat ((k + 1) % c), .tok, .tok, .tok, .tok] := by
        simp only [FnDef.spreadOut, hersS, hnpS, Option.getD_some, Tm.toList, List.length]
        exact spread6 hl2 ht2
      rw [hso2]
      exact RunS.ret
    all_goals simp [Tm.toList, Prog.sub, Prog.subU, env_right hlen]

theorem spread3 {o : List Tm} (hl : o.length = 3) {x : Tm} (ht : o.take 1 = [x]) :
    spread [false, true, true] (filt [false, true, true] o) = [x, .tok, .tok] := by
  match o, hl with
  | [_, _, _], _ => simp at ht; subst ht; rfl

theorem succmod_run {P : Prog} (hN : NatFacts P) {env : List Tm} {gid : Nat} {G : Group} {F : FnDef} (hlen : env.length = 78)
    (hG : P.groups[gid]? = some G) (hGf : G.fns = [F]) (hb : F.body = succModModel)
    {envC : List Tm} {gidC : Nat} {GC : Group} {FC : FnDef}
    (hcmp : P.cloModel (env.getD 40 .nil) 40 2 [false, false, false] cmpModel = some (envC, gidC, GC, FC)) :
    ∀ r c, r < c → ∃ outs, RunS P (env ++ [.clo (.ofList env) gid 0] ++ [.nat r, .nat c, .tok, .tok, .tok]) F.body outs ∧
      outs.length = 3 ∧ outs.take 1 = [.nat (if r + 1 < c then r + 1 else 0)] := by
  have hN1 := hN.nat
  obtain ⟨hv, hGC, hGCf, hlC, hnpC, hersC, hdlC, hbC, -⟩ := Prog.cloModel_spec hcmp
  have hFC : GC.fns[0]? = some FC := by simp [hGCf]
  intro r c hrc
  have hcr := cmp_run hN hlC hGC hGCf hbC hersC hnpC hdlC (r + 1) c
  rw [← closuresS_one (env := envC) hGCf hdlC] at hcr
  have hsp : (Tm.ofList envC).toList ++ closuresS (Tm.ofList envC).toList gidC GC ++
      FC.spreadIn (some [false, false, false])
        ((Tm.cons (.app (.vc 6 1 .nil) (.cons (.fv 79) .nil)) (.cons (.fv 80) .nil)).toList.map
          (P.sub (env ++ [.clo (.ofList env) gid 0] ++ [.nat r, .nat c, .tok, .tok, .tok]))) =
      envC ++ closuresS envC gidC GC ++ [.nat (r + 1), .nat c] := by
    simp [Tm.toList_ofList, FnDef.spreadIn, hersC, hnpC, filt, spread, Tm.toList, Prog.sub, Prog.subU, Prog.subUArgs,
      env_right hlen, hN.w61, hN.e61, maskArgs, Prog.norm, hN1, Tm.subst]
  rw [← hsp] at hcr
  have hso : ∀ v, FC.spreadOut (some [false, false, false])
      (Tm.cons (.app (.vc 6 1 .nil) (.cons (.fv 79) .nil)) (.cons (.fv 80) .nil)).toList.length [v] = [v] := by
    intro v; simp [FnDef.spreadOut, hersC, hnpC, filt, spread, Tm.toList]
  rw [hb]; unfold succModModel
  rcases Nat.lt_or_ge (r + 1) c with h | h
  · apply Exists.intro
    constructor
    · apply RunS.call (env := .ofList envC) (G := GC) (F := FC) (outs := [cmpVal (r + 1) c]) ?hf hGC hFC hcr ?rest
      case hf => simp [Prog.sub, Prog.subU, env_left (show 40 < env.length by omega), ← hv]
      case rest =>
      rw [hso]
      apply RunS.mtch' (pre := List.replicate 5 .tok) (vs := .ofList (List.replicate 5 .tok)) (c := 0) (d := 15)
      · simp [Prog.sub, Prog.subU, Prog.view, env_right hlen, cmpVal, cmpCode, h, Nat.ne_of_lt h, Tm.ofList]
      · rfl
      · exact RunS.callE RunS.ret
      · exact RunS.ret
    all_goals simp [Tm.toList, Prog.sub, Prog.subU, Prog.subUArgs, env_right hlen, h, hN.w61, hN.e61, maskArgs, Prog.norm,
      hN1, Tm.subst]
  · have he : r + 1 = c := by omega
    subst he
    apply Exists.intro
    constructor
    · apply RunS.call (env := .ofList envC) (G := GC) (F := FC) (outs := [cmpVal (r + 1) (r + 1)]) ?hf hGC hFC hcr ?rest
      case hf => simp [Prog.sub, Prog.subU, env_left (show 40 < env.length by omega), ← hv]
      case rest =>
      rw [hso]
      apply RunS.mtch' (pre := List.replicate 3 .tok) (vs := .ofList (List.replicate 3 .tok)) (c := 1) (d := 15)
      · simp [Prog.sub, Prog.subU, Prog.view, env_right hlen, cmpVal, cmpCode, Tm.ofList]
      · rfl
      · exact RunS.callE RunS.ret
      · exact RunS.ret
    all_goals simp [Tm.toList, Prog.sub, Prog.subU, Prog.subUArgs, env_right hlen, hN.w60, hN.e60, maskArgs, Prog.norm,
      hN1, Tm.subst]

theorem natmod_run {P : Prog} (hN : NatFacts P) {env : List Tm} {gid : Nat} {G : Group} {F : FnDef} (hlen : env.length = 80)
    (hG : P.groups[gid]? = some G) (hGf : G.fns = [F]) (hb : F.body = natModModel)
    (hers : F.tele.ers = [false, false, true, false, true, true]) (hnp : F.np = 3) (hdl : F.dele = none)
    {envS : List Tm} {gidS : Nat} {GS : Group} {FS : FnDef}
    (hsm : P.cloModel (env.getD 78 .nil) 78 5 [false, false, true, true, true, false, true, true] succModModel =
      some (envS, gidS, GS, FS))
    {envC : List Tm} {gidC : Nat} {GC : Group} {FC : FnDef}
    (hcmp : P.cloModel (envS.getD 40 .nil) 40 2 [false, false, false] cmpModel = some (envC, gidC, GC, FC))
    {c : Nat} (hc : 0 < c) :
    ∀ s, ∃ outs, RunS P (env ++ [.clo (.ofList env) gid 0] ++ [.nat s, .nat c, .tok]) F.body outs ∧ outs.length = 3 ∧
      outs.take 1 = [.nat (s % c)] := by
  have hF : G.fns[0]? = some F := by simp [hGf]
  have hN1 := hN.nat
  obtain ⟨hvS, hGS, hGSf, hlS, hnpS, hersS, hdlS, hbS, -⟩ := Prog.cloModel_spec hsm
  have hFS : GS.fns[0]? = some FS := by simp [hGSf]
  intro s; induction s with
  | zero =>
    rw [hb]; unfold natModModel
    apply Exists.intro
    constructor
    · exact RunS.case (d := 6) (c := 0) (ls := .nil) (vs := .nil) (pre := []) (by simp [Prog.sub, Prog.subU, Prog.view,
        env_right hlen, hN1]) rfl RunS.ret
    all_goals simp [Tm.toList, Prog.sub, Prog.subU, Prog.subUArgs, env_right hlen, hN.w60, hN.e60, maskArgs, Prog.norm,
      hN1, Tm.subst]
  | succ k ih =>
    obtain ⟨o1, h1, hl1, ht1⟩ := ih
    have hsc : (Tm.ofList env).toList ++ closuresS (Tm.ofList env).toList gid G ++
        F.spreadIn (some [false, false, true, false, true, true])
          ((Tm.cons (.fv 84) (.cons (.fv 82) (.cons (.fv 83) .nil))).toList.map
            (P.sub (env ++ [.clo (.ofList env) gid 0] ++ [.nat (k + 1), .nat c, .tok] ++ (Tm.cons (.nat k) .nil).toList))) =
        env ++ [.clo (.ofList env) gid 0] ++ [.nat k, .nat c, .tok] := by
      simp [Tm.toList_ofList, closuresS_one hGf hdl, FnDef.spreadIn, hers, hnp, filt, spread, Tm.toList, Prog.sub,
        Prog.subU, env_right hlen]
    rw [← hsc] at h1
    obtain ⟨o2, h2, hl2, ht2⟩ := succmod_run hN hlS hGS hGSf hbS hcmp (k % c) c (Nat.mod_lt k hc)
    rw [← closuresS_one (env := envS) hGSf hdlS] at h2
    rw [(succ_divmod k c hc).2] at ht2
    rw [hb]; unfold natModModel
    apply Exists.intro
    constructor
    · apply RunS.case (d := 6) (c := 1) (ls := .nil) (vs := .cons (.nat k) .nil) ?hs rfl ?body
      case hs => simp [Prog.sub, Prog.subU, Prog.view, env_right hlen, hN1]
      case body =>
      apply RunS.call (env := .ofList env) (G := G) (F := F) (outs := o1) ?hf hG hF h1 ?rest
      case hf => simp [Prog.sub, Prog.subU, env_right hlen]
      case rest =>
      have hso : F.spreadOut (some [false, false, true, false, true, true])
          ((Tm.cons (.fv 84) (.cons (.fv 82) (.cons (.fv 83) .nil)))).toList.length o1 = [.nat (k % c), .tok, .tok] := by
        simp only [FnDef.spreadOut, hers, hnp, Option.getD_some, Tm.toList, List.length]
        exact spread3 hl1 ht1
      rw [hso]
      apply RunS.chk
      have hsp : (Tm.ofList envS).toList ++ closuresS (Tm.ofList envS).toList gidS GS ++
          FS.spreadIn (some [false, false, true, true, true, false, true, true])
            ((Tm.cons (.fv 85) (.cons (.fv 82) (.cons (.fv 84) (.cons (.fv 86) (.cons (.fv 87) .nil))))).toList.map
              (P.sub (env ++ [.clo (.ofList env) gid 0] ++ [.nat (k + 1), .nat c, .tok] ++ (Tm.cons (.nat k) .nil).toList ++
                [.nat (k % c), .tok, .tok]))) =
          envS ++ closuresS envS gidS GS ++ [.nat (k % c), .nat c, .tok, .tok, .tok] := by
        simp [Tm.toList_ofList, FnDef.spreadIn, hersS, hnpS, filt, spread, Tm.toList, Prog.sub, Prog.subU, env_right hlen]
      apply RunS.call (env := .ofList envS) (G := GS) (F := FS) (outs := o2) ?hf2 hGS hFS (by rw [hsp]; exact h2) ?rest2
      case hf2 => simp [Prog.sub, Prog.subU, env_left (show 78 < env.length by omega), ← hvS]
      case rest2 =>
      have hso2 : FS.spreadOut (some [false, false, true, true, true, false, true, true])
          ((Tm.cons (.fv 85) (.cons (.fv 82) (.cons (.fv 84) (.cons (.fv 86) (.cons (.fv 87) .nil)))))).toList.length o2 =
          [.nat ((k + 1) % c), .tok, .tok] := by
        simp only [FnDef.spreadOut, hersS, hnpS, Option.getD_some, Tm.toList, List.length]
        exact spread3 hl2 ht2
      rw [hso2]
      exact RunS.ret
    all_goals simp [Tm.toList, Prog.sub, Prog.subU, env_right hlen]

def Prog.nativeSub (P : Prog) (env : List Tm) (G : Group) (j : Nat) (F : FnDef) : List Tm → Option (List Tm)
  | [.nat a, .nat b, .tok] =>
    if b ≤ a ∧ P.isModel env G j F 47 3 [false, false, true, false, true] subModel = true then
      some [.nat (a - b), .tok] else none
  | _ => none

theorem nativeSub_run {P : Prog} {env : List Tm} {gid j : Nat} {G : Group} {F : FnDef} {xs outs : List Tm}
    {ve : Option (List Bool)} {n : Nat} (hG : P.groups[gid]? = some G) (hF : G.fns[j]? = some F)
    (h : P.nativeSub env G j F xs = some outs) :
    ∃ outs', RunS P (env ++ closuresS env gid G ++ xs) F.body outs' ∧ F.spreadOut ve n outs' = F.spreadOut ve n outs := by
  unfold Prog.nativeSub at h
  split at h
  · rename_i a b
    split at h
    · rename_i hc
      obtain ⟨hl, rfl, hGf, hnp, hers, hdl, hb, hN⟩ := Prog.isModel_spec hc.2 hF
      cases h
      rw [closuresS_one hGf hdl]
      obtain ⟨pf, hr⟩ := sub_run hN hl hG hGf hb hers hnp hdl b a hc.1
      exact ⟨_, hr, by simp [FnDef.spreadOut, hers, hnp, filt]⟩
    · cases h
  · cases h

def divmodErs : List Bool := [false, false, true, false, false, true, true, true, true]
def succDivErs : List Bool := [false, false, false, true, true, true, true, true, false, false, true, true, true, true]
def natModErs : List Bool := [false, false, true, false, true, true]
def succModErs : List Bool := [false, false, true, true, true, false, true, true]

def Prog.nativeDivmod (P : Prog) (env : List Tm) (G : Group) (j : Nat) (F : FnDef) : List Tm → Option (List Tm)
  | [.nat s, .nat c, .tok] =>
    if 0 < c ∧ P.isModel env G j F 51 3 divmodErs divmodModel = true then
      match P.cloModel (env.getD 49 .nil) 49 8 succDivErs succDivModel with
      | some (envS, _, _, _) =>
        if (P.cloModel (envS.getD 40 .nil) 40 2 [false, false, false] cmpModel).isSome then
          some [.nat (s / c), .nat (s % c), .tok, .tok, .tok, .tok] else none
      | none => none
    else none
  | _ => none

def Prog.nativeMod (P : Prog) (env : List Tm) (G : Group) (j : Nat) (F : FnDef) : List Tm → Option (List Tm)
  | [.nat s, .nat c, .tok] =>
    if 0 < c ∧ P.isModel env G j F 80 3 natModErs natModModel = true then
      match P.cloModel (env.getD 78 .nil) 78 5 succModErs succModModel with
      | some (envS, _, _, _) =>
        if (P.cloModel (envS.getD 40 .nil) 40 2 [false, false, false] cmpModel).isSome then
          some [.nat (s % c), .tok, .tok] else none
      | none => none
    else none
  | _ => none

theorem nativeDivmod_run {P : Prog} {env : List Tm} {gid j : Nat} {G : Group} {F : FnDef} {xs outs : List Tm}
    {ve : Option (List Bool)} {n : Nat} (hG : P.groups[gid]? = some G) (hF : G.fns[j]? = some F)
    (h : P.nativeDivmod env G j F xs = some outs) :
    ∃ outs', RunS P (env ++ closuresS env gid G ++ xs) F.body outs' ∧ F.spreadOut ve n outs' = F.spreadOut ve n outs := by
  unfold Prog.nativeDivmod at h
  split at h
  · rename_i s c
    split at h
    · rename_i hc
      obtain ⟨hl, rfl, hGf, hnp, hers, hdl, hb, hN⟩ := Prog.isModel_spec hc.2 hF
      split at h
      · rename_i envS gidS GS FS hsd
        split at h
        · rename_i hcm
          obtain ⟨⟨envC, gidC, GC, FC⟩, hcm⟩ := Option.isSome_iff_exists.mp hcm
          cases h
          rw [closuresS_one hGf hdl]
          obtain ⟨o, hr, hl6, ht⟩ := divmod_run hN hl hG hGf hb hers hnp hdl hsd hcm hc.1 s
          refine ⟨o, hr, ?_⟩
          simp [FnDef.spreadOut, hers, hnp, divmodErs, filt6 hl6, ht, filt]
        · cases h
      · cases h
    · cases h
  · cases h

theorem nativeMod_run {P : Prog} {env : List Tm} {gid j : Nat} {G : Group} {F : FnDef} {xs outs : List Tm}
    {ve : Option (List Bool)} {n : Nat} (hG : P.groups[gid]? = some G) (hF : G.fns[j]? = some F)
    (h : P.nativeMod env G j F xs = some outs) :
    ∃ outs', RunS P (env ++ closuresS env gid G ++ xs) F.body outs' ∧ F.spreadOut ve n outs' = F.spreadOut ve n outs := by
  unfold Prog.nativeMod at h
  split at h
  · rename_i s c
    split at h
    · rename_i hc
      obtain ⟨hl, rfl, hGf, hnp, hers, hdl, hb, hN⟩ := Prog.isModel_spec hc.2 hF
      split at h
      · rename_i envS gidS GS FS hsm
        split at h
        · rename_i hcm
          obtain ⟨⟨envC, gidC, GC, FC⟩, hcm⟩ := Option.isSome_iff_exists.mp hcm
          cases h
          rw [closuresS_one hGf hdl]
          obtain ⟨o, hr, hl3, ht⟩ := natmod_run hN hl hG hGf hb hers hnp hdl hsm hcm hc.1 s
          refine ⟨o, hr, ?_⟩
          match o, hl3 with
          | [_, _, _], _ =>
            simp at ht; subst ht
            simp [FnDef.spreadOut, hers, hnp, natModErs, filt]
        · cases h
      · cases h
    · cases h
  · cases h

def Prog.native (P : Prog) (env : List Tm) (G : Group) (j : Nat) (F : FnDef) (xs : List Tm) : Option (List Tm) :=
  [P.nativeAdd, P.nativeCmp, P.nativeMul, P.nativeSub, P.nativeDivmod, P.nativeMod].findSome? fun f => f env G j F xs

theorem native_run {P : Prog} {env : List Tm} {gid j : Nat} {G : Group} {F : FnDef} {xs outs : List Tm} {ve : Option (List Bool)} {n : Nat}
    (hG : P.groups[gid]? = some G) (hF : G.fns[j]? = some F) (h : P.native env G j F xs = some outs) :
    ∃ outs', RunS P (env ++ closuresS env gid G ++ xs) F.body outs' ∧ F.spreadOut ve n outs' = F.spreadOut ve n outs := by
  simp only [Prog.native, List.findSome?_cons, List.findSome?_nil] at h
  cases h1 : P.nativeAdd env G j F xs with
  | some o => rw [h1] at h; cases h; exact nativeAdd_run hG hF h1
  | none =>
  rw [h1] at h; simp only at h
  cases h2 : P.nativeCmp env G j F xs with
  | some o => rw [h2] at h; cases h; exact nativeCmp_run hG hF h2
  | none =>
  rw [h2] at h; simp only at h
  cases h3 : P.nativeMul env G j F xs with
  | some o => rw [h3] at h; cases h; exact nativeMul_run hG hF h3
  | none =>
  rw [h3] at h; simp only at h
  cases h4 : P.nativeSub env G j F xs with
  | some o => rw [h4] at h; cases h; exact nativeSub_run hG hF h4
  | none =>
  rw [h4] at h; simp only at h
  cases h5 : P.nativeDivmod env G j F xs with
  | some o => rw [h5] at h; cases h; exact nativeDivmod_run hG hF h5
  | none =>
  rw [h5] at h; simp only at h
  cases h6 : P.nativeMod env G j F xs with
  | some o => rw [h6] at h; cases h; exact nativeMod_run hG hF h6
  | none => rw [h6] at h; cases h

variable (P : Prog)

def runS : Nat → List Tm → Core → Option (List Tm)
  | 0, _, _ => none
  | fuel + 1, ρ, c => match c with
    | .ret ts => some (ts.toList.map (P.sub ρ))
    | .call _ _ _ true ms _ rest => runS fuel (ρ ++ List.replicate ms.length .tok) rest
    | .call f _ args false _ ve rest => match P.sub ρ f with
      | .clo env gid j => do
        let G ← P.groups[gid]?
        let F ← G.fns[j]?
        let xs := F.spreadIn ve (args.toList.map (P.sub ρ))
        let outs ← (P.native env.toList G j F xs).orElse fun _ => runS fuel (env.toList ++ closuresS env.toList gid G ++ xs) F.body
        runS fuel (ρ ++ F.spreadOut ve args.toList.length outs) rest
      | _ => none
    | .mtch _ R _ _ true rest => runS fuel (ρ ++ List.replicate R.len .tok) rest
    | .mtch s _ brs els false rest => match P.view (P.sub ρ s) with
      | .app (.vc _ c _) vs => do
        let (pre, body) ← selectBr brs els c vs.toList
        let outs ← runS fuel (ρ ++ pre) body
        runS fuel (ρ ++ outs) rest
      | _ => none
    | .case _ brs els true _ => do
      let (pre, body) ← realBr brs els
      runS fuel (ρ ++ pre) body
    | .case s brs els false true => do
      let (pre, body) ← realBr brs els
      runS fuel (ρ ++ pre.map fun _ => P.sub ρ s) body
    | .case s brs els false false => match P.view (P.sub ρ s) with
      | .app (.vc _ c _) vs => do
        let (pre, body) ← selectBr brs els c vs.toList
        runS fuel (ρ ++ pre) body
      | _ => none
    | .seq _ body rest => do
      let outs ← runS fuel ρ body
      runS fuel (ρ ++ outs) rest
    | .prim p er rest => runS fuel (ρ ++ [if er then .tok else p.evalS P ρ]) rest
    | .wdo w req rest => runS fuel (ρ ++ [(Prim.wNext w).evalS P ρ, (Prim.wAsk w req).evalS P ρ]) rest
    | .defLvl rest => runS fuel (ρ ++ [.tok]) rest
    | .defFns gid rest => do runS fuel (ρ ++ closuresS ρ gid (← P.groups[gid]?)) rest
    | .chk _ _ _ rest => runS fuel ρ rest
    | .absurd _ | .dead => none

variable {P} in
theorem runS_sound : ∀ fuel ρ c out, runS P fuel ρ c = some out → RunS P ρ c out := by
  intro fuel; induction fuel with
  | zero => intro _ _ _ h; simp [runS] at h
  | succ fuel ih =>
    intro ρ c out h
    unfold runS at h
    split at h
    · cases h; exact .ret
    · exact .callE (ih _ _ _ h)
    · split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨G, hG, F, hF, outs, hb, hr⟩ := h
        cases hn : P.native _ G _ F _ with
        | none =>
          rw [hn] at hb
          exact .call ‹_› hG hF (ih _ _ _ hb) (ih _ _ _ hr)
        | some outs' =>
          rw [hn] at hb; cases hb
          obtain ⟨outs2, hb2, hsp⟩ := native_run hG hF hn
          exact .call ‹_› hG hF hb2 (hsp ▸ ih _ _ _ hr)
      · simp at h
    · exact .mtchE (ih _ _ _ h)
    · split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨⟨pre, body⟩, hsel, outs, hb, hr⟩ := h
        exact .mtch ‹_› hsel (ih _ _ _ hb) (ih _ _ _ hr)
      · simp at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨pre, body⟩, hsel, hb⟩ := h
      exact .caseE hsel (ih _ _ _ hb)
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨pre, body⟩, hsel, hb⟩ := h
      exact .caseN hsel (ih _ _ _ hb)
    · split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨⟨pre, body⟩, hsel, hb⟩ := h
        exact .case ‹_› hsel (ih _ _ _ hb)
      · simp at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨outs, hb, hr⟩ := h
      exact .seq (ih _ _ _ hb) (ih _ _ _ hr)
    · exact .prim (ih _ _ _ h)
    · exact .wdo (ih _ _ _ h)
    · exact .defLvl (ih _ _ _ h)
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨G, hG, hr⟩ := h
      exact .defFns hG (ih _ _ _ hr)
    · exact .chk (ih _ _ _ h)
    · simp at h
    · simp at h


def Tm.toArrAux : Tm → Array Tm → Array Tm
  | .cons h t, acc => Tm.toArrAux t (acc.push h)
  | _, acc => acc

theorem Tm.toArrAux_toList : ∀ (t : Tm) (acc : Array Tm), (t.toArrAux acc).toList = acc.toList ++ t.toList
  | .cons h t, acc => by simp [Tm.toArrAux, Tm.toArrAux_toList t, Tm.toList]
  | .fv _, _ | .bv _, _ | .nil, _ | .bind .., _ | .app .., _ | .tyc .., _ | .vc .., _ | .tyCtor _, _ | .valCtor _, _
  | .univ, _ | .level, _ | .predates .., _ | .subterm .., _ | .fn .., _ | .mtbl .., _ | .lvl _, _ | .tok, _
  | .clo .., _ | .nat _, _ | .ptr _, _ | .wld _, _ => by simp [Tm.toArrAux, Tm.toList]

def cvalT (env : Tm) (gid : Nat) (acc : List Tm) (F : FnDef) : Tm := match F.dele with
  | some t => (env.toList ++ acc).getD t .nil
  | none => .clo env gid acc.length

def closuresA (env : Tm) (gid : Nat) (G : Group) : List Tm :=
  if env.isList then G.fns.foldl (fun acc F => acc ++ [cvalT env gid acc F]) [] else closuresS env.toList gid G

theorem closuresA_eq (env : Tm) (gid : Nat) (G : Group) : closuresA env gid G = closuresS env.toList gid G := by
  unfold closuresA; split
  · rename_i h
    have : ∀ acc F, cvalT env gid acc F = cval env.toList gid acc F := by
      intro acc F; unfold cvalT cval; cases F.dele <;> simp [Tm.ofList_toList' env h]
    simp only [closuresS, this]
  · rfl

def natArgs : List Tm → Bool
  | .nat _ :: .nat _ :: _ => true
  | _ => false

theorem native_guard (env : List Tm) (G : Group) (j : Nat) (F : FnDef) (xs : List Tm) :
    (if natArgs xs then P.native env G j F xs else none) = P.native env G j F xs := by
  split
  · rfl
  · rename_i h
    match xs, h with
    | [], _ | [_], _ => simp [Prog.native, List.findSome?_cons, Prog.nativeAdd, Prog.nativeCmp, Prog.nativeMul,
        Prog.nativeSub, Prog.nativeDivmod, Prog.nativeMod]
    | a :: b :: r, h =>
      cases a <;> (try cases b) <;> simp_all [natArgs, Prog.native, List.findSome?_cons, Prog.nativeAdd,
        Prog.nativeCmp, Prog.nativeMul, Prog.nativeSub, Prog.nativeDivmod, Prog.nativeMod]

def Prog.subA (ρ : Array Tm) (t : Tm) : Tm := P.subU (fun i => ρ.getD i .nil) t

theorem Prog.subA_eq (ρ : Array Tm) : P.subA ρ = P.sub ρ.toList := by
  funext t; simp only [Prog.subA, Prog.sub]; congr 1; funext i
  simp [Tm.env, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

def Prim.evalA (ρ : Array Tm) : Prim → Tm
  | .tm t | .lit t | .coerce t _ _ | .place t _ | .unplace t _ => P.subA ρ t
  | .num _ n => .nat n
  | .atom d => .app (.vc d 0 .nil) .nil
  | .assert t _ => t
  | .wAsk w req => (P.answer (P.subA ρ w) (P.subA ρ req)).1
  | .wNext w => (P.subA ρ w).wnext
  | p => p.eval P ρ.toList

theorem Prim.evalA_eq (ρ : Array Tm) (p : Prim) : p.evalA P ρ = p.evalS P ρ.toList := by
  cases p <;> simp [Prim.evalA, Prim.evalS, Prim.eval, Prog.subA_eq]

def runA : Nat → Array Tm → Core → Option (List Tm)
  | 0, _, _ => none
  | fuel + 1, ρ, c => match c with
    | .ret ts => some (ts.toList.map (P.subA ρ))
    | .call _ _ _ true ms _ rest => runA fuel (ρ ++ List.replicate ms.length Tm.tok) rest
    | .call f _ args false _ ve rest => match P.subA ρ f with
      | .clo env gid j => do
        let G ← P.groups[gid]?
        let F ← G.fns[j]?
        let xs := F.spreadIn ve (args.toList.map (P.subA ρ))
        let outs ← (if natArgs xs then P.native env.toList G j F xs else none).orElse fun _ =>
          runA fuel (env.toArrAux #[] ++ closuresA env gid G ++ xs) F.body
        runA fuel (ρ ++ F.spreadOut ve args.toList.length outs) rest
      | _ => none
    | .mtch _ R _ _ true rest => runA fuel (ρ ++ List.replicate R.len Tm.tok) rest
    | .mtch s _ brs els false rest => match P.view (P.subA ρ s) with
      | .app (.vc _ c _) vs => do
        let (pre, body) ← selectBr brs els c vs.toList
        let outs ← runA fuel (ρ ++ pre) body
        runA fuel (ρ ++ outs) rest
      | _ => none
    | .case _ brs els true _ => do
      let (pre, body) ← realBr brs els
      runA fuel (ρ ++ pre) body
    | .case s brs els false true => do
      let (pre, body) ← realBr brs els
      runA fuel (ρ ++ pre.map fun _ => P.subA ρ s) body
    | .case s brs els false false => match P.view (P.subA ρ s) with
      | .app (.vc _ c _) vs => do
        let (pre, body) ← selectBr brs els c vs.toList
        runA fuel (ρ ++ pre) body
      | _ => none
    | .seq _ body rest => do
      let outs ← runA fuel ρ body
      runA fuel (ρ ++ outs) rest
    | .prim p er rest => runA fuel (ρ.push (if er then .tok else p.evalA P ρ)) rest
    | .wdo w req rest => runA fuel ((ρ.push ((Prim.wNext w).evalA P ρ)).push ((Prim.wAsk w req).evalA P ρ)) rest
    | .defLvl rest => runA fuel (ρ.push .tok) rest
    | .defFns gid rest => do runA fuel (ρ ++ closuresS ρ.toList gid (← P.groups[gid]?)) rest
    | .chk _ _ _ rest => runA fuel ρ rest
    | .absurd _ | .dead => none

theorem runA_eq : ∀ fuel (ρ : Array Tm) c, runA P fuel ρ c = runS P fuel ρ.toList c := by
  intro fuel; induction fuel with
  | zero => intro ρ c; simp [runA, runS]
  | succ fuel ih =>
    intro ρ c
    have e := Prog.subA_eq P ρ
    cases c with
    | call f d args er ms ve rest => cases er <;> simp [runA, runS, ih, e, native_guard, closuresA_eq, Tm.toArrAux_toList]
    | mtch s R brs els er rest => cases er <;> simp [runA, runS, ih, e]
    | case s brs els er nt => cases er <;> cases nt <;> simp [runA, runS, ih, e]
    | prim p er rest => simp [runA, runS, ih, Prim.evalA_eq]
    | wdo w req rest => simp [runA, runS, ih, Prim.evalA_eq]
    | _ => simp [runA, runS, ih, e]

@[simp] theorem runA_toArray (fuel : Nat) (l : List Tm) (c : Core) : runA P fuel l.toArray c = runS P fuel l c := by
  rw [runA_eq]

end Minimal
