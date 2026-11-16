/- E081 | Quotients | 3 min | Setoid, Quotient.mk, Quotient.lift, Quotient.sound, Quotient.exact
GOAL
  `Parity` is ℕ modulo "same remainder mod 2". Define `Parity.isEven` with `Quotient.lift` (proving it
  respects the relation), then show when two classes are equal.

REFERENCE
  #check @Quotient.mk     -- (s : Setoid α) → α → Quotient s          the class of `a`
  #check @Quotient.lift   -- (f : α → β) → (∀ a b, a ≈ b → f a = f b) → Quotient s → β
  #check @Quotient.sound  -- a ≈ b → Quotient.mk s a = Quotient.mk s b
  #check @Quotient.exact  -- Quotient.mk s a = Quotient.mk s b → a ≈ b
  example {α β : Type} {s : Setoid α} (f : α → β) (h : ∀ a b, a ≈ b → f a = f b) (a : α) :
      Quotient.lift f h (Quotient.mk s a) = f a := rfl     -- lift computes on a representative
NOTE: here `a ≈ b` means `parityRel.r a b`, i.e. `a % 2 = b % 2`; write `fun a b (h : a % 2 = b % 2) => …` to see it.
-/

namespace E081

-- BEGIN SPEC
def parityRel : Setoid Nat where
  r a b := a % 2 = b % 2
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

def Parity : Type := Quotient parityRel

def Parity.mk (n : Nat) : Parity := Quotient.mk parityRel n
-- END SPEC

-- BEGIN SPEC
def Parity.isEven : Parity → Bool :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem isEven_mk (n : Nat) : (Parity.mk n).isEven = (n % 2 == 0) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem mk_three_seven : Parity.mk 3 = Parity.mk 7 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem mk_eq_iff (a b : Nat) : Parity.mk a = Parity.mk b ↔ a % 2 = b % 2 :=
-- END SPEC
  sorry

end E081

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A function out of a quotient is a function on representatives plus a proof that related
    representatives give the same answer. Equal classes come from related representatives, and back.
H2. Lift `fun n => n % 2 == 0`; its obligation is `a % 2 = b % 2 → (a % 2 == 0) = (b % 2 == 0)`
    (rewrite or `simp` with the hypothesis). Then `isEven_mk` holds by `rfl`.
H3. `Quotient.lift (fun n => n % 2 == 0) (fun a b (h : a % 2 = b % 2) => by simp [h])`;
    `mk_three_seven` is `Quotient.sound` applied to a proof of `3 % 2 = 7 % 2`; `mk_eq_iff` pairs
    `Quotient.exact` and `Quotient.sound` (wrap each as `fun h => … h` so Lean can infer the setoid).
-/
