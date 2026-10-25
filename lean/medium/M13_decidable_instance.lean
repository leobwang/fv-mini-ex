/- M13 | Decidable instance | 10-15 min | Decidable, DecidablePred, decidable_of_iff, decide
GOAL
  `IsSquare n` quantifies over all `k`, so Lean cannot decide it. Provide a `DecidablePred`
  instance by reducing it to a bounded search, then let `decide` settle concrete cases.

REFERENCE
  -- decidable_of_iff (q : Prop) (h : q ↔ p) [Decidable q] : Decidable p
  def IsSmall (n : Nat) : Prop := ∃ k, k < 3 ∧ k = n
  instance : DecidablePred IsSmall := fun n => decidable_of_iff (n < 3) (by
    constructor
    · intro h; exact ⟨n, h, rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact hk)
  example : IsSmall 2 := by decide       -- bounded `∃ k, k ≤ n ∧ ...` is decidable already
  #check Nat.le_mul_self   -- (n : Nat) : n ≤ n * n
-/

namespace M13

-- BEGIN SPEC
def IsSquare (n : Nat) : Prop := ∃ k, k * k = n
-- END SPEC

-- BEGIN SPEC
instance decIsSquare : DecidablePred IsSquare :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem square_49 : IsSquare 49 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem not_square_50 : ¬ IsSquare 50 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. If `k * k = n` then `k ≤ n`, so it is enough to search `k ≤ n`.
H2. `decidable_of_iff (∃ k, k ≤ n ∧ k * k = n) proof`, where `proof` shows the two statements are equivalent.
H3. For ←: `rintro ⟨k, hk⟩; exact ⟨k, by rw [← hk]; exact Nat.le_mul_self k, hk⟩`. Then both theorems are `by decide`.
-/
