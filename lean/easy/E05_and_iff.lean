/- E05 | And and Iff | 2-3 min | constructor, obtain, rintro, Iff
GOAL
  Prove that `∧` is commutative and associative (as `↔`), and use an `↔` in both directions.

REFERENCE
  example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by constructor; exact hp; exact hq
  example (P Q : Prop) (h : P ∧ Q) : Q := by obtain ⟨hp, hq⟩ := h; exact hq  -- destructure
  example (P Q : Prop) : P ∧ Q → Q := by rintro ⟨hp, hq⟩; exact hq   -- intro + destructure
  example (P : Prop) : P ↔ P := by constructor <;> intro h <;> exact h  -- ↔ splits into → and ←
  example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := h.mpr hq          -- `.mp` : P → Q, `.mpr` : Q → P
  Focus a goal with `·` (type \.) after `constructor`.
BANNED: simp, simp_all, grind, and_comm, and_assoc
-/

-- BEGIN SPEC
theorem and_comm_iff (P Q : Prop) : P ∧ Q ↔ Q ∧ P :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem and_assoc_iff (P Q R : Prop) : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem iff_both_ways (P Q : Prop) (h : P ↔ Q) (hp : P) (hq' : Q → False) : False :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. An `↔` goal needs two proofs; `constructor` produces both goals.
H2. In each direction, `rintro ⟨...⟩` takes the conjunction apart, then `exact ⟨...⟩` rebuilds it.
H3. `and_assoc_iff`: `rintro ⟨⟨hp, hq⟩, hr⟩` then `exact ⟨hp, hq, hr⟩` (⟨a, b, c⟩ nests to the right).
-/
