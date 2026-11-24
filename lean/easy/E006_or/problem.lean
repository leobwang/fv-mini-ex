/- E006 | Or | 2-3 min | cases, rcases, left, right, Or
GOAL
  Prove that `∨` is commutative and that `∧` distributes over `∨`.

REFERENCE
  example (P Q : Prop) (hp : P) : P ∨ Q := by left; exact hp      -- `right` picks the other side
  example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
    cases h with | inl hp => exact Or.inr hp | inr hq => exact Or.inl hq   -- one goal per case
  example (P Q R : Prop) (h : P ∨ Q ∨ R) : True := by rcases h with hp | hq | hr <;> trivial
  example (P Q R : Prop) (h : P ∧ (Q ∨ R)) : True := by obtain ⟨hp, hq | hr⟩ := h <;> trivial
    -- patterns nest: ⟨_, _⟩ for ∧, `a | b` for ∨
BANNED: simp, simp_all, grind, or_comm, and_or_left
-/

-- BEGIN SPEC
theorem or_swap (P Q : Prop) : P ∨ Q → Q ∨ P :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem and_or_distrib (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. To use `h : A ∨ B`, split into the two cases; to prove `A ∨ B`, choose a side.
H2. For the `↔`, use `constructor`, then destructure with nested patterns in `rintro`.
H3. `rintro ⟨hp, hq | hr⟩` for →, and `rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)` for ← (parentheses needed).
-/
