/- E08 | Not and False | 2-3 min | Not, False, absurd, contradiction, exfalso
GOAL
  Prove facts about negation. Remember `¬P` is defined as `P → False`.

REFERENCE
  example (P : Prop) (hp : P) (hn : ¬P) : False := hn hp     -- apply a negation to get False
  example (P : Prop) : P → ¬¬P := by intro hp hn; exact hn hp  -- `intro` on a `¬` goal
  example (P Q : Prop) (hp : P) (hn : ¬P) : Q := absurd hp hn  -- anything follows from P, ¬P
  example (P Q : Prop) (hp : P) (hn : ¬P) : Q := by contradiction   -- finds the clash itself
  example (P : Prop) (h : 1 = 2) : P := by exfalso; exact absurd h (by decide)  -- goal ↦ False
BANNED: simp, simp_all, grind, not_or
-/

-- BEGIN SPEC
theorem not_and_not (P : Prop) : ¬(P ∧ ¬P) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem contrapositive (P Q : Prop) : (P → Q) → ¬Q → ¬P :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem from_clash (P Q : Prop) (hp : P) (h : P → ¬P) : Q :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem not_or_iff (P Q : Prop) : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A goal `¬X` is a function goal: start with `intro hx` and aim for `False`.
H2. `from_clash`: `h hp : ¬P` and `hp : P`, so `h hp hp : False`.
H3. `not_or_iff` →: `exact ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩`; ←: `rintro ⟨hnp, hnq⟩ (hp | hq)`.
-/
