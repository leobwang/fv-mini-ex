/- E058 | Classical logic | 2-3 min | Classical.em, Classical.byContradiction, by_cases, absurd
GOAL
  Prove four tautologies that need the excluded middle (`P ∨ ¬P` for every `P`): double negation,
  Peirce's law, contraposition, and De Morgan for `∧`. Do the case splits yourself.

REFERENCE
  #check Classical.em                -- (p : Prop) : p ∨ ¬p
  #check @Classical.byContradiction  -- (¬p → False) → p
  #check @absurd                     -- a → ¬a → b     (from a contradiction, anything)
  example (P : Prop) : P ∨ ¬P := by
    rcases Classical.em P with hp | hnp   -- split on the excluded middle
    · exact Or.inl hp
    · exact Or.inr hnp
  example (P Q : Prop) (hq : Q) : Q := by by_cases hp : P <;> exact hq  -- `by_cases` works on any Prop
BANNED: Classical.not_not, Decidable.of_not_not, Decidable.peirce, peirce', Decidable.not_imp_not, Decidable.not_imp_symm, Decidable.not_imp_comm, Classical.not_and_iff_not_or_not, Decidable.not_and_iff_not_or_not', Decidable.not_and_iff_or_not, simp, simp_all, simpa, grind, exact?, try?
NOTE: `by_contra` (no `!`) is Mathlib only; in core use `Classical.byContradiction fun h => …`.
-/

namespace E058

-- BEGIN SPEC
theorem dne (P : Prop) (h : ¬¬P) : P :=
-- END SPEC
  Classical.byContradiction h

-- BEGIN SPEC
theorem peirce (P Q : Prop) : ((P → Q) → P) → P :=
-- END SPEC
  by
    intro h
    by_cases hp : P
    · exact hp
    · exact h (fun hp' => absurd hp' hp)

-- BEGIN SPEC
theorem contrapos (P Q : Prop) (h : ¬Q → ¬P) : P → Q :=
-- END SPEC
  by
    intro hp
    rcases Classical.em Q with hq | hnq
    · exact hq
    · exact absurd hp (h hnq)

-- BEGIN SPEC
theorem not_and_split (P Q : Prop) (h : ¬(P ∧ Q)) : ¬P ∨ ¬Q :=
-- END SPEC
  by
    by_cases hp : P
    · right
      intro hq
      exact h ⟨hp, hq⟩
    · left
      exact hp

end E058

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `¬P` is `P → False`, so `h : ¬¬P` is a function that turns a proof of `¬P` into `False`.
H2. `dne` is one `Classical.byContradiction`. For the other three, split on `P` (or `Q`) with `Classical.em`
    or `by_cases`; in the "wrong" branch derive a contradiction with `absurd`.
H3. `peirce`: `intro h; by_cases hp : P`, then `exact hp` / `exact h (fun hp' => absurd hp' hp)`.
    `not_and_split`: `by_cases hp : P`, then `right; intro hq; exact h ⟨hp, hq⟩` / `left; exact hp`.
-/
