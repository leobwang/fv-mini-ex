/- E091 | tauto and aesop | 2 min | tauto, aesop, automation, Set.subset_def, mathlib
GOAL
  Close propositional tautologies with `tauto`, and goals that also need ∀ / membership reasoning
  with `aesop`, giving `aesop` an extra rewrite rule where it gets stuck.

REFERENCE
  example (P Q : Prop) (hp : P) (hq : Q) : Q ∧ P := by tauto     -- ∧ ∨ → ¬ ↔ structure only
  example (p : ℕ → Prop) (h : ∀ n, p n) : p 3 ∧ p 4 := by aesop  -- searches: intro, simp, split, apply
  -- `aesop (add norm foo)`: aesop may also rewrite with the equation `foo` as it searches
  #check Set.subset_def   -- (s ⊆ t) = ∀ x ∈ s, x ∈ t
BANNED: grind, simp, simp_all, gcongr, inter_subset_inter, inter_subset_inter_left, exact?, try?
NOTE: `tauto` does not look inside `∀` or `∩`; plain `aesop` makes no progress on `⊆` for sets.
-/
import Mathlib

namespace E091

-- BEGIN SPEC
theorem taut_trans (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) :=
-- END SPEC
  by tauto

-- BEGIN SPEC
theorem taut_demorgan (P Q : Prop) : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
-- END SPEC
  by tauto

-- BEGIN SPEC
theorem taut_contra (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) :=
-- END SPEC
  by tauto

-- BEGIN SPEC
theorem aesop_forall (p q : ℕ → Prop) (h : ∀ n, p n ∧ q n) : (∀ n, q n) ∧ ∀ n, p n :=
-- END SPEC
  by aesop

-- BEGIN SPEC
theorem aesop_list (xs ys : List ℕ) (h : ∀ x ∈ xs ++ ys, x > 0) : ∀ x ∈ ys, x > 0 :=
-- END SPEC
  by aesop

-- BEGIN SPEC
theorem aesop_subset {α : Type} (A B C : Set α) (h : A ⊆ B) : A ∩ C ⊆ B ∩ C :=
-- END SPEC
  by aesop (add norm Set.subset_def)

end E091

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first three only use connectives on opaque propositions `P Q R`; the last three quantify.
H2. `tauto` for the first three, `aesop` for the next two. On `aesop_subset` plain `aesop`
    is stuck because `⊆` is not unfolded: hand it `Set.subset_def`.
H3. `aesop (add norm Set.subset_def)`.
-/
