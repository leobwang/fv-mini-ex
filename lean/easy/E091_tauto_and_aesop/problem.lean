/- E091 | tauto and aesop | 2 min | tauto, aesop, automation, Set.subset_def, mathlib
GOAL
  Close propositional tautologies with `tauto`, and goals that also need ∀ / membership reasoning
  with `aesop`, giving `aesop` an extra rewrite rule where it gets stuck.

BANNED: grind, simp, simp_all, gcongr, inter_subset_inter, inter_subset_inter_left, exact?, try?

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E091

/- SKELETON · taut_trans
  1. Only `→` between the opaque propositions `P Q R`: a propositional tautology.   R1
-/
-- BEGIN SPEC
theorem taut_trans (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) :=
-- END SPEC
  sorry

/- SKELETON · taut_demorgan
  1. Only `¬`, `∨`, `∧`, `↔` between opaque propositions: a tautology.               R2
-/
-- BEGIN SPEC
theorem taut_demorgan (P Q : Prop) : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
-- END SPEC
  sorry

/- SKELETON · taut_contra
  1. Only `→`, `¬`, `↔`; the direction `(¬Q → ¬P) → (P → Q)` is classical.         R2
-/
-- BEGIN SPEC
theorem taut_contra (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) :=
-- END SPEC
  sorry

/- SKELETON · aesop_forall
  1. A `∀` appears, so `tauto` is out (Traps).
  2. Search: introduce `n`, split `h n`, split the `∧` goal into its two `∀` halves.   R3
-/
-- BEGIN SPEC
theorem aesop_forall (p q : ℕ → Prop) (h : ∀ n, p n ∧ q n) : (∀ n, q n) ∧ ∀ n, p n :=
-- END SPEC
  sorry

/- SKELETON · aesop_list
  1. Search as in R3; the membership in `xs ++ ys` inside `h` is rewritten into an
     `∨` by the @[simp] lemma, which the search applies by itself:                  R4, R5
-/
-- BEGIN SPEC
theorem aesop_list (xs ys : List ℕ) (h : ∀ x ∈ xs ++ ys, x > 0) : ∀ x ∈ ys, x > 0 :=
-- END SPEC
  sorry

/- SKELETON · aesop_subset
  1. Plain search gets stuck: `⊆` stays folded (Traps).
  2. Give the search the equation that unfolds `⊆`:                                 R6 → R8
  3. It then turns `x ∈ A ∩ C` into `x ∈ A ∧ x ∈ C` by itself and uses `h`:          R7, R3
-/
-- BEGIN SPEC
theorem aesop_subset {α : Type} (A B C : Set α) (h : A ⊆ B) : A ∩ C ⊆ B ∩ C :=
-- END SPEC
  sorry

end E091

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first three only use connectives on opaque propositions `P Q R`; the last three quantify
    (`∀`, `∈`, `⊆`), and that decides which tactic applies.
H2. `tauto` (R1, R2) for the first three, `aesop` (R3, R5) for the next two. On `aesop_subset` plain
    `aesop` is stuck because `⊆` is not unfolded: let it rewrite with `Set.subset_def` (R6, R8).
H3. `aesop (add norm Set.subset_def)`.
-/
