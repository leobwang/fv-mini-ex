/- E090 | choose | 2-3 min | choose, Exists.choose, Skolem functions, noncomputable, mathlib
GOAL
  Turn a hypothesis `∀ x, ∃ y, P x y` into a function `g` with `∀ x, P x (g x)` (a "Skolem
  function"), and use the term-level `h.choose` / `h.choose_spec` of a single `∃`.

BANNED: Function.surjective_iff_hasRightInverse, Function.Surjective.hasRightInverse, Function.surjInv, Function.surjInv_eq, Function.rightInverse_surjInv, Function.invFun, Function.invFun_eq, Function.rightInverse_invFun, Classical.skolem, Classical.axiomOfChoice, exact?, try?

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace E090

/- SKELETON · choose_fun
  1. Turn `h` into a function `g : ℕ → ℕ` and its property `hg : ∀ n, f (g n) > n`:   R1
  2. Give `g` as the witness of the `∃`; what is left is literally `hg`:              R2
-/
-- BEGIN SPEC
theorem choose_fun (f : ℕ → ℕ) (h : ∀ n, ∃ m, f m > n) : ∃ g : ℕ → ℕ, ∀ n, f (g n) > n :=
-- END SPEC
  sorry

/- SKELETON · choose_two
  1. Turn `h` into `g` and, with two fact names, split the `∧` into two facts:        R3
  2. Give `g` as the witness of the `∃`:                                              R2
  3. Prove `∀ x, g x > x ∧ p x (g x)` by pairing the two facts at each `x`:           R4
     (steps 2 and 3 fit in one `exact ⟨g, …⟩`)
-/
-- BEGIN SPEC
theorem choose_two (p : ℕ → ℕ → Prop) (h : ∀ x, ∃ y, y > x ∧ p x y) :
    ∃ g : ℕ → ℕ, ∀ x, g x > x ∧ p x (g x) :=
-- END SPEC
  sorry

/- SKELETON · right_inverse
  1. `hf : Function.Surjective f` already means `∀ y, ∃ a, f a = y` (unfold optional): R5
  2. Then exactly as in `choose_fun`:                                                 R1, R2
-/
-- BEGIN SPEC
theorem right_inverse (f : ℕ → ℕ) (hf : Function.Surjective f) : ∃ g : ℕ → ℕ, ∀ y, f (g y) = y :=
-- END SPEC
  sorry

-- BEGIN SPEC
noncomputable def root (h : ∃ n : ℕ, n * n = 49) : ℕ := h.choose
-- END SPEC

/- SKELETON · root_spec
  1. `root h` is by definition `h.choose` (optional: `unfold root` to see it):        R6, R7
  2. Close with the property of the witness (one term, no tactic needed):             R8
-/
-- BEGIN SPEC
theorem root_spec (h : ∃ n : ℕ, n * n = 49) : root h * root h = 49 :=
-- END SPEC
  sorry

end E090

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first three hypotheses have the shape `∀ x, ∃ y, …` (for `hf`, after unfolding
    `Function.Surjective`): that is exactly what `choose` eats (R1, R5). `root h` is by definition
    `h.choose` (R6), so its property is the witness's own property (R8).
H2. `choose` the function, then return it as the witness: `⟨g, _⟩` (R2). In `choose_two` give `choose`
    two fact names so it splits the `∧` (R3), then pair the facts with `fun x => ⟨_, _⟩` (R4).
H3. `choose_two`: `choose g hg1 hg2 using h; exact ⟨g, fun x => ⟨hg1 x, hg2 x⟩⟩`.
    `right_inverse`: `choose g hg using hf; exact ⟨g, hg⟩`. `root_spec`: `h.choose_spec`.
-/
