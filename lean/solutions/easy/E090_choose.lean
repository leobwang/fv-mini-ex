/- E090 | choose | 2-3 min | choose, Exists.choose, Skolem functions, noncomputable, mathlib
GOAL
  Turn a hypothesis `∀ x, ∃ y, P x y` into a function `g` with `∀ x, P x (g x)` (a "Skolem
  function"), and use the term-level `h.choose` / `h.choose_spec` of a single `∃`.

REFERENCE
  example (h : ∀ n : ℕ, ∃ m, m > n) : ∃ g : ℕ → ℕ, ∀ n, g n > n := by
    choose g hg using h; exact ⟨g, hg⟩     -- g : ℕ → ℕ, hg : ∀ n, g n > n
  -- `choose g h1 h2 using h` also splits `∃ y, A y ∧ B y` into two facts h1, h2
  example (h : ∃ n : ℕ, n > 3) : h.choose > 3 := h.choose_spec   -- the witness, and its proof
  #check Function.Surjective   -- `Surjective f` unfolds to `∀ b, ∃ a, f a = b`
  -- a `def` that uses `h.choose` must be `noncomputable` (it relies on the axiom of choice)
BANNED: Function.surjective_iff_hasRightInverse, Function.Surjective.hasRightInverse, Function.surjInv, Function.surjInv_eq, Function.rightInverse_surjInv, Function.invFun, Function.invFun_eq, Function.rightInverse_invFun, Classical.skolem, Classical.axiomOfChoice, exact?, try?
-/
import Mathlib

namespace E090

-- BEGIN SPEC
theorem choose_fun (f : ℕ → ℕ) (h : ∀ n, ∃ m, f m > n) : ∃ g : ℕ → ℕ, ∀ n, f (g n) > n :=
-- END SPEC
  by
    choose g hg using h
    exact ⟨g, hg⟩

-- BEGIN SPEC
theorem choose_two (p : ℕ → ℕ → Prop) (h : ∀ x, ∃ y, y > x ∧ p x y) :
    ∃ g : ℕ → ℕ, ∀ x, g x > x ∧ p x (g x) :=
-- END SPEC
  by
    choose g hg1 hg2 using h
    exact ⟨g, fun x => ⟨hg1 x, hg2 x⟩⟩

-- BEGIN SPEC
theorem right_inverse (f : ℕ → ℕ) (hf : Function.Surjective f) : ∃ g : ℕ → ℕ, ∀ y, f (g y) = y :=
-- END SPEC
  by
    choose g hg using hf
    exact ⟨g, hg⟩

-- BEGIN SPEC
noncomputable def root (h : ∃ n : ℕ, n * n = 49) : ℕ := h.choose
-- END SPEC

-- BEGIN SPEC
theorem root_spec (h : ∃ n : ℕ, n * n = 49) : root h * root h = 49 :=
-- END SPEC
  h.choose_spec

end E090

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each of the first three has a hypothesis of shape `∀ x, ∃ y, ...`: that is exactly what
    `choose` eats. `root` is defined as `h.choose`, so its property is `h.choose_spec`.
H2. `choose` the function, then return it with `⟨g, _⟩`. In `choose_two` give `choose` two names
    for the two halves of the `∧`. `hf : Surjective f` already has the `∀ y, ∃ a, f a = y` shape.
H3. `choose g hg1 hg2 using h; exact ⟨g, fun x => ⟨hg1 x, hg2 x⟩⟩`; `root_spec`: `h.choose_spec`.
-/
