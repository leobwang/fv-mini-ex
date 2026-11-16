/- M159 | Density of states of N two-level systems | 15-20 min | Finset.card, bijections, powersetCard, sum_fiberwise, mathlib
GOAL
  `N` two-level systems with level spacing `ε`: a configuration is `σ : Fin N → Bool` (`true` = excited),
  with energy `ε * nUp σ`. (a) Exactly `C(N, m)` configurations have `m` excitations (the degeneracy
  `g(m)`). (b) So `Z = ∑_σ exp (-b E(σ))` (`b` = inverse temperature β, units kB = 1) can be summed over levels: `Z = ∑_{m=0}^{N} g(m) exp (-b ε m)`.

REFERENCE
  #check Finset.card_powersetCard  -- (powersetCard n s).card = s.card.choose n
  #check Finset.mem_powersetCard   -- s ∈ powersetCard n t ↔ s ⊆ t ∧ s.card = n
  #check Finset.card_nbij'         -- maps i : α → β, j : β → α, both maps-to, j ∘ i = id, i ∘ j = id ⊢ s.card = t.card
  #check Finset.sum_fiberwise_of_maps_to  -- (∀ x ∈ s, g x ∈ t) → ∑ y ∈ t, ∑ x ∈ s with g x = y, f x = ∑ x ∈ s, f x
  #check Finset.sum_const          -- ∑ _x ∈ s, c = s.card • c
  #check nsmul_eq_mul              -- n • a = ↑n * a
  #check Finset.card_le_univ       -- s.card ≤ Fintype.card α
  example (s : Finset (Fin 3)) (i : Fin 3) : (decide (i ∈ s) = true) ↔ i ∈ s := decide_eq_true_iff
  `univ.filter p` (printed `{x | p x}`) is the finset of `x` with `p x`; `decide p : Bool` turns a Prop into a Bool.
  `Finset.card_nbij'` with `refine … ?_ ?_ ?_ ?_` leaves the four obligations as goals.
NOTE: don't rewrite `N` to `Fintype.card (Fin N)` everywhere: `rw` also rewrites the `N` inside `Fin N`.
-/
import Mathlib

open Real

namespace M159

-- BEGIN SPEC
/-- Number of excited two-level systems (`true` = excited, energy `ε`) in a configuration. -/
def nUp {N : ℕ} (σ : Fin N → Bool) : ℕ := (Finset.univ.filter fun i => σ i = true).card
-- END SPEC

-- BEGIN SPEC
theorem degeneracy (N m : ℕ) :
    (Finset.univ.filter fun σ : Fin N → Bool => nUp σ = m).card = N.choose m :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem Z_from_dos (N : ℕ) (b ε : ℝ) :
    ∑ σ : Fin N → Bool, Real.exp (-b * (ε * nUp σ)) =
      ∑ m ∈ Finset.range (N + 1), (N.choose m : ℝ) * Real.exp (-b * (ε * m)) :=
-- END SPEC
  sorry

end M159

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (a) A configuration with `m` excitations is the same thing as an `m`-element subset of the sites
    (the excited ones). (b) Group the configurations by their number of excitations.
H2. (a) Turn `N.choose m` into `(Finset.powersetCard m (Finset.univ : Finset (Fin N))).card` and use
    `Finset.card_nbij'` with `σ ↦ univ.filter (σ · = true)` and `s ↦ fun i => decide (i ∈ s)`.
    (b) `rw [← Finset.sum_fiberwise_of_maps_to (g := nUp) (t := Finset.range (N + 1))]`; on the fiber
    `nUp σ = m` the summand is the constant `exp (-b * (ε * m))`, so `sum_const` and (a) finish.
H3. The inverse laws are `funext i; simp` and `ext i; simp`. The maps-to goal of (b) is `nUp σ ≤ N`:
    `(Finset.card_le_univ _).trans (by simp)`. On a fiber, `Finset.sum_congr rfl` with the constant
    function `g := fun _ => Real.exp (-b * (ε * m))`.
-/
