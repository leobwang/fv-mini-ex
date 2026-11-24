/- H054 | Fixed points of a random permutation | 1-1.5 h | uniform PMF, linearity, double counting, Finset.card_bij, Equiv.swap, mathlib
GOAL
  Draw `σ` uniformly from all `n!` permutations of `Fin n = {0, …, n-1}` (`n ≥ 1`). Prove the
  expected number of fixed points (`i` with `σ i = i`) is exactly `1`. The law is
  `PMF.uniformOfFintype` turned into a measure by `.toMeasure`; the expectation is `∫ … ∂…`.

REFERENCE
  #check PMF.integral_eq_sum  -- ∫ a, f a ∂p.toMeasure = ∑ a, (p a).toReal • f a   (finite type)
  #check PMF.uniformOfFintype_apply  -- PMF.uniformOfFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹
  #check Fintype.card_perm  -- Fintype.card (Equiv.Perm α) = (Fintype.card α).factorial
  #check ENNReal.toReal_inv  -- (a⁻¹).toReal = (a.toReal)⁻¹
  #check ENNReal.toReal_natCast  -- (n : ℝ≥0∞).toReal = (n : ℝ)
  #check Finset.card_filter  -- #{i ∈ s | P i} = ∑ i ∈ s, if P i then 1 else 0
  #check Finset.sum_comm  -- ∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y
  #check Finset.card_eq_sum_card_fiberwise  -- MapsTo f s t → #s = ∑ b ∈ t, #{a ∈ s | f a = b}
  #check Finset.card_bij  -- i : (a ∈ s) → β, maps into t, injective, surjective ⟹ #s = #t
  example (j k : Fin 3) : Equiv.swap j k j = k := Equiv.swap_apply_left j k  -- swap j k exchanges j, k
  example (σ τ : Equiv.Perm (Fin 3)) (i : Fin 3) : (σ * τ) i = σ (τ i) := rfl  -- `*` is composition
NOTE: The two `instance`s only give the finite type `Equiv.Perm (Fin n)` the discrete σ-algebra.
  `ℝ≥0∞` = `ENNReal` = [0, ∞], where PMF values live; `.toReal : ℝ≥0∞ → ℝ` casts (∞ ↦ 0).
  `#s` = `s.card`; `#{i ∈ s | P i}` = `(s.filter P).card`; `MapsTo f s t` = `∀ a ∈ s, f a ∈ t`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace H054

-- BEGIN SPEC
instance permMeasurableSpace (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

instance permMeasurableSingleton (n : ℕ) : MeasurableSingletonClass (Equiv.Perm (Fin n)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The number of fixed points of a permutation. -/
def numFixed {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := (Finset.univ.filter fun i => σ i = i).card
-- END SPEC

-- MILESTONE (optional: change or delete)
/-- For fixed `i`, every value `j` of `σ i` is hit by equally many permutations. -/
theorem card_apply_eq (n : ℕ) (i j k : Fin n) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ i = j).card =
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ i = k).card := by
  sorry

-- MILESTONE (optional: change or delete)
/-- Hence exactly `n! / n` permutations fix `i`. -/
theorem card_fix_mul (n : ℕ) (i : Fin n) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card * n = n.factorial := by
  sorry

-- MILESTONE (optional: change or delete)
/-- Double counting the pairs `(σ, i)` with `σ i = i`. -/
theorem sum_numFixed (n : ℕ) :
    ∑ σ : Equiv.Perm (Fin n), (numFixed σ : ℝ) =
      ∑ i : Fin n, ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card : ℝ) := by
  sorry

-- BEGIN SPEC
theorem expected_fixed_points (n : ℕ) (hn : 1 ≤ n) :
    ∫ σ, (numFixed σ : ℝ) ∂(PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure = 1 :=
-- END SPEC
  sorry

end H054

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. On a uniform finite space the expectation is `(1 / n!) · ∑_σ numFixed σ`. Count the pairs `(σ, i)`
    with `σ i = i` the other way round: `∑_σ numFixed σ = ∑_i #{σ | σ i = i}` (linearity of expectation).
H2. For a fixed `i`, the `n` sets `{σ | σ i = j}` (`j : Fin n`) split all `n!` permutations and all have
    the same size, so each has `n! / n` elements. (Burnside's lemma
    `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` is a valid but longer alternative.)
H3. `card_apply_eq`: `apply Finset.card_bij (fun σ _ => Equiv.swap j k * σ)`, then `simp` each goal
    (the preimage of `τ` is `Equiv.swap j k * τ`). `card_fix_mul`: `Finset.card_eq_sum_card_fiberwise
    (f := fun σ => σ i)` and `Finset.sum_const`. `sum_numFixed`: `simp only [numFixed, Finset.card_filter,
    Nat.cast_sum, ...]; exact Finset.sum_comm`. Main: `rw [PMF.integral_eq_sum]; simp only
    [PMF.uniformOfFintype_apply, Fintype.card_perm, Fintype.card_fin, smul_eq_mul]`, then
    `rw [← Finset.mul_sum, sum_numFixed]`; replace each term by `n! / n` (from `card_fix_mul`,
    `eq_div_iff`), `rw [Finset.sum_const, …, nsmul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]`,
    and `field_simp` (with `(n! : ℝ) ≠ 0`, `(n : ℝ) ≠ 0` from `positivity` in context).
-/
