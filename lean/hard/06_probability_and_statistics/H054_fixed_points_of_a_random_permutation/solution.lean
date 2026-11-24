/- H054 | Fixed points of a random permutation | 1-1.5 h | uniform PMF, linearity, double counting, Finset.card_bij, Equiv.swap, mathlib
GOAL
  Draw `σ` uniformly from all `n!` permutations of `Fin n = {0, …, n-1}` (`n ≥ 1`). Prove the
  expected number of fixed points (`i` with `σ i = i`) is exactly `1`. The law is
  `PMF.uniformOfFintype` turned into a measure by `.toMeasure`; the expectation is `∫ … ∂…`.

GUIDE
  Entries R1–R33: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · card_apply_eq   (MILESTONE: prove it first; used by card_fix_mul)
  1. Bijection `σ ↦ Equiv.swap j k * σ` from `{σ | σ i = j}` onto `{σ | σ i = k}`:  R1
  2. Maps into: `intro σ hσ`; both memberships → equations `σ i = j`, `… = k`:     R2
       `(swap j k * σ) i` → `swap j k (σ i)` → `swap j k j` → `k`:                  R3, rw [hσ], R4
  3. Injective: `intro a _ b _ h`; cancel the left factor `swap j k` in `h`:       R6 (or R7)
  4. Surjective: `intro τ hτ`; witness `swap j k * τ` (a swap is its own inverse): R8
       membership goal:                                                            R2, R3, rw [hτ], R5
       `swap j k * (swap j k * τ) = τ`:                                             R9 → R10 → R11
  (`simp [hσ]`, `simpa using h` and `simp [← mul_assoc]` run these rewrite chains.)
-/
-- MILESTONE (optional: change or delete)
/-- For fixed `i`, every value `j` of `σ i` is hit by equally many permutations. -/
theorem card_apply_eq (n : ℕ) (i j k : Fin n) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ i = j).card =
      (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ i = k).card := by
  apply Finset.card_bij (fun σ _ => Equiv.swap j k * σ)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    simp [hσ]
  · intro a _ b _ h
    simpa using h
  · intro τ hτ
    -- WHY: `swap j k` is its own inverse, so the preimage of `τ` is `swap j k * τ`.
    refine ⟨Equiv.swap j k * τ, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      simp [hτ]
    · simp [← mul_assoc]

/- SKELETON · card_fix_mul   (MILESTONE: uses card_apply_eq; used by expected_fixed_points)
  1. Split all permutations by the value `σ i`, with `s = t = Finset.univ`:        R12
       h : Finset.univ.card = ∑ b, {a | a i = b}.card        (`a` a permutation, `b : Fin n`)
  2. In `h`, the left side → `n.factorial`:                                        R13 → R14 → R15 (at h)
  3. Goal: rw [h]; every summand → the `j = i` one, by `card_apply_eq n i j i`:     R16
  4. A sum of `n` equal terms → `n * term`; then commute, `rw` closes by rfl:      R17, R13, R15, R18, R19
-/
-- MILESTONE (optional: change or delete)
/-- Hence exactly `n! / n` permutations fix `i`. -/
theorem card_fix_mul (n : ℕ) (i : Fin n) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card * n = n.factorial := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (t := Finset.univ) (f := fun σ => σ i) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h
  rw [h, Finset.sum_congr rfl (fun j _ => card_apply_eq n i j i), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

/- SKELETON · sum_numFixed   (MILESTONE: used by expected_fixed_points)
  1. Unfold `numFixed`, cards → sums of indicators, casts inside the sums and ifs:
       one `simp only [numFixed, …]` with                                          R20, R21, R22
  2. The two sides are the same double sum in the other order:                     R23 (`exact`)
-/
-- MILESTONE (optional: change or delete)
/-- Double counting the pairs `(σ, i)` with `σ i = i`. -/
theorem sum_numFixed (n : ℕ) :
    ∑ σ : Equiv.Perm (Fin n), (numFixed σ : ℝ) =
      ∑ i : Fin n, ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card : ℝ) := by
  simp only [numFixed, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact Finset.sum_comm

/- SKELETON · expected_fixed_points   (prove the three MILESTONES first)
  1. Integral → finite sum:                                                        R24
  2. Each probability → `(↑n.factorial)⁻¹`, `•` → `*`: one `simp only` with         R25, R14, R15, R18
  3. Pull the constant out of the sum, then double counting:                       R26, rw [sum_numFixed]
  4. Fact first (the infoview prints it as `↑{σ | σ i = i}.card = ↑n.factorial / ↑n`, but
     `{σ | …}` typed by hand is a `Set`, so state the `Finset` as in the theorems above):
       hc : ∀ i : Fin n,
         ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card : ℝ) = n.factorial / n
       proof: intro i; R27 with its side goal by R28; then `card_fix_mul n i` by    R29
  5. Every summand → `n!/n`; sum of a constant; `ENNReal` → `ℝ`:
       R16 (with hc), R17, R13, R15, R30, R31, R32
  6. `have` the facts `(↑n.factorial : ℝ) ≠ 0`, `(↑n : ℝ) ≠ 0` (each by R28), then:   R33
-/
-- BEGIN SPEC
theorem expected_fixed_points (n : ℕ) (hn : 1 ≤ n) :
    ∫ σ, (numFixed σ : ℝ) ∂(PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure = 1 :=
-- END SPEC
  by
    rw [PMF.integral_eq_sum]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
    rw [← Finset.mul_sum, sum_numFixed]
    have hc : ∀ i : Fin n,
        ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card : ℝ) = n.factorial / n := by
      intro i
      rw [eq_div_iff (by positivity)]
      exact_mod_cast card_fix_mul n i
    rw [Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp

end H054

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. On a uniform finite space the expectation is `(1 / n!) · ∑_σ numFixed σ`. Count the pairs `(σ, i)`
    with `σ i = i` the other way round: `∑_σ numFixed σ = ∑_i #{σ | σ i = i}` (`sum_numFixed`). What is
    left is `#{σ | σ i = i} = n! / n` for each `i`.
H2. For a fixed `i`, split all `n!` permutations by the value `j = σ i` (R12): the `n` classes
    `{σ | σ i = j}` all have the same size (`card_apply_eq`, via the bijection `σ ↦ swap j k * σ`, R1), so
    `#{σ | σ i = i} * n = n!` (`card_fix_mul`). Main theorem: R24, R25 turn the integral into
    `(↑n!)⁻¹.toReal * ∑_σ …`; after R26 and `sum_numFixed` it is arithmetic in `ℝ`. (Burnside's lemma
    `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` is a valid but longer alternative.)
H3. `card_apply_eq`: `apply Finset.card_bij (fun σ _ => Equiv.swap j k * σ)`, then `simp` each goal
    (the preimage of `τ` is `Equiv.swap j k * τ`). `card_fix_mul`: `Finset.card_eq_sum_card_fiberwise
    (f := fun σ => σ i) (fun _ _ => Finset.mem_univ _)` and `Finset.sum_const`. `sum_numFixed`:
    `simp only [numFixed, Finset.card_filter, Nat.cast_sum, ...]; exact Finset.sum_comm`. Main:
    `rw [PMF.integral_eq_sum]; simp only [PMF.uniformOfFintype_apply, Fintype.card_perm, Fintype.card_fin,
    smul_eq_mul]`, then `rw [← Finset.mul_sum, sum_numFixed]`; `hc` by `rw [eq_div_iff (by positivity)]`
    and `exact_mod_cast card_fix_mul n i`; `rw [Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_const,
    …, nsmul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]`, and `field_simp` with the two `≠ 0` facts.
-/
