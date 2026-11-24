/- M158 | Maximum entropy | 15-20 min | negMulLog, concavity, Jensen, Gibbs entropy, mathlib
GOAL
  The Gibbs entropy `S(p) = ∑ i, negMulLog (p i)` (with `negMulLog x = -x log x`, units kB = 1) of any
  probability distribution `p` on `Ω = Fintype.card ι` microstates is at most `log Ω`, and the uniform
  distribution `p i = 1/Ω` attains it: Boltzmann's `S = log Ω` is the maximum entropy.
BANNED: Hₛ_le_log_d, Hₛ_uniform, Sᵥₙ_le_log_d, try?

GUIDE
  Entries R1–R25: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Real

namespace M158

/- SKELETON · max_entropy
  1. Name Ω as a real number, `n := (Fintype.card ι : ℝ)`, with its defining equation `hn`:  R1
  2. Prove `hn0 : 0 < n`: rewrite with `hn`, then the cast of a positive card:               rw [hn], R3 with R2
  3. Jensen for the concave `negMulLog` on `[0, ∞)`, with `t := Finset.univ`,
     equal weights `w := fun _ => 1 / n` and points `p := p`:                                R4, R5
     Each side goal is an argument (as a `?_` it comes after the main goal):
       side goal 1, `∀ i ∈ Finset.univ, 0 ≤ 1 / n`: take `i` and `i ∈ univ`
         (`fun _ _ => by …`), then                                                           R6
       side goal 2, `∑ i, 1 / n = 1`: `simp` with R8 and `← hn` (it applies R14, R7, R9)
       side goal 3, `∀ i ∈ Finset.univ, p i ∈ Set.Ici 0`: `fun i _ => …` with `hp i`  R10
  4. Simplify `hJ` (`simp only […] at hJ`): `•` → `*`, pull `1 / n` out of the left sum,
     replace `∑ i, p i` by 1:                                                                R11, ← R12, hs
     hJ is now  `1 / n * ∑ i, negMulLog (p i) ≤ negMulLog (1 / n * 1)`.
  5. Prove `hR : negMulLog (1 / n * 1) = log n / n` (`simp` with R13, R15; it applies R14),
     it leaves `n⁻¹ * log n = log n / n`, which R16 closes; then `rw [hR] at hJ`.
  6. Multiply `hJ` by `n ≥ 0`:                                                               R18 with R17
  7. Cancel `n * (1 / n * S)` and `n * (log n / n)` and close with the result:              R24 with R20, R21 (R19), R22, R23 (R19)
-/
-- BEGIN SPEC
theorem max_entropy {ι : Type} [Fintype ι] [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) :
    ∑ i, Real.negMulLog (p i) ≤ Real.log (Fintype.card ι) :=
-- END SPEC
  by
    set n : ℝ := (Fintype.card ι : ℝ) with hn
    have hn0 : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
    have hJ := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := fun _ => 1 / n) (p := p)
      (fun _ _ => by positivity) (by simp [Finset.card_univ, ← hn]) (fun i _ => hp i)
    simp only [smul_eq_mul, ← Finset.mul_sum, hs] at hJ
    have hR : Real.negMulLog (1 / n * 1) = Real.log n / n := by
      simp [Real.negMulLog, Real.log_inv]
      field_simp
    rw [hR] at hJ
    have := mul_le_mul_of_nonneg_left hJ hn0.le
    rwa [← mul_assoc, mul_one_div_cancel hn0.ne', one_mul, mul_div_cancel₀ _ hn0.ne'] at this

/- SKELETON · uniform_attains
  1. (Optional) `0 < (Fintype.card ι : ℝ)`, as in max_entropy step 2:                          R3 with R2
  2. One `simp`, naming R13 (unfold `negMulLog`), R15 and R8. It applies R14, R7, R9 itself and
     then R25, proving `↑(Fintype.card ι) ≠ 0` on its own (`Fintype.card_ne_zero`, `Nat.cast_eq_zero`).
-/
-- BEGIN SPEC
theorem uniform_attains {ι : Type} [Fintype ι] [Nonempty ι] :
    ∑ _i : ι, Real.negMulLog (1 / Fintype.card ι) = Real.log (Fintype.card ι) :=
-- END SPEC
  by
    have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    simp [Real.negMulLog, Real.log_inv, Finset.card_univ]

end M158

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `negMulLog` is concave on `[0, ∞)` (R4). Jensen (R5) with the equal weights `1/Ω` says: the average
    of the `negMulLog (p i)` is at most `negMulLog` of the average of the `p i`, and that average is
    `1/Ω` because `∑ i, p i = 1`. For `uniform_attains` every summand is the same constant.
H2. Set `n := (Fintype.card ι : ℝ)` (R1) and prove `0 < n` (R2, R3). Get `hJ` from
    `Real.concaveOn_negMulLog.le_map_sum` with named arguments `t`, `w`, `p`, simplify it to
    `1 / n * ∑ i, negMulLog (p i) ≤ negMulLog (1 / n * 1)` (R11, R12, `hs`), show the right side is
    `log n / n` (R13–R16), multiply by `n` (R17, R18) and cancel (R19–R24).
H3. `have hJ := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := fun _ => 1 / n) (p := p)
      (fun _ _ => by positivity) (by simp [Finset.card_univ, ← hn]) (fun i _ => hp i)`
    then `simp only [smul_eq_mul, ← Finset.mul_sum, hs] at hJ`. The last line is a
    `rwa [← mul_assoc, mul_one_div_cancel …, one_mul, mul_div_cancel₀ …] at this`.
    `uniform_attains`: `simp [Real.negMulLog, Real.log_inv, Finset.card_univ]`.
-/
