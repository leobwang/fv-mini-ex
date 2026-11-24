/- M078 | ε-δ continuity ⇔ sequential continuity | 15-20 min | epsilon-delta, sequences, push Not, choose, mathlib
GOAL
  `f` is ε-δ continuous at `x` iff for every sequence `a n → x` we have `f (a n) → f x`
  (both notions are the explicit definitions below, not Mathlib's).

BANNED: Continuous, ContinuousOn, ContinuousAt, ContinuousWithinAt, continuous, continuousOn, continuousAt, Tendsto, tendsto, nhds, 𝓝, Filter, atTop, Eventually, eventually, ∀ᶠ, Metric, CauchySeq, tendsto_nhds_nhds, tendsto_nhds, tendsto_atTop, tendsto_order, eventually_atTop, mem_atTop_sets, ball_mem_nhds, continuous_iff_continuousAt, continuous_def, cauchySeq_iff, cauchySeq_iff', cauchy_iff_exists_le_nhds, fun_prop, continuity, tendsto_nhds_iff_seq_tendsto, SeqContinuous, continuous_iff_seqContinuous

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M078

-- BEGIN SPEC
def ContAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε
-- END SPEC

-- BEGIN SPEC
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- END SPEC

/- SKELETON · contAt_iff_seq
  1. Split the `↔`:                                                         R1
  (→) 2. Introduce hf, a, ha, then the ε, hε of the goal `ConvergesTo …`:   R3, R2
      3. δ from continuity at ε, then N from convergence of `a` at δ:      R4, R4
      4. Give N; for n ≥ N chain `hN n hn` into the δ-statement:            R5
  (←) 5. Introduce h; assume ¬ContAt, unfold it, push the ¬ inward:         R6, R7, R8
      6. Take apart the bad ε:  obtain ⟨ε, hε, hbad⟩                        R4
      7. Build the bad sequence with δ = 1 / (↑n + 1):                      R9 with R10
           a : ℕ → ℝ,  ha1 : ∀ n, |a n - x| < 1 / (↑n + 1),  ha2 : ∀ n, ε ≤ |f (a n) - f x|
      8. MILESTONE  hconv : ConvergesTo a x   (have … := by)
           intro η hη; Archimedes N > 1 / η:                                R3, R2, R11 (via R4)
           give N, reduce |a n - x| < η to 1 / (↑n + 1) ≤ η:                R5 + R12
           cast n ≥ N to ℝ, clear both divisions, finish:                   R13, R14 with R10, R15, R16
      9. Feed hconv to h at ε, get N; contradict at n = N:                  R4, R17, R18, R19
-/
-- BEGIN SPEC
theorem contAt_iff_seq (f : ℝ → ℝ) (x : ℝ) :
    ContAt f x ↔ ∀ a : ℕ → ℝ, ConvergesTo a x → ConvergesTo (fun n => f (a n)) (f x) :=
-- END SPEC
  sorry

end M078

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (→) is a chase: ε gives δ (continuity, R4), δ gives N (convergence of `a`, R4), and the same N
    works for `fun n => f (a n)` (R5). (←) goes by contradiction (R6): if `f` is not continuous at `x`, pick for
    each n a bad point within 1 / (n + 1) of `x`; that sequence converges to `x` but its image does not.
H2. (←): `by_contra hf; unfold ContAt at hf; push Not at hf` and `obtain ⟨ε, hε, hbad⟩ := hf` give
    `hbad : ∀ δ > 0, ∃ y, |y - x| < δ ∧ ε ≤ |f y - f x|` (R6–R8). Build the sequence with `choose` (R9),
    prove `ConvergesTo a x` as a separate `have` (Archimedes, R11–R16), then apply `h` to it at `ε` and
    compare the two facts at index N (R17–R19).
H3. `choose a ha1 ha2 using fun n : ℕ => hbad (1 / ((n : ℝ) + 1)) (by positivity)`. Inside `hconv`:
    `obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)`, `refine ⟨N, fun n hn => lt_of_lt_of_le (ha1 n) ?_⟩`,
    `rw [div_le_iff₀ (by positivity)]`, `rw [div_lt_iff₀ hη] at hN`, then `nlinarith` with
    `(N : ℝ) ≤ n`. Finish with `absurd (hN N le_rfl) (not_lt.mpr (ha2 N))`.
-/
