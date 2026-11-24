/- M174 | The Lorentz factor is at least 1 | 10 min | boost matrix entries, Real.sqrt, one_le_div, nlinarith, physlib
GOAL
  `boost i β hβ` is the Lorentz boost with speed `β = v / c` (speed in units of `c`, `|β| < 1`) along
  spatial axis `i`. Show its time-time entry `Λ⁰₀ = (boost i β hβ).1 (Sum.inl 0) (Sum.inl 0)` is `≥ 1`
  (that entry is the Lorentz factor `γ β = 1 / √(1 - β ^ 2)`: moving clocks never run fast).

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Physlib.Relativity.LorentzGroup.Boosts.Basic

open LorentzGroup

namespace M174

/- SKELETON · one_le_gamma
  1. Name the matrix entry, then expose the definition:                    R1, R2
       goal becomes  1 ≤ 1 / √(1 - β ^ 2)
  2. Prove the radicand is positive, as a `have`:                           R3 inside R5
       h1 : 0 < 1 - β ^ 2
  3. `1 ≤ 1 / s` → `s ≤ 1`, with the positivity of `s = √(1 - β ^ 2)`:      R6 inside R7
  4. `√(1 - β ^ 2) ≤ 1` → `1 - β ^ 2 ≤ 1`, then arithmetic with `0 ≤ β ^ 2`: R8, then R4 inside R5
-/
-- BEGIN SPEC
theorem one_le_gamma {d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1) :
    1 ≤ (boost i β hβ).1 (Sum.inl 0) (Sum.inl 0) :=
-- END SPEC
  by
    rw [boost_inl_0_inl_0]
    unfold γ
    have h1 : 0 < 1 - β ^ 2 := by nlinarith [abs_lt.mp hβ]
    rw [one_le_div (Real.sqrt_pos.mpr h1)]
    exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg β])

end M174

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. First turn the matrix entry into a real number: physlib names the time-time entry of a boost
    (`boost_inl_0_inl_0`), and `γ` unfolds to `1 / √(1 - β ^ 2)`. Then `1 ≤ 1 / s` holds exactly when
    `0 < s ≤ 1`.
H2. Rewrite the entry to `γ β` and unfold it (R1, R2). Prove `h1 : 0 < 1 - β ^ 2` from both halves of
    `abs_lt.mp hβ` with `nlinarith` (R3, R5). Use `h1`, through `Real.sqrt_pos`, as the premise of
    `one_le_div` (R6, R7); finish `√(1 - β ^ 2) ≤ 1` with `Real.sqrt_le_one` and `sq_nonneg β` (R8, R4, R5).
H3. `rw [boost_inl_0_inl_0]; unfold γ`, then the key step is `rw [one_le_div (Real.sqrt_pos.mpr h1)]`,
    which leaves `√(1 - β ^ 2) ≤ 1`.
-/
