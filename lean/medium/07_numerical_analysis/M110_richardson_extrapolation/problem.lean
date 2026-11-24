/- M110 | Richardson extrapolation | 15-20 min | error expansion, abs, powers, set, gcongr, mathlib
GOAL
  `D t` approximates an exact value `A` with step `t`, with known leading error `c tᵖ` and a remainder
  bounded by `K t^q`. Show that the combination `(2ᵖ D(h/2) - D(h)) / (2ᵖ - 1)` cancels the `c tᵖ`
  term: its error is `O(h^q)`, with the explicit constant below (`c` does not appear in it).

GUIDE
  Entries R1–R18: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M110

/- SKELETON · richardson
  1. Two facts about `2 ^ p`; write the types, or Lean reads them in ℕ:
       h2p : (1:ℝ) < 2 ^ p                    R1 (side goals: norm_num, R2 from hp)
       hpos : (0:ℝ) < 2 ^ p - 1               R3 from h2p
  2. Instantiate hD at `h / 2` and at `h`, BEFORE step 3:                   R4, R5
       e1 : |D (h / 2) - (A + c * (h / 2) ^ p)| ≤ K * (h / 2) ^ q
       e2 : |D h - (A + c * h ^ p)| ≤ K * h ^ q
  3. Name the remainders u := D (h / 2) - (A + c * (h / 2) ^ p) and
     w := D h - (A + c * h ^ p); e1, e2 become |u| ≤ …, |w| ≤ …:           R6, R6
  4. Prove the cancellation fact (2 ^ p * (h / 2) ^ p = h ^ p kills c):
       key : (2 ^ p * D (h / 2) - D h) / (2 ^ p - 1) - A = (2 ^ p * u - w) / (2 ^ p - 1)
       proof: rw [hu, hw], R7, R8, R9
  5. rw [key], then strip the positive denominator:                        R10, R11, R12
       goal: |2 ^ p * u - w| ≤ (2 ^ p / 2 ^ q + 1) / (2 ^ p - 1) * K * h ^ q * (2 ^ p - 1)
  6. Triangle step  htri : |2 ^ p * u - w| ≤ 2 ^ p * |u| + |w|:            R13: R14, then R15, R11 with R5
  7. Put e1 in the form K * (h ^ q / 2 ^ q):                                R16 with R7
  8. Close the goal with a calc (R13):
       htri  →  ≤ 2 ^ p * (K * (h ^ q / 2 ^ q)) + K * h ^ q   by R17 (uses e1, e2)
             →  = the right side                                by R18
-/
-- BEGIN SPEC
theorem richardson (p q : ℕ) (A c K h : ℝ) (D : ℝ → ℝ) (hp : 1 ≤ p) (hh : 0 < h)
    (hD : ∀ t, 0 < t → |D t - (A + c * t ^ p)| ≤ K * t ^ q) :
    |(2 ^ p * D (h / 2) - D h) / (2 ^ p - 1) - A| ≤ (2 ^ p / 2 ^ q + 1) / (2 ^ p - 1) * K * h ^ q :=
-- END SPEC
  sorry

end M110

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The `c` terms cancel because `2 ^ p * (h / 2) ^ p = h ^ p`. Name the two remainders
    `u = D (h/2) - (A + c (h/2)ᵖ)` and `w = D h - (A + c hᵖ)`; `hD` bounds each (at `h / 2` and at `h`).
H2. Get `hpos : (0:ℝ) < 2 ^ p - 1` (via `one_lt_pow₀`, `linarith`) and `e1`, `e2` from `hD`, then `set u`, `set w`.
    Prove `key`: the error equals `(2 ^ p * u - w) / (2 ^ p - 1)`. Rewrite with it, clear the denominator,
    and finish with a `calc`: triangle inequality, then the two bounds, then algebra.
H3. `key` by `rw [hu, hw, div_pow]; field_simp; ring`; then `rw [key, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]`.
    After `rw [div_pow] at e1`, the middle `calc` step is
    `_ ≤ 2 ^ p * (K * (h ^ q / 2 ^ q)) + K * h ^ q := by gcongr`, and `field_simp` closes the last one.
-/
