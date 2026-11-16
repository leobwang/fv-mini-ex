/- M074 | Computing a supremum | 10-15 min | sSup, IsLUB, Archimedean, mathlib
GOAL
  Show `sup {1 - 1/(n+1) | n ∈ ℕ} = 1`: `1` is an upper bound, and any `b < 1` is beaten by some term
  (Archimedean property).

REFERENCE
  #check IsLUB.csSup_eq     -- IsLUB s a → s.Nonempty → sSup s = a
  -- `IsLUB s a` unfolds to `a ∈ upperBounds s ∧ ∀ b ∈ upperBounds s, a ≤ b`; `constructor` splits it
  example (s : Set ℝ) (b : ℝ) : b ∈ upperBounds s ↔ ∀ x ∈ s, x ≤ b := mem_upperBounds
  #check Set.mem_range_self -- (i : ι) : f i ∈ Set.range f
  -- `rintro _ ⟨n, rfl⟩` introduces an element of `Set.range f` as `f n`
  #check exists_nat_gt      -- (x : R) : ∃ n : ℕ, x < n
  #check div_lt_iff₀        -- 0 < c → (b / c < a ↔ b < a * c)
  example (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
NOTE: `sSup s` is the least upper bound of `s : Set ℝ`; Mathlib sets it to `0` when `s` is empty or unbounded.
BANNED: isLUB_of_tendsto_atTop, isGLB_of_tendsto_atTop, tendsto_one_div_add_atTop_nhds_zero_nat, Tendsto, tendsto, nhds, 𝓝, Filter, atTop
-/
import Mathlib

namespace M074

-- BEGIN SPEC
theorem sSup_one_sub_inv : sSup (Set.range fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) = 1 :=
-- END SPEC
  by
    apply IsLUB.csSup_eq _ ⟨_, Set.mem_range_self 0⟩
    constructor
    · rintro _ ⟨n, rfl⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      dsimp only
      linarith
    · intro b hb
      by_contra hlt
      push Not at hlt
      have h1 : 0 < 1 - b := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - b))
      have hbn : 1 - 1 / ((n : ℝ) + 1) ≤ b := hb ⟨n, rfl⟩
      have : 1 / ((n : ℝ) + 1) < 1 - b := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ h1] at hn
        nlinarith
      linarith

end M074

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Reduce to `IsLUB (Set.range ...) 1`; the set is nonempty because it contains the `n = 0` term.
H2. `apply IsLUB.csSup_eq _ ⟨_, Set.mem_range_self 0⟩; constructor`. Upper bound: `rintro _ ⟨n, rfl⟩`, then
    `0 < 1 / (n + 1)`. Least: take an upper bound `b`, assume `b < 1` (`by_contra`), and find a term above `b`.
H3. Pick `n` with `1 / (1 - b) < n` (`exists_nat_gt`). Then `1 / ((n : ℝ) + 1) < 1 - b` by
    `rw [div_lt_iff₀ (by positivity)]` and `rw [div_lt_iff₀ h1] at hn; nlinarith` (where `h1 : 0 < 1 - b`);
    compare with `hb ⟨n, rfl⟩` using `linarith`.
-/
