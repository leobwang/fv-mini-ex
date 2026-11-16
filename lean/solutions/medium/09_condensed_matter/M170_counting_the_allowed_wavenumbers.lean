/- M170 | Counting the allowed wavenumbers | 10-15 min | Set.ncard, injectivity, casts, physlib
GOAL
  Periodic boundary conditions allow exactly `N` wavenumbers, one per site:
  the set `T.QuantaWaveNumber` has `T.N` elements.

REFERENCE
  -- T.QuantaWaveNumber = {x | ∃ n : Fin T.N, 2 * Real.pi / (T.a * T.N) * ((n : ℝ) - (T.N / 2 : ℕ)) = x}
  #check Set.ncard_range_of_injective  -- Function.Injective f → (Set.range f).ncard = Nat.card α
  #check Nat.card_eq_fintype_card      -- Nat.card α = Fintype.card α   (then `Fintype.card_fin`)
  #check mul_left_cancel₀  -- a ≠ 0 → a * b = a * c → b = c
  #check sub_left_inj      -- b - a = c - a ↔ b = c
  #check TightBindingChain.a_pos  -- 0 < T.a   (and `NeZero.pos T.N : 0 < T.N`)
  example (m n : Fin 5) (h : (m : ℝ) = n) : m = n := Fin.ext (by exact_mod_cast h)
  example (s t : Set ℕ) (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by ext x; exact h x  -- set equality by membership
NOTE: `Set.ncard s` counts a set (it is `0` for infinite sets, so finiteness is part of the claim).
  `(T.N / 2 : ℕ)` is natural-number division, i.e. `⌊N/2⌋`, then cast to `ℝ`.
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter

namespace M170

-- BEGIN SPEC
theorem card_wavenumbers (T : TightBindingChain) : T.QuantaWaveNumber.ncard = T.N :=
-- END SPEC
  by
    have hset : T.QuantaWaveNumber = Set.range (fun n : Fin T.N =>
        2 * Real.pi / (T.a * T.N) * ((n : ℝ) - (T.N / 2 : ℕ))) := by
      ext x
      simp [TightBindingChain.QuantaWaveNumber]
    rw [hset, Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
    intro m n h
    have hc : 2 * Real.pi / (T.a * T.N) ≠ 0 := by
      have := T.a_pos
      have : (0 : ℝ) < T.N := by exact_mod_cast NeZero.pos T.N
      positivity
    exact Fin.ext (by exact_mod_cast sub_left_inj.mp (mul_left_cancel₀ hc h))

end M170

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The definition is the range of a function `Fin T.N → ℝ`; count it as the image of an
    injective map.
H2. First show `T.QuantaWaveNumber = Set.range (fun n : Fin T.N => 2 * Real.pi / (T.a * T.N) * ((n : ℝ) - (T.N / 2 : ℕ)))`
    (`ext x; simp [TightBindingChain.QuantaWaveNumber]`).
    Injectivity: the prefactor is nonzero (`positivity` after `T.a_pos` and `0 < (T.N : ℝ)`),
    cancel it, then cancel the shift, then cast back to `Fin`.
H3. `rw [this, Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]`; for
    injectivity: `intro m n h; exact Fin.ext (by exact_mod_cast sub_left_inj.mp (mul_left_cancel₀ hc h))`.
-/
