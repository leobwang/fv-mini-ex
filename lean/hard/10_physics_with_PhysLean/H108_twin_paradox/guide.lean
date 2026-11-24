/- Guide for H108 (Twin paradox: the travelling twin is younger).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Entries that build a fact (`(… ).mp h`, `norm_nonneg x`, a structure field) use `have h' := …`, so
the context gains `h'` and you can read off exactly what was produced. `g : … → G` then only closes
the example.
Part W: worked combinations on objects that are NOT the exercise's (plain reals, `u - v`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.Relativity.Special.TwinParadox.Basic

open Lorentz Vector SpecialRelativity

namespace H108Guide

/-! # Part R · Reference entries -/

/-! ## The causal future and the Minkowski product -/

/-! ### R1. `rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩` on `causallyFollows p q` · goal list: one goal per case
`causallyFollows p q` unfolds to `q ∈ interiorFutureLightCone p ∨ q ∈ futureLightConeBoundary p`, and
each set is `{q | … ∧ …}`; `rcases` sees through both definitions. -/
example {d : ℕ} (p q : SpaceTime d) (G : Prop) (h : causallyFollows p q)
    (ht : causalCharacter (q - p) = .timeLike → 0 < (q - p).timeComponent → G)
    (hl : causalCharacter (q - p) = .lightLike → 0 ≤ (q - p).timeComponent → G) : G := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  exact ht h1 h2
  exact hl h1 h2

/-! ### R2. `timeLike_iff_norm_sq_pos` · `causalCharacter p = .timeLike ↔ 0 < ⟪p, p⟫ₘ`
`(timeLike_iff_norm_sq_pos p).mp h` uses the `→` half (`Iff.mp`): context gains `0 < ⟪p, p⟫ₘ`. -/
example {d : ℕ} (p : Lorentz.Vector d) (h : causalCharacter p = .timeLike) (G : Prop)
    (g : 0 < ⟪p, p⟫ₘ → G) : G := by
  have h' := (timeLike_iff_norm_sq_pos p).mp h
  exact g h'

/-! ### R3. `lightLike_iff_norm_sq_zero` · `causalCharacter p = .lightLike ↔ ⟪p, p⟫ₘ = 0` -/
example {d : ℕ} (p : Lorentz.Vector d) (h : causalCharacter p = .lightLike) (G : Prop)
    (g : ⟪p, p⟫ₘ = 0 → G) : G := by
  have h' := (lightLike_iff_norm_sq_zero p).mp h
  exact g h'

/-! ### R4. `hlt.le`, `heq.ge` · context gains a `≤` from a `<` (`LT.lt.le`) or from an `=` (`Eq.ge`)
`Eq.ge : a = b → b ≤ a`, so from `⟪p, p⟫ₘ = 0` it gives `0 ≤ ⟪p, p⟫ₘ`. -/
example (x y : ℝ) (hlt : x < y) (heq : x = y) (G : Prop) (g : x ≤ y → y ≤ x → G) : G := by
  have h1 := hlt.le
  have h2 := heq.ge
  exact g h1 h2

/-! ### R5. `obtain ⟨h1, h2⟩ := h` · context: `h : A ∧ B` → `h1 : A`, `h2 : B` -/
example (A B G : Prop) (h : A ∧ B) (g : A → B → G) : G := by
  obtain ⟨h1, h2⟩ := h
  exact g h1 h2

/-! ### R6. `minkowskiProduct_self_eq_timeComponent_spatialPart` · `⟪p, p⟫ₘ = ‖p⁰‖ ^ 2 - ‖p⃗‖ ^ 2`
Here `rw [...] at h` rewrites the hypothesis `h`, not the goal. -/
example {d : ℕ} (p : Lorentz.Vector d) (h : 0 ≤ ⟪p, p⟫ₘ) (G : Prop)
    (g : 0 ≤ ‖p.timeComponent‖ ^ 2 - ‖p.spatialPart‖ ^ 2 → G) : G := by
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at h
  exact g h

/-! ### R7. `Real.norm_eq_abs`, `sq_abs` · goal: `‖x‖ ^ 2` → `|x| ^ 2` → `x ^ 2` for a real `x` -/
example (x : ℝ) (P : ℝ → Prop) (h : P (x ^ 2)) : P (‖x‖ ^ 2) := by
  rw [Real.norm_eq_abs]
  rw [sq_abs]
  exact h

/-! ### R8. `sub_nonneg` · `0 ≤ a - b ↔ b ≤ a` -/
example (a b : ℝ) (h : 0 ≤ a - b) (G : Prop) (g : b ≤ a → G) : G := by
  rw [sub_nonneg] at h
  exact g h

/-! ### R9. `simpa [lemmas] using h` · closes the goal: simplifies `h` and the goal, then matches them
`simp` already knows R7 `Real.norm_eq_abs` and R8 `sub_nonneg`; `sq_abs` has to be named. -/
example (x y : ℝ) (h : 0 ≤ ‖x‖ ^ 2 - y) : y ≤ x ^ 2 := by
  simpa [sq_abs] using h

/-! ### R10. `abs_le_of_sq_le_sq'` · `a ^ 2 ≤ b ^ 2 → 0 ≤ b → -b ≤ a ∧ a ≤ b`; `.2` is the right half -/
example (a b : ℝ) (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) (G : Prop) (g : a ≤ b → G) : G := by
  have h' := abs_le_of_sq_le_sq' h hb
  exact g h'.2

/-! ## Naming pieces, and inequalities between reals -/

/-! ### R11. `set a := e` · context gains `a : ℝ := e`; every `e` in the goal and context becomes `a`
`simp only [a]` (or `simp [a, …]`) unfolds `a` back to `e`. -/
example {d : ℕ} (u : Lorentz.Vector d) (P : ℝ → Prop) (h : P u.timeComponent) :
    P u.timeComponent := by
  set a := u.timeComponent
  simp only [a]
  exact h

/-! ### R12. `norm_nonneg` · `0 ≤ ‖x‖` for any `x` of a normed type -/
example {E : Type} [NormedAddCommGroup E] (x : E) (G : Prop) (g : 0 ≤ ‖x‖ → G) : G := by
  have h' := norm_nonneg x
  exact g h'

/-! ### R13. `minkowskiProduct_eq_timeComponent_spatialPart` · `⟪p, q⟫ₘ = p⁰ * q⁰ - inner ℝ p⃗ q⃗` -/
example {d : ℕ} (p q : Lorentz.Vector d) (P : ℝ → Prop)
    (h : P (p.timeComponent * q.timeComponent - inner ℝ p.spatialPart q.spatialPart)) :
    P ⟪p, q⟫ₘ := by
  rw [minkowskiProduct_eq_timeComponent_spatialPart]
  exact h

/-! ### R14. `real_inner_le_norm` · Cauchy–Schwarz: `inner ℝ x y ≤ ‖x‖ * ‖y‖` -/
example {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) (G : Prop) (g : inner ℝ x y ≤ ‖x‖ * ‖y‖ → G) :
    G := by
  have h' := real_inner_le_norm x y
  exact g h'

/-! ### R15. `linarith [t₁, …]` · closes a linear (in)equality from the context plus the facts `tᵢ` -/
example (f : ℝ → ℝ) (hf : ∀ x, f x ≤ 1) (a b : ℝ) (hb : b = 2 - f a) : 1 ≤ b := by
  linarith [hf a]

/-! ### R16. `nlinarith [t₁, …]` · closes a polynomial (in)equality; also multiplies hypotheses in pairs -/
example (a b c e : ℝ) (hc : 0 ≤ c) (he : 0 ≤ e) (hca : c ≤ a) (heb : e ≤ b) : c * e ≤ a * b := by
  nlinarith

/-! ### R17. `Real.sqrt_mul` · `0 ≤ x → √(x * y) = √x * √y`; used right to left: `rw [← Real.sqrt_mul hx]`
`√x` is `Real.sqrt x`, which is `0` for `x < 0`; hence the hypothesis `0 ≤ x`. -/
example (x y : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P √(x * y)) : P (√x * √y) := by
  rw [← Real.sqrt_mul hx]
  exact h

/-! ### R18. `refine le_trans ?_ h` · goal `a ≤ c` with `h : b ≤ c` → goal `a ≤ b` -/
example (a b c : ℝ) (h : b ≤ c) (hab : a ≤ b) : a ≤ c := by
  refine le_trans ?_ h
  exact hab

/-! ### R19. `Real.sqrt_le_left` · `0 ≤ y → (√x ≤ y ↔ x ≤ y ^ 2)`; `rw` with it squares both sides -/
example (x y : ℝ) (hy : 0 ≤ y) (h : x ≤ y ^ 2) : √x ≤ y := by
  rw [Real.sqrt_le_left hy]
  exact h

/-! ### R20. `sq_nonneg` · `0 ≤ a ^ 2`; the usual hint for `nlinarith` -/
example (a b : ℝ) (G : Prop) (g : 0 ≤ (a - b) ^ 2 → G) : G := by
  have h' := sq_nonneg (a - b)
  exact g h'

/-! ### R21. `apply Real.le_sqrt_of_sq_le` · `x ^ 2 ≤ y → x ≤ √y` · goal `x ≤ √y` → `x ^ 2 ≤ y` -/
example (x y : ℝ) (h : x ^ 2 ≤ y) : x ≤ √y := by
  apply Real.le_sqrt_of_sq_le
  exact h

/-! ## Expanding `⟪u + v, u + v⟫ₘ` and the squares -/

/-! ### R22. `map_add` · goal: `⟪u + v, w⟫ₘ` → `⟪u, w⟫ₘ + ⟪v, w⟫ₘ` (and in the second slot)
`minkowskiProduct` is a linear map into linear maps, so `map_add` splits the first argument into a sum
of maps `(minkowskiProduct u + minkowskiProduct v) w`, and plain `simp` then applies that sum. -/
example {d : ℕ} (u v w : Lorentz.Vector d) (P : ℝ → Prop) (h : P (⟪u, w⟫ₘ + ⟪v, w⟫ₘ)) :
    P ⟪u + v, w⟫ₘ := by
  simp only [map_add]
  simp
  exact h

/-! ### R23. `minkowskiProduct_symm` · `⟪p, q⟫ₘ = ⟪q, p⟫ₘ`
Give the arguments, `minkowskiProduct_symm q p`, so that only `⟪q, p⟫ₘ` is turned around. -/
example {d : ℕ} (p q : Lorentz.Vector d) (P : ℝ → Prop) (h : P (⟪p, q⟫ₘ + ⟪p, q⟫ₘ)) :
    P (⟪p, q⟫ₘ + ⟪q, p⟫ₘ) := by
  rw [minkowskiProduct_symm q p]
  exact h

/-! ### R24. `add_sq` · `(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2` -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (a ^ 2 + 2 * a * b + b ^ 2)) : P ((a + b) ^ 2) := by
  rw [add_sq]
  exact h

/-! ### R25. `Real.sq_sqrt` · `0 ≤ x → √x ^ 2 = x` -/
example (x : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P x) : P (√x ^ 2) := by
  rw [Real.sq_sqrt hx]
  exact h

/-! ## The twin paradox structure -/

/-! ### R26. `unfold` · goal: `T.ageGap` → the three proper times → three square roots
`SpaceTime.properTime q p = √⟪p - q, p - q⟫ₘ` (note the order: from `q` to `p`). -/
example (T : InstantaneousTwinParadox) (P : ℝ → Prop)
    (h : P (√⟪T.endPoint - T.startPoint, T.endPoint - T.startPoint⟫ₘ -
      (√⟪T.twinBMid - T.startPoint, T.twinBMid - T.startPoint⟫ₘ +
        √⟪T.endPoint - T.twinBMid, T.endPoint - T.twinBMid⟫ₘ))) :
    P T.ageGap := by
  unfold InstantaneousTwinParadox.ageGap
  unfold InstantaneousTwinParadox.properTimeTwinA InstantaneousTwinParadox.properTimeTwinB
  unfold SpaceTime.properTime
  exact h

/-! ### R27. A structure field, `T.twinBMid_causallyFollows_startPoint` · context gains a causal fact
The other fields: `T.endPoint_causallyFollows_twinBMid`, `T.endPoint_causallyFollows_startPoint`. -/
example (T : InstantaneousTwinParadox) (G : Prop)
    (g : causallyFollows T.startPoint T.twinBMid → G) : G := by
  have h' := T.twinBMid_causallyFollows_startPoint
  exact g h'

/-! ### R28. `abel` · closes an identity in a commutative additive group (`+`, `-`, `0`, `n • x`) -/
example {E : Type} [AddCommGroup E] (x y : E) : x + y - x = y := by abel

/-! ### R29. `rw [show t = t' by tac] at h` · context: `h` with `t` replaced by `t'`
`show t = t' by tac` is a one-off lemma proved on the spot. -/
example {E : Type} [AddCommGroup E] (x y z : E) (P : E → Prop) (h : P (y - x + (z - y))) :
    P (z - x) := by
  rw [show y - x + (z - y) = z - x by abel] at h
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. AM–GM `√x √y ≤ (x + y) / 2`: R17, then R19 (square), then R16 with R20 -/
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : √x * √y ≤ (x + y) / 2 := by
  rw [← Real.sqrt_mul hx]
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith [sq_nonneg (x - y)]

/-! ### W2. `√x + √y ≤ √(2 (x + y))`: R21 (square), R24, R25, then R16 with R20 -/
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : √x + √y ≤ √(2 * (x + y)) := by
  apply Real.le_sqrt_of_sq_le
  rw [add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
  nlinarith [sq_nonneg (√x - √y), Real.sq_sqrt hx, Real.sq_sqrt hy]

/-! ### W3. Expanding a Minkowski square of a difference: `simp` with the linearity lemma and R23 -/
example {d : ℕ} (u v : Lorentz.Vector d) :
    ⟪u - v, u - v⟫ₘ = ⟪u, u⟫ₘ - 2 * ⟪u, v⟫ₘ + ⟪v, v⟫ₘ := by
  simp [map_sub, minkowskiProduct_symm v u]
  ring

end H108Guide
