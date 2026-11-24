/- Guide for H063 (Power iteration converges).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Vectors are functions `ι → ℝ` on any finite index type `ι` (`[Fintype ι]`); the exercise uses `Fin 2`.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Filter Topology
open scoped Matrix

namespace H063Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · Symmetric matrices: moving `A` across a dot product -/

/-! ### R1. `Matrix.dotProduct_mulVec` · `v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w` · goal -/
example {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (v w : ι → ℝ) (P : ℝ → Prop)
    (h : P ((v ᵥ* A) ⬝ᵥ w)) : P (v ⬝ᵥ (A *ᵥ w)) := by
  rw [Matrix.dotProduct_mulVec]
  exact h

/-! ### R2. `Matrix.mulVec_transpose` · `Aᵀ *ᵥ x = x ᵥ* A`; right to left: `rw [← …]` · goal -/
example {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) (P : (ι → ℝ) → Prop)
    (h : P (Aᵀ *ᵥ x)) : P (x ᵥ* A) := by
  rw [← Matrix.mulVec_transpose]
  exact h

/-! ### R3. `rw [e] at h` · context: rewrites the hypothesis `h`, not the goal -/
example {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (u : ι → ℝ) (μ : ℝ) (Q : (ι → ℝ) → Prop)
    (hu : A *ᵥ u = μ • u) (h : Q (A *ᵥ u)) : Q (μ • u) := by
  rw [hu] at h
  exact h

/-! ### R4. `dotProduct_smul` · `v ⬝ᵥ (c • w) = c • (v ⬝ᵥ w)` · goal -/
example {ι : Type} [Fintype ι] (c : ℝ) (v w : ι → ℝ) (P : ℝ → Prop) (h : P (c • (v ⬝ᵥ w))) :
    P (v ⬝ᵥ (c • w)) := by
  rw [dotProduct_smul]
  exact h

/-! ### R5. `smul_dotProduct` · `(c • v) ⬝ᵥ w = c • (v ⬝ᵥ w)` · goal -/
example {ι : Type} [Fintype ι] (c : ℝ) (v w : ι → ℝ) (P : ℝ → Prop) (h : P (c • (v ⬝ᵥ w))) :
    P ((c • v) ⬝ᵥ w) := by
  rw [smul_dotProduct]
  exact h

/-! ### R6. `smul_eq_mul` · `c • a = c * a` when both are numbers · goal -/
example (c a : ℝ) (P : ℝ → Prop) (h : P (c * a)) : P (c • a) := by
  rw [smul_eq_mul]
  exact h

/-! ### R7. `linarith` · closes a (in)equality that is a linear consequence of the hypotheses
Products such as `a * x` count as single unknowns, after multiplying out. -/
example (a b x : ℝ) (h : a * x = b * x + 2) : (a - b) * x = 2 := by
  linarith

/-! ### R8. `mul_eq_zero` · `a * b = 0 ↔ a = 0 ∨ b = 0` · context, with `rw … at h` -/
example (a b : ℝ) (Q : Prop) (h : a * b = 0) (hQ : a = 0 ∨ b = 0 → Q) : Q := by
  rw [mul_eq_zero] at h
  exact hQ h

/-! ### R9. `sub_ne_zero` · `a - b ≠ 0 ↔ a ≠ b` · goal -/
example (a b : ℝ) (hne : a ≠ b) : a - b ≠ 0 := by
  rw [sub_ne_zero]
  exact hne

/-! ### R10. `Or.resolve_left` · from `h : A ∨ B` and `¬A`, get `B` · closes the goal -/
example (A B : Prop) (h : A ∨ B) (hna : ¬A) : B := by
  exact h.resolve_left hna

/-! ## Part 2 · Orthonormal bases: expanding dot products -/

/-! ### R11. `dotProduct_comm` · `v ⬝ᵥ w = w ⬝ᵥ v` · goal -/
example {ι : Type} [Fintype ι] (v w : ι → ℝ) (P : ℝ → Prop) (h : P (w ⬝ᵥ v)) :
    P (v ⬝ᵥ w) := by
  rw [dotProduct_comm]
  exact h

/-! ### R12. `dotProduct_add`, `add_dotProduct` · `⬝ᵥ` distributes over `+` on either side · goal -/
example {ι : Type} [Fintype ι] (x y v w : ι → ℝ) (P : ℝ → Prop)
    (h : P (x ⬝ᵥ v + x ⬝ᵥ w + (y ⬝ᵥ v + y ⬝ᵥ w))) : P ((x + y) ⬝ᵥ (v + w)) := by
  rw [add_dotProduct]
  rw [dotProduct_add, dotProduct_add]
  exact h

/-! ## Part 3 · Induction on the iteration -/

/-! ### R13. `induction n with | zero => ?_ | succ n ih => ?_` · goal list: base case and step -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1)) (n : ℕ) : P n := by
  induction n with | zero => ?_ | succ n ih => ?_
  exacts [h0, hs n ih]

/-! ### R14. `simp only [f]` on a recursive `def` · goal: `f 0`, `f (n + 1)` → that case's body
A `let y := e` in the body is substituted away (`y` becomes `e`). -/
noncomputable def iter (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 =>
    let y := 3 * iter x₀ n
    (√y)⁻¹ * y

example (x₀ : ℝ) (n : ℕ) (P : ℝ → Prop) (h0 : P x₀) (h : P ((√(3 * iter x₀ n))⁻¹ * (3 * iter x₀ n))) :
    P (iter x₀ 0) ∧ P (iter x₀ (n + 1)) := by
  simp only [iter]
  exact ⟨h0, h⟩

/-! ### R15. `obtain ⟨c, hc, hx⟩ := h` · context: `h : ∃ c, A c ∧ B c` → `c`, `hc : A c`, `hx : B c` -/
example (A B : ℝ → Prop) (G : Prop) (h : ∃ c, A c ∧ B c) (hG : ∀ c, A c → B c → G) : G := by
  obtain ⟨c, hc, hx⟩ := h
  exact hG c hc hx

/-! ### R16. `Matrix.mulVec_smul` · `A *ᵥ (c • x) = c • (A *ᵥ x)` · goal -/
example {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) (P : (ι → ℝ) → Prop)
    (h : P (c • (A *ᵥ x))) : P (A *ᵥ (c • x)) := by
  rw [Matrix.mulVec_smul]
  exact h

/-! ### R17. `Matrix.mulVec_add` · `A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y` · goal -/
example {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (x y : ι → ℝ) (P : (ι → ℝ) → Prop)
    (h : P (A *ᵥ x + A *ᵥ y)) : P (A *ᵥ (x + y)) := by
  rw [Matrix.mulVec_add]
  exact h

/-! ### R18. `smul_smul` · `a • b • x = (a * b) • x` · goal -/
example {ι : Type} (a b : ℝ) (x : ι → ℝ) (P : (ι → ℝ) → Prop) (h : P ((a * b) • x)) :
    P (a • b • x) := by
  rw [smul_smul]
  exact h

/-! ### R19. `congr 2` · goal list: `c • (x + y) = c • (x' + y')` → `x = x'`, `y = y'`
`congr k` strips `k` layers of the same function from both sides; equal arguments close by `rfl`. -/
example {ι : Type} (c : ℝ) (x y x' y' : ι → ℝ) (hx : x' = x) (hy : y' = y) :
    c • (x + y) = c • (x' + y') := by
  congr 2
  exacts [hx.symm, hy.symm]

/-! ### R20. `mul_pos` · `0 < a → 0 < b → 0 < a * b` · goal list (with `apply`) -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  apply mul_pos
  exacts [ha, hb]

/-! ### R21. `mul_ne_zero`, `pow_ne_zero` · `a ≠ 0 → b ≠ 0 → a * b ≠ 0`; `a ≠ 0 → a ^ n ≠ 0` -/
example (a b : ℝ) (n : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ^ n ≠ 0 := by
  apply mul_ne_zero
  exacts [ha, pow_ne_zero n hb]

/-! ### R22. `mul_self_pos` · `0 < a * a ↔ a ≠ 0` · goal; `mul_self_nonneg a : 0 ≤ a * a` -/
example (a : ℝ) (ha : a ≠ 0) : 0 < a * a := by
  rw [mul_self_pos]
  exact ha

example (b : ℝ) : 0 ≤ b * b := mul_self_nonneg b

/-! ### R23. `add_pos_of_pos_of_nonneg` · `0 < a → 0 ≤ b → 0 < a + b` · goal list (with `apply`) -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b := by
  apply add_pos_of_pos_of_nonneg
  exacts [ha, hb]

/-! ### R24. `set y := e with hy` · context gains `y := e` and `hy : y = e`; every `e` → `y` -/
example (f : ℝ → ℝ) (x : ℝ) (P : ℝ → Prop) (h : ∀ z, P (z + z)) : P (f x + f x) := by
  set y := f x with hy
  exact h y

/-! ### R25. `inv_pos`, `Real.sqrt_pos` · `0 < a⁻¹ ↔ 0 < a`; `0 < √x ↔ 0 < x` · goal -/
example (x : ℝ) (hx : 0 < x) : 0 < (√x)⁻¹ := by
  rw [inv_pos]
  rw [Real.sqrt_pos]
  exact hx

/-! ### R26. `mul_smul` · `(a * b) • x = a • b • x` · goal -/
example {ι : Type} (a b : ℝ) (x : ι → ℝ) (P : (ι → ℝ) → Prop) (h : P (a • b • x)) :
    P ((a * b) • x) := by
  rw [mul_smul]
  exact h

/-! ## Part 4 · The iterate is a unit vector -/

/-! ### R27. `rcases le_or_gt a b with h | h` · goal list: one goal with `h : a ≤ b`, one with `h : b < a` -/
example (a b : ℝ) (Q : Prop) (h1 : a ≤ b → Q) (h2 : b < a → Q) : Q := by
  rcases le_or_gt a b with h | h
  exacts [h1 h, h2 h]

/-! ### R28. `left`, `right` · goal: `A ∨ B` → `A` (resp. `B`) -/
example (A B : Prop) (hb : B) : A ∨ B := by
  right
  exact hb

/-! ### R29. `Real.sqrt_eq_zero'` · `√x = 0 ↔ x ≤ 0` · goal, used as `rw [Real.sqrt_eq_zero'.mpr hx]` -/
example (x : ℝ) (hx : x ≤ 0) (P : ℝ → Prop) (h : P 0) : P √x := by
  rw [Real.sqrt_eq_zero'.mpr hx]
  exact h

/-! ### R30. `inv_zero`, `zero_mul` · `0⁻¹ = 0`; `0 * a = 0` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P 0) : P (0⁻¹ * a) := by
  rw [inv_zero]
  rw [zero_mul]
  exact h

/-! ### R31. `mul_assoc` · `a * b * c = a * (b * c)`; right to left regroups to the left · goal -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P (a * b * c)) : P (a * (b * c)) := by
  rw [← mul_assoc]
  exact h

/-! ### R32. `mul_inv` · `(a * b)⁻¹ = a⁻¹ * b⁻¹`; right to left: `rw [← mul_inv]` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (a * b)⁻¹) : P (a⁻¹ * b⁻¹) := by
  rw [← mul_inv]
  exact h

/-! ### R33. `Real.mul_self_sqrt` · `0 ≤ x → √x * √x = x` · goal -/
example (x : ℝ) (hx : 0 ≤ x) (P : ℝ → Prop) (h : P x) : P (√x * √x) := by
  rw [Real.mul_self_sqrt hx]
  exact h

/-! ### R34. `inv_mul_cancel₀` · `a ≠ 0 → a⁻¹ * a = 1` · goal -/
example (a : ℝ) (ha : a ≠ 0) (P : ℝ → Prop) (h : P 1) : P (a⁻¹ * a) := by
  rw [inv_mul_cancel₀ ha]
  exact h

/-! ## Part 5 · A geometric ratio tends to 0 -/

/-! ### R35. `rintro rfl` · goal `x ≠ 0` → `False`; context: `x` replaced by `0` everywhere -/
example (x : ℝ) (P : ℝ → Prop) (hx : P x) (h0 : ¬P 0) : x ≠ 0 := by
  rintro rfl
  exact h0 hx

/-! ### R36. `abs_zero` · `|0| = 0` · context, with `rw … at h`; then `linarith [abs_nonneg a]` -/
example (a : ℝ) (h : |a| < |0|) : False := by
  rw [abs_zero] at h
  linarith [abs_nonneg a]

/-! ### R37. `div_pow` · `(a / b) ^ n = a ^ n / b ^ n` · goal -/
example (a b : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (a ^ n / b ^ n)) : P ((a / b) ^ n) := by
  rw [div_pow]
  exact h

/-! ### R38. `div_lt_one` · `0 < b → (a / b < 1 ↔ a < b)` · goal -/
example (a b : ℝ) (hb : 0 < b) (h : a < b) : a / b < 1 := by
  rw [div_lt_one hb]
  exact h

/-! ### R39. `positivity` · closes `0 < e` or `0 ≤ e` from the shape of `e` (squares, sums, `≠ 0` facts) -/
example (a b : ℝ) (ha : a ≠ 0) : 0 < a ^ 2 + b ^ 2 := by
  positivity

/-! ### R40. `sq_lt_sq` · `a ^ 2 < b ^ 2 ↔ |a| < |b|` · goal -/
example (a b : ℝ) (h : |a| < |b|) : a ^ 2 < b ^ 2 := by
  rw [sq_lt_sq]
  exact h

/-! ### R41. `tendsto_pow_atTop_nhds_zero_of_lt_one` · `0 ≤ r → r < 1 → rⁿ → 0` · context -/
example (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) (G : Prop)
    (hG : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) → G) : G := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  exact hG h

/-! ### R42. `Filter.Tendsto.const_mul` · `f → a` gives `b * f → b * a` · context -/
example (f : ℕ → ℝ) (a b : ℝ) (hf : Tendsto f atTop (𝓝 a)) (G : Prop)
    (hG : Tendsto (fun n => b * f n) atTop (𝓝 (b * a)) → G) : G := by
  have h := hf.const_mul b
  exact hG h

/-! ### R43. `Filter.Tendsto.congr` · `Tendsto f l l'` and `∀ n, f n = g n` give `Tendsto g l l'` · goal -/
example (f g : ℕ → ℝ) (a : ℝ) (hf : Tendsto f atTop (𝓝 a)) (hfg : ∀ n, f n = g n) :
    Tendsto g atTop (𝓝 a) := by
  refine hf.congr fun n => ?_
  exact hfg n

/-! ### R44. `mul_div_mul_comm` · `a * b / (c * d) = a / c * (b / d)` · goal -/
example (a b c d : ℝ) (P : ℝ → Prop) (h : P (a / c * (b / d))) : P (a * b / (c * d)) := by
  rw [mul_div_mul_comm]
  exact h

/-! ### R45. `mul_pow`, `pow_mul` · `(a * b) ^ n = a ^ n * b ^ n`; `a ^ (m * n) = (a ^ m) ^ n` · goal -/
example (a b : ℝ) (m n : ℕ) (P : ℝ → Prop) (h : P (a ^ n * b ^ (m * n))) :
    P ((a * (b ^ m)) ^ n) := by
  rw [mul_pow]
  rw [← pow_mul]
  exact h

/-! ## Part 6 · Limits of combinations -/

/-! ### R46. `lt_irrefl` · `lt_irrefl a : ¬a < a` · closes `False` from `h : a < a` -/
example (a : ℝ) (h : a < a) : False := by
  exact lt_irrefl a h

/-! ### R47. `field_simp` · goal: clears denominators it can prove `≠ 0` (from hypotheses `h : d ≠ 0`) -/
example (a b x y : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h : x * b = a * y) : x / a = y / b := by
  field_simp
  exact h

/-! ### R48. `eq_div_iff` · `c ≠ 0 → (a = b / c ↔ a * c = b)` · goal -/
example (a b c : ℝ) (hc : c ≠ 0) (h : a * c = b) : a = b / c := by
  rw [eq_div_iff hc]
  exact h

/-! ### R49. `tendsto_const_nhds` · a constant sequence tends to its value · context
`(x := c)` fixes the constant; without it Lean must guess `c` from later use. -/
example (c : ℝ) (G : Prop) (hG : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) → G) : G := by
  have h := tendsto_const_nhds (x := c) (f := (atTop : Filter ℕ))
  exact hG h

/-! ### R50. `Filter.Tendsto.add` · `f → a`, `g → b` give `f + g → a + b` · context -/
example (f g : ℕ → ℝ) (a b : ℝ) (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b))
    (G : Prop) (hG : Tendsto (fun n => f n + g n) atTop (𝓝 (a + b)) → G) : G := by
  have h := hf.add hg
  exact hG h

/-! ### R51. `Filter.Tendsto.mul_const` · `f → a` gives `f * b → a * b` · context -/
example (f : ℕ → ℝ) (a b : ℝ) (hf : Tendsto f atTop (𝓝 a)) (G : Prop)
    (hG : Tendsto (fun n => f n * b) atTop (𝓝 (a * b)) → G) : G := by
  have h := hf.mul_const b
  exact hG h

/-! ### R52. `Filter.Tendsto.div` · `f → a`, `g → b`, `b ≠ 0` give `f / g → a / b` · context -/
example (f g : ℕ → ℝ) (a b : ℝ) (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b))
    (hb : b ≠ 0) (G : Prop) (hG : Tendsto (fun n => f n / g n) atTop (𝓝 (a / b)) → G) : G := by
  have h := hf.div hg hb
  exact hG h

/-! ### R53. `tendsto_add_atTop_iff_nat` · `(fun n => f (n + k)) → L ↔ f → L` · goal
Right to left drops the first `k` terms, so you may assume `n ≥ k`. -/
example (f : ℕ → ℝ) (L : ℝ) (h : Tendsto (fun n => f (n + 1)) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 L) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  exact h

/-! ### R54. `tendsto_add_atTop_nat`, `Filter.Tendsto.comp` · `f → L` gives `f (· + k) → L` · context -/
example (f : ℕ → ℝ) (L : ℝ) (hf : Tendsto f atTop (𝓝 L)) (G : Prop)
    (hG : Tendsto (f ∘ fun n => n + 1) atTop (𝓝 L) → G) : G := by
  have h := hf.comp (tendsto_add_atTop_nat 1)
  exact hG h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A limit of a quotient: R49–R52, normalise the limit with `simp only … at h`, then R43 -/
example (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n => (3 + s n * 5) / (2 + s n)) atTop (𝓝 (3 / 2)) := by
  have h := (tendsto_const_nhds (x := (3 : ℝ))).add (hs.mul_const 5) |>.div
    ((tendsto_const_nhds (x := (2 : ℝ))).add hs) (by norm_num)
  simp only [zero_mul, add_zero] at h
  exact h

/-! ### W2. A rescaled iteration by induction: R13, R14, R15, then a witness with R20, R25 -/
noncomputable def halve : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
    let y := 4 * halve n
    (√2)⁻¹ * y

example (n : ℕ) : ∃ c : ℝ, 0 < c ∧ halve n = c * 4 ^ n := by
  induction n with | zero => ?_ | succ n ih => ?_
  · exact ⟨1, one_pos, by simp [halve]⟩
  · obtain ⟨c, hc, hx⟩ := ih
    refine ⟨(√2)⁻¹ * c, mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))) hc, ?_⟩
    simp only [halve, hx]
    ring

/-! ### W3. A dot product with an eigenvector: R3, R4, R6 -/
example {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (u w : ι → ℝ) (μ : ℝ)
    (hu : A *ᵥ u = μ • u) (h : w ⬝ᵥ (A *ᵥ u) = 6) (hw : w ⬝ᵥ u = 2) : μ = 3 := by
  rw [hu, dotProduct_smul, hw, smul_eq_mul] at h
  linarith

end H063Guide
