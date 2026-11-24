/- Guide for H077 (Robertson's uncertainty relation).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`ι` is any finite index type (`[Fintype ι]`), vectors are `v w x y : ι → ℂ`, matrices `M N : Matrix ι ι ℂ`.
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Matrix

namespace H077Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · moving a Hermitian matrix across `⬝ᵥ` -/

/-! ### R1. `Matrix.star_mulVec` · goal: `star (M *ᵥ v)` → `star v ᵥ* Mᴴ` -/
example {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (v : ι → ℂ) (P : (ι → ℂ) → Prop)
    (h : P (star v ᵥ* Mᴴ)) : P (star (M *ᵥ v)) := by
  rw [Matrix.star_mulVec]
  exact h

/-! ### R2. `hM.eq` (lemma `Matrix.IsHermitian.eq`) · goal: `Mᴴ` → `M` -/
example {ι : Type} (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (P : Matrix ι ι ℂ → Prop)
    (h : P M) : P Mᴴ := by
  rw [hM.eq]
  exact h

/-! ### R3. `Matrix.dotProduct_mulVec` · goal: `v ⬝ᵥ (M *ᵥ w)` → `(v ᵥ* M) ⬝ᵥ w` -/
example {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) (v w : ι → ℂ) (P : ℂ → Prop)
    (h : P (v ᵥ* M ⬝ᵥ w)) : P (v ⬝ᵥ (M *ᵥ w)) := by
  rw [Matrix.dotProduct_mulVec]
  exact h

/-! ## Part 2 · expanding products of matrices and scalars -/

/-! ### R4. `sub_mul` · `(a - b) * c = a * c - b * c` · goal -/
example {α : Type} [Ring α] (a b c : α) (P : α → Prop) (h : P (a * c - b * c)) :
    P ((a - b) * c) := by
  rw [sub_mul]
  exact h

/-! ### R5. `mul_sub` · `a * (b - c) = a * b - a * c` · goal -/
example {α : Type} [Ring α] (a b c : α) (P : α → Prop) (h : P (a * b - a * c)) :
    P (a * (b - c)) := by
  rw [mul_sub]
  exact h

/-! ### R6. `smul_mul_assoc` · `(s • M) * N = s • (M * N)` · goal -/
example {ι : Type} [Fintype ι] (s : ℂ) (M N : Matrix ι ι ℂ) (P : Matrix ι ι ℂ → Prop)
    (h : P (s • (M * N))) : P (s • M * N) := by
  rw [smul_mul_assoc]
  exact h

/-! ### R7. `mul_smul_comm` · `M * (s • N) = s • (M * N)` · goal -/
example {ι : Type} [Fintype ι] (s : ℂ) (M N : Matrix ι ι ℂ) (P : Matrix ι ι ℂ → Prop)
    (h : P (s • (M * N))) : P (M * s • N) := by
  rw [mul_smul_comm]
  exact h

/-! ### R8. `one_mul`, `mul_one` · `1 * M = M`, `M * 1 = M` · goal -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (M N : Matrix ι ι ℂ)
    (P : Matrix ι ι ℂ → Matrix ι ι ℂ → Prop) (h : P M N) : P (1 * M) (N * 1) := by
  rw [one_mul, mul_one]
  exact h

/-! ### R9. `smul_sub` · `s • (M - N) = s • M - s • N` · goal -/
example {ι : Type} (s : ℂ) (M N : Matrix ι ι ℂ) (P : Matrix ι ι ℂ → Prop)
    (h : P (s • M - s • N)) : P (s • (M - N)) := by
  rw [smul_sub]
  exact h

/-! ### R10. `smul_smul` · `s • t • M = (s * t) • M` · goal -/
example {ι : Type} (s t : ℂ) (M : Matrix ι ι ℂ) (P : Matrix ι ι ℂ → Prop)
    (h : P ((s * t) • M)) : P (s • t • M) := by
  rw [smul_smul]
  exact h

/-! ### R11. `mul_comm t s` · `t * s = s * t`, only for these two arguments · goal -/
example (s t : ℂ) (P : ℂ → Prop) (h : P (s * t)) : P (t * s) := by
  rw [mul_comm t s]
  exact h

/-! ### R12. `abel` · closes an equation that holds in every commutative additive group -/
example {ι : Type} (M N K : Matrix ι ι ℂ) : M - (N - K) - (M - N) = K := by
  abel

/-! ## Part 3 · expectation values are real; the shifted matrix; the variance -/

/-! ### R13. `apply Complex.conj_eq_iff_re.mp` · goal `↑z.re = z` → `conj z = z` -/
example (z : ℂ) (hz : starRingEnd ℂ z = z) : (z.re : ℂ) = z := by
  apply Complex.conj_eq_iff_re.mp
  exact hz

/-! ### R14. `unfold d at h ⊢` · goal and hypothesis `h`: the name `d` → its body -/
def cube (z : ℂ) : ℂ := z * z * z
example (z : ℂ) (P Q : ℂ → Prop) (hz : P (cube z)) (h : P (z * z * z) → Q (z * z * z)) :
    Q (cube z) := by
  unfold cube at hz ⊢
  exact h hz

/-! ### R15. `simp only [dotProduct]` · goal: `v ⬝ᵥ w` → `∑ i, v i * w i` -/
example {ι : Type} [Fintype ι] (v w : ι → ℂ) (P : ℂ → Prop) (h : P (∑ i, v i * w i)) :
    P (v ⬝ᵥ w) := by
  simp only [dotProduct]
  exact h

/-! ### R16. `simp` pushes `conj` (`starRingEnd ℂ`) into a sum and a product · goal -/
example {ι : Type} [Fintype ι] (f g : ι → ℂ) (P : ℂ → Prop)
    (h : P (∑ i, starRingEnd ℂ (f i) * starRingEnd ℂ (g i))) :
    P (starRingEnd ℂ (∑ i, f i * g i)) := by
  simp
  exact h

/-! ### R17. `rw [show a = b by tac]` · goal: rewrite with an equation proved on the spot -/
example (a b : ℂ) (P : ℂ → Prop) (h : P (b * a)) : P (a * b) := by
  rw [show a * b = b * a by ring]
  exact h

/-! ### R18. `Matrix.IsHermitian.sub` · `M.IsHermitian → N.IsHermitian → (M - N).IsHermitian` -/
example {ι : Type} (M N : Matrix ι ι ℂ) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    (M - N).IsHermitian := by
  apply hM.sub
  exact hN

/-! ### R19. `unfold Matrix.IsHermitian` · goal: `M.IsHermitian` → `Mᴴ = M` -/
example {ι : Type} (M : Matrix ι ι ℂ) (h : Mᴴ = M) : M.IsHermitian := by
  unfold Matrix.IsHermitian
  exact h

/-! ### R20. `Matrix.conjTranspose_smul` · goal: `(c • M)ᴴ` → `star c • Mᴴ` -/
example {ι : Type} (c : ℂ) (M : Matrix ι ι ℂ) (P : Matrix ι ι ℂ → Prop) (h : P (star c • Mᴴ)) :
    P ((c • M)ᴴ) := by
  rw [Matrix.conjTranspose_smul]
  exact h

/-! ### R21. `simp` closes `star ↑r • 1ᴴ = ↑r • 1` for a real `r`
(`Matrix.conjTranspose_one`: `1ᴴ = 1`; `Complex.conj_ofReal`: `conj ↑r = ↑r`). -/
example {ι : Type} [DecidableEq ι] (r : ℝ) :
    star (r : ℂ) • (1 : Matrix ι ι ℂ)ᴴ = (r : ℂ) • 1 := by
  rw [Matrix.conjTranspose_one]
  simp

/-! ### R22. `Matrix.mulVec_mulVec` · goal: `M *ᵥ (N *ᵥ v)` → `(M * N) *ᵥ v`; `←` splits it -/
example {ι : Type} [Fintype ι] (M N : Matrix ι ι ℂ) (v : ι → ℂ) (P : (ι → ℂ) → Prop)
    (h : P ((M * N) *ᵥ v)) : P (M *ᵥ (N *ᵥ v)) := by
  rw [Matrix.mulVec_mulVec]
  exact h

/-! ### R23. `Matrix.sub_mulVec` · goal: `(M - N) *ᵥ v` → `M *ᵥ v - N *ᵥ v` -/
example {ι : Type} [Fintype ι] (M N : Matrix ι ι ℂ) (v : ι → ℂ) (P : (ι → ℂ) → Prop)
    (h : P (M *ᵥ v - N *ᵥ v)) : P ((M - N) *ᵥ v) := by
  rw [Matrix.sub_mulVec]
  exact h

/-! ### R24. `Matrix.smul_mulVec` · goal: `(c • M) *ᵥ v` → `c • (M *ᵥ v)` -/
example {ι : Type} [Fintype ι] (c : ℂ) (M : Matrix ι ι ℂ) (v : ι → ℂ) (P : (ι → ℂ) → Prop)
    (h : P (c • (M *ᵥ v))) : P ((c • M) *ᵥ v) := by
  rw [Matrix.smul_mulVec]
  exact h

/-! ### R25. `Matrix.one_mulVec` · goal: `1 *ᵥ v` → `v` -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) (P : (ι → ℂ) → Prop) (h : P v) :
    P (1 *ᵥ v) := by
  rw [Matrix.one_mulVec]
  exact h

/-! ### R26. `dotProduct_sub` · goal: `u ⬝ᵥ (v - w)` → `u ⬝ᵥ v - u ⬝ᵥ w` -/
example {ι : Type} [Fintype ι] (u v w : ι → ℂ) (P : ℂ → Prop) (h : P (u ⬝ᵥ v - u ⬝ᵥ w)) :
    P (u ⬝ᵥ (v - w)) := by
  rw [dotProduct_sub]
  exact h

/-! ### R27. `dotProduct_smul` · goal: `v ⬝ᵥ (c • w)` → `c • (v ⬝ᵥ w)` -/
example {ι : Type} [Fintype ι] (c : ℂ) (v w : ι → ℂ) (P : ℂ → Prop) (h : P (c • (v ⬝ᵥ w))) :
    P (v ⬝ᵥ (c • w)) := by
  rw [dotProduct_smul]
  exact h

/-! ### R28. `Complex.ofReal_re` · goal: `(↑r).re` → `r` (real part of a real number cast to `ℂ`) -/
example (r : ℝ) (P : ℝ → Prop) (h : P r) : P (r : ℂ).re := by
  rw [Complex.ofReal_re]
  exact h

/-! ### R29. `simp [sq]` · closes real-part arithmetic: `sq` turns `a ^ 2` into `a * a`, then
`Complex.sub_re`, `Complex.mul_re`, `Complex.ofReal_re`, `Complex.ofReal_im`, `smul_eq_mul` fire. -/
example (r : ℝ) (z : ℂ) : (z - (r : ℂ) ^ 2).re = (z - (r : ℂ) • (r : ℂ)).re := by
  simp [sq]

/-! ## Part 4 · Cauchy–Schwarz through `EuclideanSpace` -/

/-! ### R30. `have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x) (WithLp.toLp 2 y)`
· context gains Cauchy–Schwarz `‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖` for the wrapped vectors -/
example {ι : Type} [Fintype ι] (x y : ι → ℂ) (G : Prop) (g : G) : G := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x : EuclideanSpace ℂ ι) (WithLp.toLp 2 y)
  exact g

/-! ### R31. `EuclideanSpace.inner_eq_star_dotProduct` · `inner ℂ x y = y.ofLp ⬝ᵥ star x.ofLp` -/
example {ι : Type} [Fintype ι] (x y : ι → ℂ) (P : ℂ → Prop)
    (h : P ((WithLp.toLp 2 y).ofLp ⬝ᵥ star (WithLp.toLp 2 x).ofLp)) :
    P (inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι) (WithLp.toLp 2 y)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  exact h

/-! ### R32. `simp only at h` · hypothesis: `(WithLp.toLp 2 x).ofLp` → `x` (wrap then unwrap) -/
example {ι : Type} [Fintype ι] (x y : ι → ℂ) (P : ℂ → Prop)
    (h : P ((WithLp.toLp 2 y).ofLp ⬝ᵥ star (WithLp.toLp 2 x).ofLp)) : P (y ⬝ᵥ star x) := by
  simp only at h
  exact h

/-! ### R33. `dotProduct_comm` · goal: `v ⬝ᵥ w` → `w ⬝ᵥ v` -/
example {ι : Type} [Fintype ι] (v w : ι → ℂ) (P : ℂ → Prop) (h : P (w ⬝ᵥ v)) : P (v ⬝ᵥ w) := by
  rw [dotProduct_comm]
  exact h

/-! ### R34. `@norm_sq_eq_re_inner ℂ` · goal: `‖x‖ ^ 2` → `RCLike.re (inner ℂ x x)`
`RCLike.re` is the real part on `ℝ` or `ℂ`; `simp` turns it into `.re`. -/
example {ι : Type} [Fintype ι] (x : ι → ℂ) (P : ℝ → Prop)
    (h : P (RCLike.re (inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ ι) (WithLp.toLp 2 x)))) :
    P (‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ^ 2) := by
  rw [@norm_sq_eq_re_inner ℂ]
  exact h

/-! ### R35. `calc` · goal `a ≤ c` → one goal per step `a ≤ b`, `b = c` -/
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b = c) : a ≤ c := by
  calc a ≤ b := h₁
    _ = c := h₂

/-! ### R36. `pow_le_pow_left₀ ha hab n` · `0 ≤ a → a ≤ b → a ^ n ≤ b ^ n`
`norm_nonneg x : 0 ≤ ‖x‖` supplies `ha` when `a` is a norm. -/
example (z : ℂ) (b : ℝ) (hab : ‖z‖ ≤ b) : ‖z‖ ^ 2 ≤ b ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg z) hab 2
  exact h

/-! ### R37. `mul_pow` · goal: `(a * b) ^ n` → `a ^ n * b ^ n` -/
example (a b : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (a ^ n * b ^ n)) : P ((a * b) ^ n) := by
  rw [mul_pow]
  exact h

/-! ## Part 5 · `‖z − conj z‖² ≤ 4‖z‖²` and the final inequality -/

/-! ### R38. `Complex.sq_norm` · goal: `‖z‖ ^ 2` → `Complex.normSq z` -/
example (z : ℂ) (P : ℝ → Prop) (h : P (Complex.normSq z)) : P (‖z‖ ^ 2) := by
  rw [Complex.sq_norm]
  exact h

/-! ### R39. `Complex.normSq_apply` · goal: `normSq z` → `z.re * z.re + z.im * z.im` -/
example (z : ℂ) (P : ℝ → Prop) (h : P (z.re * z.re + z.im * z.im)) : P (Complex.normSq z) := by
  rw [Complex.normSq_apply]
  exact h

/-! ### R40. `simp` · goal: real and imaginary parts of `z - conj z`
(`Complex.sub_re`, `Complex.sub_im`, `Complex.conj_re : (conj z).re = z.re`,
`Complex.conj_im : (conj z).im = -z.im`). -/
example (z : ℂ) (P : ℝ → ℝ → Prop) (h : P 0 (z.im + z.im)) :
    P (z - starRingEnd ℂ z).re (z - starRingEnd ℂ z).im := by
  simp
  exact h

/-! ### R41. `nlinarith [t₁, …]` · closes a polynomial inequality, using the hints `tᵢ` (and the
context) multiplied in pairs; `sq_nonneg a : 0 ≤ a ^ 2` is the usual hint -/
example (a b : ℝ) : (b + b) * (b + b) ≤ 4 * (a * a + b * b) := by
  nlinarith [sq_nonneg a]

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A single shift drops out of a commutator: R4–R8 in one `simp only`, then R12 -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (M N : Matrix ι ι ℂ) (s : ℂ) :
    (M - s • 1) * N - N * (M - s • 1) = M * N - N * M := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  abel

/-! ### W2. The real-part twin of Part 5: `‖z + conj z‖² ≤ 4‖z‖²` (R38, R39, `simp`, R41) -/
example (z : ℂ) : ‖z + starRingEnd ℂ z‖ ^ 2 ≤ 4 * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp
  nlinarith [sq_nonneg z.im]

/-! ### W3. Square both sides of a bound and split the square of a product (R35, R36, R37) -/
example (a b c : ℝ) (ha : 0 ≤ a) (h : a ≤ b * c) : a ^ 2 ≤ b ^ 2 * c ^ 2 := by
  calc a ^ 2 ≤ (b * c) ^ 2 := pow_le_pow_left₀ ha h 2
    _ = b ^ 2 * c ^ 2 := by rw [mul_pow]

/-! ### W4. A real number times the identity is Hermitian (R19, R20, R21) -/
example {ι : Type} [DecidableEq ι] (r : ℝ) : ((r : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul]
  simp

end H077Guide
