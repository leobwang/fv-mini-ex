/- Guide for H081 (Tsirelson's bound).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other vectors, `√3`, a 2-term
operator instead of the CHSH operator).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Matrix

namespace H081Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · Cauchy–Schwarz through `EuclideanSpace` -/

/-! ### R1. `WithLp.toLp 2 x : EuclideanSpace ℂ n` · a term: the function `x` as a vector of ℓ²
`EuclideanSpace ℂ n` is `n → ℂ` with the inner product `⟪u, v⟫ = ∑ i, conj (u i) * v i` and the
norm `‖u‖ = √(∑ i, ‖u i‖²)`. `WithLp.toLp 2` moves a plain function into it; `.ofLp` moves back. -/
example {n : Type} [Fintype n] (x : n → ℂ) (P : EuclideanSpace ℂ n → Prop) (h : ∀ v, P v) :
    P (WithLp.toLp 2 x) := by
  exact h (WithLp.toLp 2 x)

/-! ### R2. `have h := norm_inner_le_norm (𝕜 := ℂ) u v` · context gains Cauchy–Schwarz
`norm_inner_le_norm : ‖inner 𝕜 u v‖ ≤ ‖u‖ * ‖v‖`. `inner ℂ u v` is the inner product `⟪u, v⟫`
(conjugate-linear in `u`). Name `𝕜 := ℂ`: the scalar field cannot be read off `u v`. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (u v : E) (G : Prop)
    (k : ‖inner ℂ u v‖ ≤ ‖u‖ * ‖v‖ → G) : G := by
  have h := norm_inner_le_norm (𝕜 := ℂ) u v
  exact k h

/-! ### R3. `EuclideanSpace.inner_eq_star_dotProduct` · goal: `inner ℂ x y` → `y.ofLp ⬝ᵥ star x.ofLp`
The arguments come out swapped: the conjugate sits on the RIGHT. -/
example {n : Type} [Fintype n] (x y : EuclideanSpace ℂ n) (P : ℂ → Prop)
    (h : P (y.ofLp ⬝ᵥ star x.ofLp)) : P (inner ℂ x y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  exact h

/-! ### R4. `WithLp.ofLp_toLp` · goal: `(WithLp.toLp 2 x).ofLp` → `x` (`simp` applies it by itself) -/
example {n : Type} (x : n → ℂ) (P : (n → ℂ) → Prop) (h : P x) : P (WithLp.toLp 2 x).ofLp := by
  rw [WithLp.ofLp_toLp]
  exact h

/-! ### R5. `dotProduct_comm` · goal: `v ⬝ᵥ w` → `w ⬝ᵥ v` -/
example {n : Type} [Fintype n] (v w : n → ℂ) (P : ℂ → Prop) (h : P (w ⬝ᵥ v)) : P (v ⬝ᵥ w) := by
  rw [dotProduct_comm]
  exact h

/-! ### R6. `norm_sq_eq_re_inner (𝕜 := ℂ)` · goal: `‖u‖ ^ 2` → `RCLike.re (inner ℂ u u)`
`RCLike.re` is the real part on `ℝ` or `ℂ`; on `ℂ`, `simp` turns it into `Complex.re`, printed `z.re`.
Without `(𝕜 := ℂ)` (or `@norm_sq_eq_re_inner ℂ`) `rw` cannot find the field and fails. -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (u : E) (P : ℝ → Prop)
    (h : P (RCLike.re (inner ℂ u u))) : P (‖u‖ ^ 2) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact h

/-! ### R7. `rw [e] at h` · context: hypothesis `h` rewritten, goal unchanged -/
example {α : Type} (a b : α) (P : α → Prop) (G : Prop) (e : a = b) (h : P a) (k : P b → G) : G := by
  rw [e] at h
  exact k h

/-! ### R8. `calc` · goal `a ≤ c` → one goal per step (`a ≤ b`, `b = c`), each closed after `:=` -/
example {α : Type} [Preorder α] (a b c : α) (h₁ : a ≤ b) (h₂ : b = c) : a ≤ c := by
  calc a ≤ b := h₁
    _ = c := h₂

/-! ### R9. `pow_le_pow_left₀` · `0 ≤ a → a ≤ b → ∀ m, a ^ m ≤ b ^ m` · goal list: two side goals -/
example (a b : ℝ) (m : ℕ) (ha : 0 ≤ a) (hab : a ≤ b) : a ^ m ≤ b ^ m := by
  apply pow_le_pow_left₀
  exact ha
  exact hab

/-! ### R10. `norm_nonneg` · `0 ≤ ‖u‖` for any norm -/
example {E : Type} [NormedAddCommGroup E] (u : E) : 0 ≤ ‖u‖ := by
  exact norm_nonneg u

/-! ### R11. `mul_pow` · goal: `(a * b) ^ m` → `a ^ m * b ^ m` -/
example {α : Type} [CommMonoid α] (a b : α) (m : ℕ) (P : α → Prop) (h : P (a ^ m * b ^ m)) :
    P ((a * b) ^ m) := by
  rw [mul_pow]
  exact h

/-! ## Part 2 · Matrix–vector algebra and isometries -/

/-! ### R12. `Matrix.star_mulVec` · goal: `star (M *ᵥ v)` → `star v ᵥ* Mᴴ`
`M *ᵥ v` is the column vector `M v`; `v ᵥ* M` is the row vector `vᵀ M`; `Mᴴ` the conjugate transpose. -/
example {n : Type} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) (P : (n → ℂ) → Prop)
    (h : P (star v ᵥ* Mᴴ)) : P (star (M *ᵥ v)) := by
  rw [Matrix.star_mulVec]
  exact h

/-! ### R13. `Matrix.dotProduct_mulVec` · goal: `v ⬝ᵥ A *ᵥ w` → `v ᵥ* A ⬝ᵥ w` (move `A` to the left)
Lean prints `v ⬝ᵥ (A *ᵥ w)` as `v ⬝ᵥ A *ᵥ w` and `(v ᵥ* A) ⬝ᵥ w` as `v ᵥ* A ⬝ᵥ w`. -/
example {n : Type} [Fintype n] (v w : n → ℂ) (A : Matrix n n ℂ) (P : ℂ → Prop)
    (h : P (v ᵥ* A ⬝ᵥ w)) : P (v ⬝ᵥ A *ᵥ w) := by
  rw [Matrix.dotProduct_mulVec]
  exact h

/-! ### R14. `Matrix.vecMul_vecMul` · goal: `v ᵥ* M ᵥ* N` → `v ᵥ* (M * N)` -/
example {n : Type} [Fintype n] (v : n → ℂ) (M N : Matrix n n ℂ) (P : (n → ℂ) → Prop)
    (h : P (v ᵥ* (M * N))) : P (v ᵥ* M ᵥ* N) := by
  rw [Matrix.vecMul_vecMul]
  exact h

/-! ### R15. `Matrix.vecMul_one` · goal: `v ᵥ* 1` → `v` (`1` is the identity matrix) -/
example {n : Type} [Fintype n] [DecidableEq n] (v : n → ℂ) (P : (n → ℂ) → Prop) (h : P v) :
    P (v ᵥ* 1) := by
  rw [Matrix.vecMul_one]
  exact h

/-! ### R16. `Complex.one_re`, then `one_mul` · goal: `Complex.re 1` → `1`, then `1 * r` → `r` -/
example (r : ℝ) (P : ℝ → Prop) (h : P r) : P ((1 : ℂ).re * r) := by
  rw [Complex.one_re]
  rw [one_mul]
  exact h

/-! ### R17. `nlinarith [t₁, …]` · closes a polynomial inequality over `ℝ` from the hypotheses and
the extra facts `tᵢ`, by multiplying pairs of them. Here: `a² ≤ 1` and `0 ≤ a` give `a ≤ 1`. -/
example (a : ℝ) (h : a ^ 2 ≤ 1) (ha : 0 ≤ a) : a ≤ 1 := by
  nlinarith [ha]

/-! ## Part 3 · Expanding a product of non-commuting matrices -/

/-! ### R18. A `∀`-helper: `have sw : ∀ {a b : R}, … := by intro a b h x; …` · context gains `sw`
`R` is any ring; `Matrix n n ℂ` is one (non-commutative). Braces `{a b}` make `a b` implicit: write
`sw hab` and Lean reads `a b` off `hab : a * b = b * a`. `intro a b h x` names the binders. -/
example {R : Type} [Ring R] (G : Prop)
    (k : (∀ {a b : R}, a * b = b * a → ∀ x, b * (a * x) = a * (b * x)) → G) : G := by
  have sw : ∀ {a b : R}, a * b = b * a → ∀ x, b * (a * x) = a * (b * x) := by
    intro a b h x
    rw [← mul_assoc, ← h, mul_assoc]
  exact k sw

/-! ### R19. `rw [← mul_assoc]` · goal: `a * (b * c)` → `a * b * c` (`*` groups to the left)
`rw [← mul_assoc b]` fixes the first factor `b`: it regroups only a product `b * (_ * _)`. -/
example {R : Type} [Ring R] (a b c : R) (P : R → Prop) (h : P (a * b * c)) : P (a * (b * c)) := by
  rw [← mul_assoc]
  exact h

/-! ### R20. `simp only [add_mul, mul_add, sub_mul, mul_sub]` · goal: products distributed over `+`, `-`
`ring` cannot do this for matrices: it needs a commutative `*`. -/
example {R : Type} [Ring R] (a b c d : R) (P : R → Prop)
    (h : P (a * c + b * c - (a * d + b * d) - (a * c - b * c + (a * d - b * d)))) :
    P ((a + b) * (c - d) - (a - b) * (c + d)) := by
  simp only [add_mul, mul_add, sub_mul, mul_sub]
  exact h

/-! ### R21. `simp only [mul_assoc]` · goal: every product re-associated to the right -/
example {R : Type} [Ring R] (a b c d : R) (P : R → Prop) (h : P (a * (b * (c * d)))) :
    P (a * b * c * d) := by
  simp only [mul_assoc]
  exact h

/-! ### R22. `simp only [sw hab, sq1 ha]` · goal: rewrite with instantiated `∀`-helpers
`sw hab : ∀ x, b * (a * x) = a * (b * x)` moves `a` left past `b`;
`sq1 ha : ∀ x, a * (a * x) = x` cancels a square in front of any tail `x`. -/
example {R : Type} [Ring R] (a b c : R) (P : R → Prop)
    (sw : ∀ {a b : R}, a * b = b * a → ∀ x, b * (a * x) = a * (b * x))
    (sq1 : ∀ {a : R}, a * a = 1 → ∀ x, a * (a * x) = x)
    (hab : a * b = b * a) (ha : a * a = 1) (h : P (b * c)) : P (a * (b * (a * c))) := by
  simp only [sw hab, sq1 ha]
  exact h

/-! ### R23. `simp only [mul_one]` · goal: `a * 1` → `a` -/
example {R : Type} [Ring R] (a b : R) (P : R → Prop) (h : P (a * b)) : P (a * (b * 1)) := by
  simp only [mul_one]
  exact h

/-! ### R24. `rw [show (4 : R) = 1 + 1 + 1 + 1 by norm_num]` · goal: the numeral `4` → `1 + 1 + 1 + 1`
`show T by tac` is a term proving `T`; `rw` then uses it like a lemma. -/
example {R : Type} [Ring R] (P : R → Prop) (h : P (1 + 1 + 1 + 1)) : P 4 := by
  rw [show (4 : R) = 1 + 1 + 1 + 1 by norm_num]
  exact h

/-! ### R25. `abel` · closes an equation of sums/differences (an additive commutative group),
treating each product such as `a * (b * c)` as an opaque atom. It does not know `4 = 1 + 1 + 1 + 1`. -/
example {R : Type} [Ring R] (x y : R) : 1 + x - y + (1 + y) = 1 + 1 + x := by
  abel

/-! ## Part 4 · `⟨C⟩² ≤ ⟨C²⟩` for a Hermitian `C` -/

/-! ### R26. `Matrix.IsHermitian.eq` (`hA.eq`) · goal: `Aᴴ` → `A`
`A.IsHermitian` is by definition `Aᴴ = A`; `hA.eq` is that equation, usable in `rw`. -/
example {n : Type} (A : Matrix n n ℂ) (hA : A.IsHermitian) (P : Matrix n n ℂ → Prop) (h : P A) :
    P Aᴴ := by
  rw [hA.eq]
  exact h

/-! ### R27. `Matrix.mulVec_mulVec` · goal: `M *ᵥ N *ᵥ v` → `(M * N) *ᵥ v`
`M *ᵥ N *ᵥ v` is how Lean prints `M *ᵥ (N *ᵥ v)`. -/
example {n : Type} [Fintype n] (M N : Matrix n n ℂ) (v : n → ℂ) (P : (n → ℂ) → Prop)
    (h : P ((M * N) *ᵥ v)) : P (M *ᵥ N *ᵥ v) := by
  rw [Matrix.mulVec_mulVec]
  exact h

/-! ### R28. `have hre := Complex.abs_re_le_norm z` · context gains `|z.re| ≤ ‖z‖` -/
example (z : ℂ) (G : Prop) (k : |z.re| ≤ ‖z‖ → G) : G := by
  have hre := Complex.abs_re_le_norm z
  exact k hre

/-! ### R29. `sq_abs` · goal: `|a| ^ 2` → `a ^ 2`; with `abs_nonneg`, the hints `nlinarith` needs
to go from `|a| ≤ c` and `c ^ 2 ≤ b` to `a ^ 2 ≤ b`. -/
example (a : ℝ) (P : ℝ → Prop) (h : P (a ^ 2)) : P (|a| ^ 2) := by
  rw [sq_abs]
  exact h

/-! ## Part 5 · Assembling the bound -/

/-! ### R30. `set C := e with hC` · goal: every `e` → `C`; context gains `C := e` and `hC : C = e` -/
example {R : Type} [Ring R] (a b : R) (P : R → Prop) (k : ∀ y, P y) : P (a * b + b * a) := by
  set C := a * b + b * a with hC
  exact k C

/-! ### R31. `simp only [Matrix.IsHermitian]` · goal: `A.IsHermitian` → `Aᴴ = A` (unfold the definition) -/
example {n : Type} (A : Matrix n n ℂ) (h : Aᴴ = A) : A.IsHermitian := by
  simp only [Matrix.IsHermitian]
  exact h

/-! ### R32. `Matrix.conjTranspose_add`, `Matrix.conjTranspose_sub` · goal: `(M + N)ᴴ` → `Mᴴ + Nᴴ` -/
example {n : Type} (M N K : Matrix n n ℂ) (P : Matrix n n ℂ → Prop) (h : P (Mᴴ + Nᴴ - Kᴴ)) :
    P (M + N - K)ᴴ := by
  rw [Matrix.conjTranspose_sub]
  rw [Matrix.conjTranspose_add]
  exact h

/-! ### R33. `Matrix.conjTranspose_mul` · goal: `(M * N)ᴴ` → `Nᴴ * Mᴴ` (the order flips) -/
example {n : Type} [Fintype n] (M N : Matrix n n ℂ) (P : Matrix n n ℂ → Prop) (h : P (Nᴴ * Mᴴ)) :
    P (M * N)ᴴ := by
  rw [Matrix.conjTranspose_mul]
  exact h

/-! ### R34. `Matrix.sub_mulVec` · goal: `(A - B) *ᵥ x` → `A *ᵥ x - B *ᵥ x` -/
example {n : Type} [Fintype n] (A B : Matrix n n ℂ) (x : n → ℂ) (P : (n → ℂ) → Prop)
    (h : P (A *ᵥ x - B *ᵥ x)) : P ((A - B) *ᵥ x) := by
  rw [Matrix.sub_mulVec]
  exact h

/-! ### R35. `dotProduct_sub` · goal: `v ⬝ᵥ (x - y)` → `v ⬝ᵥ x - v ⬝ᵥ y` -/
example {n : Type} [Fintype n] (v x y : n → ℂ) (P : ℂ → Prop) (h : P (v ⬝ᵥ x - v ⬝ᵥ y)) :
    P (v ⬝ᵥ (x - y)) := by
  rw [dotProduct_sub]
  exact h

/-! ### R36. `Matrix.ofNat_mulVec`, `dotProduct_smul`, `smul_eq_mul` · goal: `⟨ψ| 4 |ψ⟩` → `4 * ⟨ψ|ψ⟩`
The numeral matrix `4` is `4 • 1`; `simp` applies these by itself (then `hψ` and `mul_one`). -/
example {n : Type} [Fintype n] [DecidableEq n] (ψ : n → ℂ) (P : ℂ → Prop)
    (h : P (4 * (star ψ ⬝ᵥ ψ))) : P (star ψ ⬝ᵥ (4 : Matrix n n ℂ) *ᵥ ψ) := by
  simp only [Matrix.ofNat_mulVec]
  simp only [dotProduct_smul]
  simp only [smul_eq_mul]
  exact h

/-! ### R37. `refine h.trans ?_` (`le_trans`) · goal `a ≤ c`, given `h : a ≤ b` → goal `b ≤ c` -/
example {α : Type} [Preorder α] (a b c : α) (h : a ≤ b) (k : b ≤ c) : a ≤ c := by
  refine h.trans ?_
  exact k

/-! ### R38. `Complex.sub_re`, `Complex.add_re` · goal: `(z - w).re` → `z.re - w.re` -/
example (z w u : ℂ) (P : ℝ → Prop) (h : P (z.re - (w.re + u.re))) : P (z - (w + u)).re := by
  simp only [Complex.sub_re, Complex.add_re]
  exact h

/-! ### R39. `norm_num` on `Complex.re 4` (lemma `Complex.re_ofNat`) · goal: `Complex.re 4` → `4` -/
example (P : ℝ → Prop) (h : P 4) : P (Complex.re 4) := by
  rw [Complex.re_ofNat]
  exact h

/-! ### R40. `rw [abs_le] at h` · context: `h : |a| ≤ b` → `h : -b ≤ a ∧ a ≤ b` -/
example (a b : ℝ) (G : Prop) (h : |a| ≤ b) (k : -b ≤ a ∧ a ≤ b → G) : G := by
  rw [abs_le] at h
  exact k h

/-! ### R41. `linarith` · closes a linear (in)equality over `ℝ` from hypotheses (it splits `∧`s) -/
example (a b : ℝ) (h₁ : -1 ≤ a ∧ a ≤ 1) (h₂ : -1 ≤ b ∧ b ≤ 1) : a - b ≤ 2 := by
  linarith

/-! ### R42. `Real.sq_sqrt`, `Real.sqrt_nonneg` · `0 ≤ x → √x ^ 2 = x` and `0 ≤ √x`: the facts that
let `nlinarith` turn `t ^ 2 ≤ 4 * x` into `t ≤ 2 * √x` -/
example (x : ℝ) (P : ℝ → Prop) (hx : 0 ≤ x) (h : P x) : P (√x ^ 2) := by
  rw [Real.sq_sqrt hx]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. R3, R4, R5 on a concrete pair: `⟪toLp v, toLp w⟫ = star v ⬝ᵥ w` -/
example (v w : Fin 3 → ℂ) :
    inner ℂ (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 3)) (WithLp.toLp 2 w) = star v ⬝ᵥ w := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp]
  rw [dotProduct_comm]

/-! ### W2. R6, R3, R4 for a norm: `‖toLp v‖ ^ 2` as a real part -/
example (v : Fin 3 → ℂ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 3))‖ ^ 2 = (v ⬝ᵥ star v).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [WithLp.ofLp_toLp]
  rfl

/-! ### W3. R12, R13, R14, R15: `Uᴴ U = 1` preserves the inner product of two vectors `v`, `w` -/
example {n : Type} [Fintype n] [DecidableEq n] (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) (v w : n → ℂ) :
    star (U *ᵥ v) ⬝ᵥ U *ᵥ w = star v ⬝ᵥ w := by
  rw [Matrix.star_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_vecMul]
  rw [hU]
  rw [Matrix.vecMul_one]

/-! ### W4. R18–R22, R25 on a smaller operator: `(ab + ba)(ab − ba) = 0` when `a² = b² = 1` and
`a b = b a` (`R` any ring, e.g. `Matrix n n ℂ`). Same pattern: distribute, re-associate to the right,
commute and cancel with the helpers, finish with `abel`. -/
example {R : Type} [Ring R] (a b : R) (sa : a * a = 1) (sb : b * b = 1) (hab : a * b = b * a) :
    (a * b + b * a) * (a * b - b * a) = 0 := by
  have sw : ∀ {a b : R}, a * b = b * a → ∀ x, b * (a * x) = a * (b * x) := by
    intro a b h x
    rw [← mul_assoc, ← h, mul_assoc]
  have sq1 : ∀ {c : R}, c * c = 1 → ∀ x, c * (c * x) = x := by
    intro c h x
    rw [← mul_assoc, h, one_mul]
  simp only [add_mul, mul_sub]
  simp only [mul_assoc]
  simp only [sw hab, sq1 sa, sq1 sb, sa, sb]
  abel

/-! ### W5. R37, R38, R39, R40, R41: a real part bounded through two unit-modulus terms -/
example (z w : ℂ) (hz : |z.re| ≤ 1) (hw : |w.re| ≤ 1) (t : ℝ) (ht : t ≤ (2 - (z - w)).re) :
    t ≤ 4 := by
  refine ht.trans ?_
  simp only [Complex.sub_re]
  norm_num
  rw [abs_le] at hz hw
  linarith

/-! ### W6. R42 with `nlinarith`: from `t ^ 2 ≤ 12` to `t ≤ 2 * √3` -/
example (t : ℝ) (h : t ^ 2 ≤ 12) : t ≤ 2 * Real.sqrt 3 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]

end H081Guide
