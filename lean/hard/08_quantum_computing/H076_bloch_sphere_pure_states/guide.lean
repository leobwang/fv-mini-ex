/- Guide for H076 (The Bloch sphere: pure iff on the sphere).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (other kets, other numbers).
Assumed: Lean basics (E001–E033).
-/
import QuantumInfo.States.Mixed.MState

open scoped Matrix

namespace H076Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · Facts every qubit state satisfies (`herm_facts`) -/

/-! ### R1. `have hH := ρ.Hermitian` (`MState.Hermitian`) · context gains `hH : ρ.m.IsHermitian`
`MState d` is a density matrix on the basis `d` (here `d = Fin 2`, a qubit): positive semidefinite,
trace 1. `ρ.m : Matrix d d ℂ` is its plain matrix, so `ρ.m i j : ℂ` is an entry.
`A.IsHermitian` means `Aᴴ = A` (conjugate transpose). -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) (G : Prop)
    (k : ρ.m.IsHermitian → G) : G := by
  have hH := ρ.Hermitian
  exact k hH

/-! ### R2. `have htr := ρ.tr'` (`MState.tr'`) · context gains `htr : ρ.m.trace = 1` -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ : MState d) (G : Prop)
    (k : ρ.m.trace = 1 → G) : G := by
  have htr := ρ.tr'
  exact k htr

/-! ### R3. `rw [Matrix.trace_fin_two] at htr` · context: `A.trace` → `A 0 0 + A 1 1` in `htr` -/
example (A : Matrix (Fin 2) (Fin 2) ℂ) (htr : A.trace = 1) (G : Prop)
    (k : A 0 0 + A 1 1 = 1 → G) : G := by
  rw [Matrix.trace_fin_two] at htr
  exact k htr

/-! ### R4. `Matrix.IsHermitian.apply` · `hH.apply i j : star (A j i) = A i j` · context gains it
`star z` on `ℂ` is the complex conjugate. -/
example {n : Type} (A : Matrix n n ℂ) (hH : A.IsHermitian) (i j : n) (G : Prop)
    (k : star (A j i) = A i j → G) : G := by
  have e := hH.apply i j
  exact k e

/-! ### R5. `refine ⟨e.symm, ?_⟩` · goal list: first conjunct filled by a flipped equation
`e.symm : b = a` for `e : a = b` (`Eq.symm`). -/
example {α : Type} (a b : α) (Q : Prop) (e : a = b) (q : Q) : b = a ∧ Q := by
  refine ⟨e.symm, ?_⟩
  exact q

/-! ### R6. `have k := congrArg f e` · context gains `k : f a = f b` from `e : a = b` -/
example (z w : ℂ) (e : z = w) (G : Prop) (g : z.im = w.im → G) : G := by
  have k := congrArg Complex.im e
  exact g k

/-! ### R7. `simp at k` · context: `(star z).im` → `-z.im` (`Complex.star_def`, `Complex.conj_im`) -/
example (z : ℂ) (k : (star z).im = z.im) (G : Prop) (g : -z.im = z.im → G) : G := by
  simp at k
  exact g k

/-! ### R8. `linarith` · closes a linear (in)equality over `ℝ` that follows from hypotheses -/
example (x : ℝ) (k : -x = x) : x = 0 := by
  linarith

/-! ### R9. `simpa using k` · closes the goal: simplifies `k` and the goal, then matches them
`(z + w).re` → `z.re + w.re` and `(1 : ℂ).re` → `1` are `simp` lemmas. -/
example (z w : ℂ) (k : (z + w).re = (1 : ℂ).re) : z.re + w.re = 1 := by
  simpa using k

/-! ## Part 2 · The sphere as a determinant condition (`sphere_iff`) -/

/-! ### R10. `obtain ⟨-, -, hc⟩ := e` · context gains only the last part of `e : A ∧ B ∧ C`
A `-` in the pattern throws that part away. -/
example (A B C G : Prop) (e : A ∧ B ∧ C) (g : C → G) : G := by
  obtain ⟨-, -, hc⟩ := e
  exact g hc

/-! ### R11. `rw [Complex.normSq_apply]` · goal: `normSq z` → `z.re * z.re + z.im * z.im`
`Complex.normSq z = |z|²`, a real number. -/
example (z : ℂ) (P : ℝ → Prop) (h : P (z.re * z.re + z.im * z.im)) : P (Complex.normSq z) := by
  rw [Complex.normSq_apply]
  exact h

/-! ### R12. `simp only [f]` · goal: a defined name `f` → its body -/
def twice (x : ℝ) : ℝ := 2 * x
example (x : ℝ) (P : ℝ → Prop) (h : P (2 * x)) : P (twice x) := by
  simp only [twice]
  exact h

/-! ### R13. `constructor` on `A ↔ B` · goal list: `A → B` and `B → A` (cases `mp`, `mpr`) -/
example (A B : Prop) (f : A → B) (g : B → A) : A ↔ B := by
  constructor
  exacts [f, g]

/-! ### R14. `nlinarith` · closes polynomial (in)equalities: `linarith` plus products of hypotheses -/
example (a b : ℝ) (hs : a + b = 1) (h : (a - b) ^ 2 = 1) : a * b = 0 := by
  nlinarith

/-! ## Part 3 · Pure states lie on the sphere (`pure_on_sphere`) -/

/-! ### R15. `rw [e]` with `e : A ↔ B` · goal: the proposition `A` → `B` -/
example (A B : Prop) (e : A ↔ B) (h : B) : A := by
  rw [e]
  exact h

/-! ### R16. `MState.pure_apply` · goal: `(MState.pure ψ).m i j` → `ψ i * (starRingEnd ℂ) (ψ j)`
`Ket d` is a unit vector: `ψ i : ℂ` is its `i`-th amplitude. `MState.pure ψ = |ψ⟩⟨ψ|`.
`(starRingEnd ℂ) z` is how Lean prints `conj z`. -/
example {d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) (i j : d) (P : ℂ → Prop)
    (h : P (ψ i * (starRingEnd ℂ) (ψ j))) : P ((MState.pure ψ).m i j) := by
  rw [MState.pure_apply]
  exact h

/-! ### R17. `Complex.normSq_mul` · goal: `normSq (z * w)` → `normSq z * normSq w` -/
example (z w : ℂ) (P : ℝ → Prop) (h : P (Complex.normSq z * Complex.normSq w)) :
    P (Complex.normSq (z * w)) := by
  rw [Complex.normSq_mul]
  exact h

/-! ### R18. `Complex.normSq_conj` · goal: `normSq (conj z)` → `normSq z` -/
example (z : ℂ) (P : ℝ → Prop) (h : P (Complex.normSq z)) :
    P (Complex.normSq ((starRingEnd ℂ) z)) := by
  rw [Complex.normSq_conj]
  exact h

/-! ### R19. `Complex.mul_conj` · goal: `z * conj z` → `↑(normSq z)` (a real cast into `ℂ`) -/
example (z : ℂ) (P : ℂ → Prop) (h : P ↑(Complex.normSq z)) : P (z * (starRingEnd ℂ) z) := by
  rw [Complex.mul_conj]
  exact h

/-! ### R20. `Complex.ofReal_re` · goal: `(↑r).re` → `r` -/
example (r : ℝ) (P : ℝ → Prop) (h : P r) : P (r : ℂ).re := by
  rw [Complex.ofReal_re]
  exact h

/-! ## Part 4 · Building a ket (`exists_ket`) -/

/-! ### R21. `rcases ha.eq_or_lt with rfl | ha` · goal list: case `a = 0` (substituted) and case `0 < a`
`LE.le.eq_or_lt : a ≤ b → a = b ∨ a < b`. `rfl` replaces `a` by `0` everywhere. -/
example (a : ℝ) (P : ℝ → Prop) (ha : 0 ≤ a) (h0 : P 0) (hp : 0 < a → P a) : P a := by
  rcases ha.eq_or_lt with rfl | ha
  · exact h0
  · exact hp ha

/-! ### R22. `simp at hz` · context: `normSq z = 0 * b` → `z = 0`
`simp` uses `zero_mul` and `map_eq_zero` (`normSq z = 0 ↔ z = 0`). `simpa using hz` also closes `⊢ z = 0`. -/
example (z : ℂ) (b : ℝ) (hz : Complex.normSq z = 0 * b) (G : Prop) (g : z = 0 → G) : G := by
  simp at hz
  exact g hz

/-! ### R23. `Ket.basis i` with `simp [Ket.basis, Ket.apply]` · goal: amplitudes of `|i⟩` evaluated
`Ket.basis i` is the basis ket `|i⟩`: amplitude 1 at `i`, 0 elsewhere. `Ket.apply : ψ i = ψ.vec i`. -/
example (P : ℂ → Prop) (h : P 0) : P ((Ket.basis (1 : Fin 2)) 0) := by
  simp [Ket.basis, Ket.apply]
  exact h

/-! ### R24. `exact_mod_cast e` · closes a goal that is `e` up to casts `ℝ → ℂ` -/
example (x : ℝ) (e : x ≠ 0) : (x : ℂ) ≠ 0 := by
  exact_mod_cast e

/-! ### R25. `(Real.sqrt_pos.mpr hx).ne'` · context gains `√x ≠ 0` from `hx : 0 < x`
`Real.sqrt_pos : 0 < √x ↔ 0 < x`; `.mpr` uses it right to left; `h.ne' : b ≠ a` for `h : a < b`. -/
example (x : ℝ) (hx : 0 < x) (G : Prop) (g : √x ≠ 0 → G) : G := by
  have k := (Real.sqrt_pos.mpr hx).ne'
  exact g k

/-! ### R26. `Real.mul_self_sqrt` · `0 ≤ x → √x * √x = x`; with R24 the same fact in `ℂ` -/
example (x : ℝ) (hx : 0 ≤ x) (G : Prop) (g : (√x : ℂ) * (√x : ℂ) = x → G) : G := by
  have k : (√x : ℂ) * (√x : ℂ) = x := by exact_mod_cast Real.mul_self_sqrt hx
  exact g k

/-! ### R27. `refine ⟨![a, b], ?_⟩` for a `Ket (Fin 2)` · goal: the normalization of `![a, b]`
A ket is a structure: amplitudes `vec : d → ℂ` and a proof `∑ x, ‖vec x‖ ^ 2 = 1`.
`![a, b]` is the function `Fin 2 → ℂ` with `0 ↦ a`, `1 ↦ b`; `‖z‖` is the modulus `|z|`. -/
example (a b : ℂ) (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : Ket (Fin 2) := by
  refine ⟨![a, b], ?_⟩
  simpa using h

/-! ### R28. `let ψ : Ket (Fin 2) := ⟨v, proof⟩` · context gains `ψ` together with its value
`simp [ψ]` (or `simp only [ψ]`) later unfolds `ψ` to its value. -/
example (P : Ket (Fin 2) → Prop) (h : ∀ φ, P φ) : P (Ket.basis 0) := by
  let ψ : Ket (Fin 2) := Ket.basis 0
  exact h ψ

/-! ### R29. `Fin.sum_univ_two` · goal: a sum over `Fin 2` → two terms -/
example {β : Type} [AddCommMonoid β] (f : Fin 2 → β) (P : β → Prop) (h : P (f 0 + f 1)) :
    P (∑ i, f i) := by
  rw [Fin.sum_univ_two]
  exact h

/-! ### R30. `Matrix.cons_val_zero`, `Matrix.cons_val_one` · goal: `![a, b] 0` → `a`, `![a, b] 1` → `b` -/
example {α : Type} (a b : α) (P : α → α → Prop) (h : P a b) : P (![a, b] 0) (![a, b] 1) := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact h

/-! ### R31. `← Complex.normSq_eq_norm_sq` · goal: `‖z‖ ^ 2` → `normSq z`
The lemma is `normSq z = ‖z‖ ^ 2`; the kets' normalization is stated with `‖·‖ ^ 2`. -/
example (z : ℂ) (P : ℝ → Prop) (h : P (Complex.normSq z)) : P (‖z‖ ^ 2) := by
  rw [← Complex.normSq_eq_norm_sq]
  exact h

/-! ### R32. `Complex.normSq_div` · goal: `normSq (z / w)` → `normSq z / normSq w` -/
example (z w : ℂ) (P : ℝ → Prop) (h : P (Complex.normSq z / Complex.normSq w)) :
    P (Complex.normSq (z / w)) := by
  rw [Complex.normSq_div]
  exact h

/-! ### R33. `Complex.normSq_ofReal` · goal: `normSq ↑r` → `r * r` -/
example (r : ℝ) (P : ℝ → Prop) (h : P (r * r)) : P (Complex.normSq (r : ℂ)) := by
  rw [Complex.normSq_ofReal]
  exact h

/-! ### R34. `field_simp` · goal: denominators cleared, using `≠ 0` facts in the context
It looks for hypotheses `ha : a ≠ 0`, then cancels (`a * x / a` → `x`) or cross-multiplies. -/
example (a c x : ℝ) (ha : a ≠ 0) (h : c + x = 1) : c + a * x / a = 1 := by
  field_simp
  exact h

/-! ### R35. `map_div₀` · goal: `conj (z / w)` → `conj z / conj w` -/
example (z w : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) z / (starRingEnd ℂ) w)) :
    P ((starRingEnd ℂ) (z / w)) := by
  rw [map_div₀]
  exact h

/-! ### R36. `Complex.conj_conj` · goal: `conj (conj z)` → `z` -/
example (z : ℂ) (P : ℂ → Prop) (h : P z) : P ((starRingEnd ℂ) ((starRingEnd ℂ) z)) := by
  rw [Complex.conj_conj]
  exact h

/-! ### R37. `Complex.conj_ofReal` · goal: `conj ↑r` → `↑r` -/
example (r : ℝ) (P : ℂ → Prop) (h : P (r : ℂ)) : P ((starRingEnd ℂ) (r : ℂ)) := by
  rw [Complex.conj_ofReal]
  exact h

/-! ### R38. `div_mul_div_comm` · goal: `a / b * (c / d)` → `a * c / (b * d)` -/
example {α : Type} [DivisionCommMonoid α] (a b c d : α) (P : α → Prop) (h : P (a * c / (b * d))) :
    P (a / b * (c / d)) := by
  rw [div_mul_div_comm]
  exact h

/-! ### R39. `mul_comm a` · goal: `a * b` → `b * a`; naming `a` picks which product turns -/
example {α : Type} [CommMagma α] (a b c : α) (P : α → α → Prop) (h : P (b * a) (c * b)) :
    P (a * b) (c * b) := by
  rw [mul_comm a]
  exact h

/-! ### R40. `push_cast` · goal: casts pushed inward, `↑(x * y)` → `↑x * ↑y` -/
example (x y : ℝ) (P : ℂ → Prop) (h : P ((x : ℂ) * (y : ℂ))) : P ((x * y : ℝ) : ℂ) := by
  push_cast
  exact h

/-! ## Part 5 · The theorem (`bloch_sphere`) -/

/-! ### R41. `rintro ⟨x, rfl⟩` · goal `(∃ x, a = f x) → G`: context gains `x`, and `a` is replaced by `f x` -/
example {α : Type} (f : α → ℕ) (a : ℕ) (G : ℕ → Prop) (g : ∀ x, G (f x)) :
    (∃ x, a = f x) → G a := by
  rintro ⟨x, rfl⟩
  exact g x

/-! ### R42. `rw [e] at h` with `e : A ↔ B` · context: `h : A` → `h : B` -/
example (A B G : Prop) (e : A ↔ B) (h : A) (g : B → G) : G := by
  rw [e] at h
  exact g h

/-! ### R43. `nlinarith [Complex.normSq_nonneg z]` · closes the goal using an extra fact `0 ≤ normSq z` -/
example (a : ℝ) (z : ℂ) (h : Complex.normSq z = a * a * a) : 0 ≤ a * a * a := by
  nlinarith [Complex.normSq_nonneg z]

/-! ### R44. `simp only [Fin.forall_fin_two]` · goal: `∀ i j : Fin 2, P i j` → four conjunctions
`Fin.forall_fin_two : (∀ i : Fin 2, p i) ↔ p 0 ∧ p 1`. -/
example (P : Fin 2 → Fin 2 → Prop) (h : (P 0 0 ∧ P 0 1) ∧ P 1 0 ∧ P 1 1) : ∀ i j, P i j := by
  simp only [Fin.forall_fin_two]
  exact h

/-! ### R45. `apply Complex.ext` · goal `z = w` → real parts equal, imaginary parts equal -/
example (z : ℂ) (r : ℝ) (h1 : z.re = r) (h2 : z.im = 0) : z = (r : ℂ) := by
  apply Complex.ext
  · simpa using h1
  · simpa using h2

/-! ### R46. `map_mul` · goal: `conj (z * w)` → `conj z * conj w` (`simp` applies it by itself) -/
example (z w : ℂ) (P : ℂ → Prop) (h : P ((starRingEnd ℂ) z * (starRingEnd ℂ) w)) :
    P ((starRingEnd ℂ) (z * w)) := by
  rw [map_mul]
  exact h

/-! ### R47. `apply MState.ext_m` · goal `ρ₁ = ρ₂` → `ρ₁.m = ρ₂.m` (states are equal when matrices are) -/
example {d : Type} [Fintype d] [DecidableEq d] (ρ₁ ρ₂ : MState d) (h : ρ₁.m = ρ₂.m) : ρ₁ = ρ₂ := by
  apply MState.ext_m
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A concrete ket `(3/5, 4/5)`: R27, then R29 + R30, R31, `simp`, `norm_num` -/
example : ∃ ψ : Ket (Fin 2), ψ 1 = 4 / 5 := by
  refine ⟨⟨![3 / 5, 4 / 5], ?_⟩, rfl⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp
  norm_num

/-! ### W2. `normSq (w / √c) = normSq w / c` for `c > 0`: R32, R33, R26 -/
example (w : ℂ) (c : ℝ) (hc : 0 < c) :
    Complex.normSq (w / (√c : ℂ)) = Complex.normSq w / c := by
  rw [Complex.normSq_div, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt hc.le]

/-! ### W3. Conjugating a quotient by a real square root: R35, R36, R37 -/
example (w : ℂ) (c : ℝ) :
    (starRingEnd ℂ) ((starRingEnd ℂ) w / (√c : ℂ)) = w / (√c : ℂ) := by
  rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal]

/-! ### W4. Cancel a real square root in `ℂ`: the `≠ 0` fact over `ℂ`, then `field_simp`
(R24, R25, R34) -/
example (w : ℂ) (c : ℝ) (hc : 0 < c) : 3 * w / (√c : ℂ) * (√c : ℂ) = 3 * w := by
  have hs : (√c : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hc).ne'
  field_simp

end H076Guide
