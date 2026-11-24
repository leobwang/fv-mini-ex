/- Guide for H100 (The tight-binding spectrum is the band).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders, in the order the skeletons use them. Put the cursor before and after the step to see
the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`E` is any complex inner product space (`[NormedAddCommGroup E] [InnerProductSpace ℂ E]`);
`T.HilbertSpace` is one.
Part W: worked combinations on objects that are NOT the exercise's (other coefficients, another
finite set, a linear functional).
Assumed: Lean basics (E001–E033).
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain InnerProductSpace

namespace H100Guide

/-! # Part R · Reference entries -/

/-! ## `bloch_norm_sq`: expand `⟪ψ_k, ψ_k⟫` into a double sum, then collapse it -/

/-! ### R1. `simp only [TightBindingChain.energyEigenstate]` · goal: the Bloch state `ψ_k` → its
definition `∑ n, exp (I k n a) • |n⟩` (`|n⟩ = localizedState n`) -/
example (T : TightBindingChain) (k : T.QuantaWaveNumber) (P : T.HilbertSpace → Prop)
    (h : P (∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • localizedState n)) :
    P (T.energyEigenstate k) := by
  simp only [TightBindingChain.energyEigenstate]
  exact h

/-! ### R2. `sum_inner` · `⟪∑ i ∈ s, f i, x⟫_ℂ = ∑ i ∈ s, ⟪f i, x⟫_ℂ` · goal: a sum in the left
slot comes out -/
example {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Finset ι) (f : ι → E)
    (x : E) (P : ℂ → Prop) (h : P (∑ i ∈ s, ⟪f i, x⟫_ℂ)) : P ⟪∑ i ∈ s, f i, x⟫_ℂ := by
  rw [sum_inner]
  exact h

/-! ### R3. `inner_sum` · `⟪x, ∑ i ∈ s, f i⟫_ℂ = ∑ i ∈ s, ⟪x, f i⟫_ℂ` · goal: a sum in the right
slot comes out -/
example {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Finset ι) (f : ι → E)
    (x : E) (P : ℂ → Prop) (h : P (∑ i ∈ s, ⟪x, f i⟫_ℂ)) : P ⟪x, ∑ i ∈ s, f i⟫_ℂ := by
  rw [inner_sum]
  exact h

/-! ### R4. `inner_smul_left` · `⟪r • x, y⟫_ℂ = conj r * ⟪x, y⟫_ℂ` (conjugate-linear on the left;
`conj` prints as `(starRingEnd ℂ)`) · goal -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) (r : ℂ)
    (P : ℂ → Prop) (h : P ((starRingEnd ℂ) r * ⟪x, y⟫_ℂ)) : P ⟪r • x, y⟫_ℂ := by
  rw [inner_smul_left]
  exact h

/-! ### R5. `inner_smul_right` · `⟪x, r • y⟫_ℂ = r * ⟪x, y⟫_ℂ` (linear on the right) · goal -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) (r : ℂ)
    (P : ℂ → Prop) (h : P (r * ⟪x, y⟫_ℂ)) : P ⟪x, r • y⟫_ℂ := by
  rw [inner_smul_right]
  exact h

/-! ### R6. `localizedState_orthonormal_eq_ite` · `⟪|m⟩, |n⟩⟫_ℂ = if m = n then 1 else 0` (the site
states are orthonormal) · goal; written `⟨m|n⟩` by physlib's notation -/
example (T : TightBindingChain) (m n : Fin T.N) (P : ℂ → Prop) (h : P (if m = n then 1 else 0)) :
    P ⟪localizedState m, localizedState n⟫_ℂ := by
  rw [localizedState_orthonormal_eq_ite]
  exact h

/-! ### R7. `simp` collapses a Kronecker-delta sum (it uses `mul_ite`, `mul_one`, `mul_zero`,
`Finset.sum_ite_eq'`, `Finset.mem_univ`) · goal: `∑ m, f m * if m = j then 1 else 0` → `f j` -/
example (n : ℕ) (f : Fin n → ℂ) (j : Fin n) (P : ℂ → Prop) (h : P (f j)) :
    P (∑ m, f m * if m = j then 1 else 0) := by
  simp
  exact h

/-! ### R8. `Complex.exp_conj` · `Complex.exp (conj z) = conj (Complex.exp z)`; right to left
(`← Complex.exp_conj`) the conjugate moves inside the exponential · goal -/
example (z : ℂ) (P : ℂ → Prop) (h : P (Complex.exp ((starRingEnd ℂ) z))) :
    P ((starRingEnd ℂ) (Complex.exp z)) := by
  rw [← Complex.exp_conj]
  exact h

/-! ### R9. `Complex.conj_ofReal` · `conj ↑r = ↑r` for `r : ℝ` cast into `ℂ` · goal -/
example (r : ℝ) (P : ℂ → Prop) (h : P ↑r) : P ((starRingEnd ℂ) ↑r) := by
  rw [Complex.conj_ofReal]
  exact h

/-! ### R10. `map_mul`, `Complex.conj_I` · `conj (z * w) = conj z * conj w`, `conj I = -I` · goal;
`simp` applies both by itself -/
example (z : ℂ) (P : ℂ → Prop) (h : P (-Complex.I * (starRingEnd ℂ) z)) :
    P ((starRingEnd ℂ) (Complex.I * z)) := by
  rw [map_mul]
  rw [Complex.conj_I]
  exact h

/-! ### R11. `Complex.exp_add` · `Complex.exp (x + y) = Complex.exp x * Complex.exp y`; right to
left a product of exponentials becomes one · goal -/
example (x y : ℂ) (P : ℂ → Prop) (h : P (Complex.exp (x + y))) :
    P (Complex.exp x * Complex.exp y) := by
  rw [← Complex.exp_add]
  exact h

/-! ### R12. `add_neg_cancel`, `Complex.exp_zero` · `a + -a = 0`, `Complex.exp 0 = 1` · goal -/
example (z : ℂ) (P : ℂ → Prop) (h : P 1) : P (Complex.exp (z + -z)) := by
  rw [add_neg_cancel]
  rw [Complex.exp_zero]
  exact h

/-! ### R13. `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`, `nsmul_eq_mul` · goal:
a sum of `N` ones → `↑N` (`•` is repeated addition: `n • c = c + ⋯ + c`) -/
example (n : ℕ) (P : ℂ → Prop) (h : P ↑n) : P (∑ _i : Fin n, (1 : ℂ)) := by
  rw [Finset.sum_const]
  rw [Finset.card_univ]
  rw [Fintype.card_fin]
  rw [nsmul_eq_mul, mul_one]
  exact h

/-! ## `card_wavenumbers`: the allowed wavenumbers are the image of an injective map on `Fin N` -/

/-! ### R14. `ext x` (lemma `Set.ext`) · goal `s = t` between sets → context gains `x`, goal
`x ∈ s ↔ x ∈ t` -/
example {α : Type} (s t : Set α) (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  ext x
  exact h x

/-! ### R15. `simp only [TightBindingChain.QuantaWaveNumber]` · goal: `x ∈ T.QuantaWaveNumber` →
the set-builder definition `x ∈ {x | ∃ n, 2π/(a N) · (n − ⌊N/2⌋) = x}` -/
example (T : TightBindingChain) (x : ℝ) (P : Prop → Prop)
    (h : P (x ∈ {x | ∃ n : Fin T.N, 2 * Real.pi / (T.a * T.N) * ((n : ℝ) - (T.N / 2 : ℕ)) = x})) :
    P (x ∈ T.QuantaWaveNumber) := by
  simp only [TightBindingChain.QuantaWaveNumber]
  exact h

/-! ### R16. `Set.mem_setOf_eq`, `Set.mem_range` · `x ∈ {y | p y} ↔ p x`, `x ∈ Set.range f ↔ ∃ n, f n = x`
· `simp` closes a goal whose two sides unfold to the same `∃` -/
example {α β : Type} (f : α → β) (x : β) : x ∈ {y | ∃ n, f n = y} ↔ x ∈ Set.range f := by
  simp

/-! ### R17. `Set.ncard_range_of_injective` · `Function.Injective f → (Set.range f).ncard = Nat.card α`
· goal list: the goal is rewritten, plus the side goal `Function.Injective f` -/
example {α β : Type} (f : α → β) (P : ℕ → Prop) (h : P (Nat.card α)) (hf : Function.Injective f) :
    P (Set.range f).ncard := by
  rw [Set.ncard_range_of_injective]
  exact h
  exact hf

/-! ### R18. `Nat.card_eq_fintype_card` · `Nat.card α = Fintype.card α` when `[Fintype α]` · goal;
right to left (`← Nat.card_eq_fintype_card`) it goes back -/
example {α : Type} [Fintype α] (P : ℕ → Prop) (h : P (Fintype.card α)) : P (Nat.card α) := by
  rw [Nat.card_eq_fintype_card]
  exact h

/-! ### R19. `Fintype.card_fin` · `Fintype.card (Fin n) = n` · goal -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P (Fintype.card (Fin n)) := by
  rw [Fintype.card_fin]
  exact h

/-! ### R20. `intro m n h` on `Function.Injective f` · goal `Function.Injective f` (a `∀` in disguise:
`∀ a b, f a = f b → a = b`) → context gains `m n` and `h : f m = f n`, goal `m = n` -/
example {α β : Type} (f : α → β) (hf : ∀ a b, f a = f b → a = b) : Function.Injective f := by
  intro m n h
  exact hf m n h

/-! ### R21. `T.a_pos`, `NeZero.pos T.N` · context gains `0 < T.a` (a field of the structure) and
`0 < T.N` (`T.N` carries an instance `NeZero T.N`, i.e. `T.N ≠ 0`) -/
example (T : TightBindingChain) (G : Prop) (g : 0 < T.a → 0 < T.N → G) : G := by
  have ha := T.a_pos
  have hN := NeZero.pos T.N
  exact g ha hN

/-! ### R22. `exact_mod_cast` · closes a goal that is a hypothesis up to casts `↑` (`ℕ → ℝ`,
`ℕ → ℂ`, …): here `(0 : ℝ) < ↑n` from `0 < n` -/
example (n : ℕ) (h : 0 < n) : (0 : ℝ) < n := by
  exact_mod_cast h

/-! ### R23. `positivity` · closes `0 < e`, `0 ≤ e` or `e ≠ 0` when `e` is built by `*`, `/`, `^`, `+`
from numerals, `Real.pi` and atoms that have a `0 < x` hypothesis in the context -/
example (a x : ℝ) (ha : 0 < a) (hx : 0 < x) : 3 * Real.pi / (a * x ^ 2) ≠ 0 := by
  positivity

/-! ### R24. `mul_left_cancel₀` · `a ≠ 0 → a * b = a * c → b = c` · context gains the cancelled
equation -/
example (a b c : ℝ) (ha : a ≠ 0) (h : a * b = a * c) (G : Prop) (g : b = c → G) : G := by
  have h' := mul_left_cancel₀ ha h
  exact g h'

/-! ### R25. `sub_left_inj` · `b - a = c - a ↔ b = c` · context (`.mp`) -/
example (a b c : ℝ) (h : b - a = c - a) (G : Prop) (g : b = c → G) : G := by
  have h' := sub_left_inj.mp h
  exact g h'

/-! ### R26. `Fin.ext` · `(↑m : ℕ) = ↑n → m = n` · goal `m = n` between elements of `Fin N` → the
equation of their values in `ℕ` -/
example (N : ℕ) (m n : Fin N) (h : ((m : ℕ) : ℝ) = ((n : ℕ) : ℝ)) : m = n := by
  apply Fin.ext
  exact_mod_cast h

/-! ## `span_top`: `N` orthogonal nonzero vectors in an `N`-dimensional space span it -/

/-! ### R27. `Set.finite_of_ncard_pos` · `0 < s.ncard → s.Finite` (an infinite set has
`ncard = 0`) · context -/
example {α : Type} (s : Set α) (hs : 0 < s.ncard) (G : Prop) (g : s.Finite → G) : G := by
  have hfin := Set.finite_of_ncard_pos hs
  exact g hfin

/-! ### R28. `haveI : Fintype s := hfin.fintype` (`Set.Finite.fintype`) · context gains the
instance `Fintype ↑s`, so `Fintype.card ↑s` makes sense and lemmas with `[Fintype ι]` apply -/
example {α : Type} (s : Set α) (hfin : s.Finite) (P : ℕ → Prop) (h : ∀ [Fintype s], P (Fintype.card s)) :
    ∃ n, P n := by
  haveI : Fintype s := hfin.fintype
  exact ⟨_, h⟩

/-! ### R29. `apply LinearIndependent.span_eq_top_of_card_eq_finrank'` · goal list:
`Submodule.span ℂ (Set.range b) = ⊤` → `case lin_ind` (the family is linearly independent) and
`case card_eq` (it has `finrank` many members) -/
example {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (b : ι → E) (hli : LinearIndependent ℂ b)
    (hcard : Fintype.card ι = Module.finrank ℂ E) : Submodule.span ℂ (Set.range b) = ⊤ := by
  apply LinearIndependent.span_eq_top_of_card_eq_finrank'
  · exact hli
  · exact hcard

/-! ### R30. `apply linearIndependent_of_ne_zero_of_inner_eq_zero _ hpair` · goal
`LinearIndependent ℂ v` → `∀ i, v i ≠ 0`, given `hpair : Pairwise fun i j => ⟪v i, v j⟫_ℂ = 0`
(nonzero and pairwise orthogonal ⇒ independent) -/
example {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : ι → E)
    (hpair : Pairwise fun i j => ⟪v i, v j⟫_ℂ = 0) (hv : ∀ i, v i ≠ 0) : LinearIndependent ℂ v := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero _ hpair
  exact hv

/-! ### R31. `TightBindingChain.energyEigenstate_orthogonal` · the fact
`Pairwise fun k₁ k₂ => ⟪ψ_k₁, ψ_k₂⟫_ℂ = 0` (Bloch states with different `k` are orthogonal;
`Pairwise r` means `∀ i j, i ≠ j → r i j`) · closes a goal of that form -/
example (T : TightBindingChain) :
    Pairwise fun k₁ k₂ => ⟪T.energyEigenstate k₁, T.energyEigenstate k₂⟫_ℂ = 0 := by
  exact T.energyEigenstate_orthogonal

/-! ### R32. `intro hk` on `a ≠ b` · `a ≠ b` is `a = b → False`: context gains `hk : a = b`, goal
`False` -/
example {α : Type} (a b : α) (g : a = b → False) : a ≠ b := by
  intro hk
  exact g hk

/-! ### R33. `inner_zero_left` · `⟪0, x⟫_ℂ = 0` · goal (in the exercise `at h`, after `rw [hk]`
with `hk : v = 0` has put the `0` there) -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) (P : ℂ → Prop)
    (h : P 0) : P ⟪0, x⟫_ℂ := by
  rw [inner_zero_left]
  exact h

/-! ### R34. `NeZero.ne n` · `n ≠ 0` from the instance `[NeZero n]`; cast it into `ℂ` with R22 ·
context -/
example (T : TightBindingChain) (G : Prop) (g : (T.N : ℂ) ≠ 0 → G) : G := by
  have hN : (T.N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne T.N
  exact g hN

/-! ### R35. `hne h` (also `hne h.symm`) · `hne : a ≠ b` applied to `h : a = b` closes `False`;
`h.symm : b = a` flips an equation -/
example (a b : ℂ) (hne : a ≠ b) (h : b = a) : False := by
  exact hne h.symm

/-! ### R36. `localizedState (T := T)` · the site basis `|n⟩` as an `OrthonormalBasis (Fin T.N) ℂ
T.HilbertSpace`; `.toBasis` forgets orthonormality and gives a `Module.Basis` · context. Write
`(T := T)`: `T` is implicit in `localizedState` and nothing else determines it -/
example (T : TightBindingChain) (G : Prop) (g : Module.Basis (Fin T.N) ℂ T.HilbertSpace → G) : G := by
  have b := (localizedState (T := T)).toBasis
  exact g b

/-! ### R37. `Module.finrank_eq_card_basis b` · `Module.finrank ℂ E = Fintype.card ι` for a basis
`b : Module.Basis ι ℂ E` (dimension = number of basis vectors) · goal -/
example {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : Module.Basis ι ℂ E) (P : ℕ → Prop) (h : P (Fintype.card ι)) :
    P (Module.finrank ℂ E) := by
  rw [Module.finrank_eq_card_basis b]
  exact h

/-! ### R38. `Nat.card_coe_set_eq` · `Nat.card ↑s = s.ncard` (the number of elements of the
subtype `↑s` is the `ncard` of the set) · goal -/
example {α : Type} (s : Set α) (P : ℕ → Prop) (h : P s.ncard) : P (Nat.card s) := by
  rw [Nat.card_coe_set_eq]
  exact h

/-! ## `orth_of_ne`: eigenvectors of a Hermitian operator for different eigenvalues are orthogonal -/

/-! ### R39. `T.hamiltonian_hermitian ψ φ` · the fact `⟪H ψ, φ⟫_ℂ = ⟪ψ, H φ⟫_ℂ` (`H` is
Hermitian) · closes a goal of that form; in the exercise `have h := T.hamiltonian_hermitian ψ_k ψ` -/
example (T : TightBindingChain) (ψ φ : T.HilbertSpace) :
    ⟪T.hamiltonian ψ, φ⟫_ℂ = ⟪ψ, T.hamiltonian φ⟫_ℂ := by
  exact T.hamiltonian_hermitian ψ φ

/-! ### R40. `hamiltonian_energyEigenstate` · `H ψ_k = E(k) • ψ_k` with the REAL scalar
`E(k) = T.energyEigenvalue k : ℝ` · goal (or `at h`) -/
example (T : TightBindingChain) (k : T.QuantaWaveNumber) (P : T.HilbertSpace → Prop)
    (h : P (T.energyEigenvalue k • T.energyEigenstate k)) :
    P (T.hamiltonian (T.energyEigenstate k)) := by
  rw [hamiltonian_energyEigenstate]
  exact h

/-! ### R41. `show r • v = (r : ℂ) • v from rfl` · goal: a real scalar `r • v` → the complex scalar
`↑r • v`, so R4 and R5 (stated for `ℂ` scalars) apply. It is `rfl` because `ℝ` acts on
`T.HilbertSpace` through `ℂ` (`rw [← Complex.coe_smul]` does the same) -/
example (T : TightBindingChain) (r : ℝ) (v : T.HilbertSpace) (P : T.HilbertSpace → Prop)
    (h : P ((r : ℂ) • v)) : P (r • v) := by
  rw [show r • v = (r : ℂ) • v from rfl]
  exact h

/-! ### R42. `sub_mul` · `(a - b) * c = a * c - b * c` · goal -/
example (a b c : ℂ) (P : ℂ → Prop) (h : P (a * c - b * c)) : P ((a - b) * c) := by
  rw [sub_mul]
  exact h

/-! ### R43. `sub_self` · `a - a = 0` · goal -/
example (a : ℂ) (P : ℂ → Prop) (h : P 0) : P (a - a) := by
  rw [sub_self]
  exact h

/-! ### R44. `mul_eq_zero` · `a * b = 0 ↔ a = 0 ∨ b = 0` (`ℂ` has no zero divisors) · context (`.mp`) -/
example (a b : ℂ) (h : a * b = 0) (G : Prop) (g : a = 0 ∨ b = 0 → G) : G := by
  have h' := mul_eq_zero.mp h
  exact g h'

/-! ### R45. `Or.resolve_left` · `A ∨ B → ¬A → B` · closes the goal `B` -/
example (A B : Prop) (h : A ∨ B) (hA : ¬A) : B := by
  exact h.resolve_left hA

/-! ### R46. `sub_ne_zero` · `a - b ≠ 0 ↔ a ≠ b` · goal (as a term: `sub_ne_zero.mpr hab`) -/
example (a b : ℂ) (h : a ≠ b) : a - b ≠ 0 := by
  rw [sub_ne_zero]
  exact h

/-! ## `spectrum_eq_band`: contradiction, span induction, `⟪ψ, ψ⟫ = 0` -/

/-! ### R47. `by_contra hne` · goal `G` → context gains `hne : ¬G`, goal `False` -/
example (G : Prop) (h : ¬¬G) : G := by
  by_contra hne
  exact h hne

/-! ### R48. `push Not` · goal (or `at hne`: context): the negation is pushed inside,
`¬ ∃ k, a = f k` → `∀ k, a ≠ f k` -/
example {ι : Type} (a : ℂ) (f : ι → ℂ) (h : ∀ k, a ≠ f k) : ¬ ∃ k, a = f k := by
  push Not
  exact h

/-! ### R49. `induction hx using Submodule.span_induction` · goal `p x` with
`hx : x ∈ Submodule.span ℂ s` → four goals: `mem` (`p` on generators `x ∈ s`), `zero` (`p 0`),
`add` (`p x → p y → p (x + y)`), `smul` (`p x → p (c • x)`). Name the variables with
`… with | mem x hx => … | zero => … | add x y _ _ hx hy => … | smul c x _ hx => …`;
without `with` they are inaccessible (`x✝`) and `case mem y hy => …` names them -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Set E) (p : E → Prop)
    (hs : ∀ y ∈ s, p y) (h0 : p 0) (hadd : ∀ y z, p y → p z → p (y + z))
    (hsmul : ∀ (c : ℂ) y, p y → p (c • y)) (x : E) (hx : x ∈ Submodule.span ℂ s) : p x := by
  induction hx using Submodule.span_induction
  case mem y hy => exact hs y hy
  case zero => exact h0
  case add y z _ _ hy hz => exact hadd y z hy hz
  case smul c y _ hy => exact hsmul c y hy

/-! ### R50. `obtain ⟨k, rfl⟩ := hx` with `hx : x ∈ Set.range f` · context: `hx` and `x` disappear,
every `x` becomes `f k` (`x ∈ Set.range f` unfolds to `∃ k, f k = x`) -/
example {ι E : Type} (f : ι → E) (x : E) (hx : x ∈ Set.range f) (P : E → Prop)
    (h : ∀ k, P (f k)) : P x := by
  obtain ⟨k, rfl⟩ := hx
  exact h k

/-! ### R51. `inner_add_left` · `⟪x + y, z⟫_ℂ = ⟪x, z⟫_ℂ + ⟪y, z⟫_ℂ` · goal -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y z : E) (P : ℂ → Prop)
    (h : P (⟪x, z⟫_ℂ + ⟪y, z⟫_ℂ)) : P ⟪x + y, z⟫_ℂ := by
  rw [inner_add_left]
  exact h

/-! ### R52. `add_zero`, `mul_zero` · `a + 0 = a`, `a * 0 = 0` · goal; after `rw [hx, hy]` puts
the zeros in, `rw` closes `0 + 0 = 0`-style goals by `rfl` -/
example (a c : ℂ) : a * 0 + c * 0 = 0 := by
  rw [mul_zero, mul_zero, add_zero]

/-! ### R53. `trivial` (lemma `Submodule.mem_top`) · closes `x ∈ ⊤`: every vector lies in the
whole space `⊤` -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) :
    x ∈ (⊤ : Submodule ℂ E) := by
  trivial

/-! ### R54. `inner_self_eq_zero` · `⟪x, x⟫_ℂ = 0 ↔ x = 0` (positive definiteness) · goal; as a
term, `inner_self_eq_zero.mp h : x = 0` -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) (h : x = 0) :
    ⟪x, x⟫_ℂ = 0 := by
  rw [inner_self_eq_zero]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Expand an inner product against a site state with arbitrary coefficients `c n`:
R2, R4, R6, then R7 -/
example (T : TightBindingChain) (c : Fin T.N → ℂ) (m : Fin T.N) :
    ⟪∑ n, c n • localizedState n, localizedState m⟫_ℂ = (starRingEnd ℂ) (c m) := by
  simp only [sum_inner, inner_smul_left, localizedState_orthonormal_eq_ite]
  simp

/-! ### W2. Count the image of an injective map on `Fin 5`: R17, R18, R19, then R20, R24, R26 -/
example : (Set.range fun n : Fin 5 => (3 : ℝ) * n).ncard = 5 := by
  rw [Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  intro m n h
  exact Fin.ext (by exact_mod_cast mul_left_cancel₀ (by norm_num : (3 : ℝ) ≠ 0) h)

/-! ### W3. A linear functional `f` that vanishes on `s` vanishes on `Submodule.span ℂ s`: R49 with
`with`. (`map_add`, `map_smul`, `map_zero`, applied by `simp`, say `f` is linear.) -/
example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Set E) (f : E →ₗ[ℂ] ℂ)
    (hf : ∀ x ∈ s, f x = 0) : ∀ x ∈ Submodule.span ℂ s, f x = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
    | mem y hy => exact hf y hy
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]

end H100Guide
