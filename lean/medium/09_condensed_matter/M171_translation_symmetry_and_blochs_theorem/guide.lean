/- Guide for M171 (Translation symmetry and Bloch's theorem).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (the identity `∑ n, |n⟩⟨n|`, an
arbitrary coefficient function `g`).
Assumed: Lean basics (E001–E033).
-/
import Physlib.CondensedMatter.TightBindingChain.Basic

open CondensedMatter TightBindingChain

namespace M171Guide

/-! # Part R · Reference entries -/

/-! ## A sum of operators applied to a basis vector (the helper `translation_apply`) -/

/-! ### R1. `LinearMap.sum_apply` · goal: `(∑ i, f i) x` → `∑ i, f i x` -/
example {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (f : ι → V →ₗ[ℂ] V) (x : V)
    (P : V → Prop) (h : P (∑ i, f i x)) : P ((∑ i, f i) x) := by
  rw [LinearMap.sum_apply]
  exact h

/-! ### R2. `localizedComp_apply_localizedState` · goal: `|m⟩⟨n| |p⟩` → `if n = p then |m⟩ else 0` -/
example (T : TightBindingChain) (m n p : Fin T.N) (P : T.HilbertSpace → Prop)
    (h : P (if n = p then localizedState m else 0)) : P (localizedComp m n (localizedState p)) := by
  rw [localizedComp_apply_localizedState]
  exact h

/-! ### R3. `Finset.sum_ite_eq'` · goal: a sum of `if x = a then b x else 0` → one `if` -/
example {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] (b : ι → V) (a : ι)
    (P : V → Prop) (h : P (if a ∈ Finset.univ then b a else 0)) :
    P (∑ x, if x = a then b x else 0) := by
  rw [Finset.sum_ite_eq']
  exact h

/-! ### R4. `Finset.mem_univ`, `if_true` · goal: `if a ∈ Finset.univ then x else y` → `x` -/
example {ι V : Type} [Fintype ι] [DecidableEq ι] (x y : V) (a : ι)
    (P : V → Prop) (h : P x) : P (if a ∈ Finset.univ then x else y) := by
  simp only [Finset.mem_univ, if_true]
  exact h

/-! ## Equality of linear maps, checked on a basis -/

/-! ### R5. `apply b.toBasis.ext` (lemma `Module.Basis.ext`) · goal `f = g` → `∀ i, f (b i) = g (b i)` -/
example {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : OrthonormalBasis ι ℂ E) (f g : E →ₗ[ℂ] E) (h : ∀ i, f (b.toBasis i) = g (b.toBasis i)) :
    f = g := by
  apply b.toBasis.ext
  exact h

/-! ### R6. `OrthonormalBasis.coe_toBasis` · goal: `b.toBasis i` → `b i` -/
example {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : OrthonormalBasis ι ℂ E) (i : ι) (P : E → Prop) (h : P (b i)) : P (b.toBasis i) := by
  rw [OrthonormalBasis.coe_toBasis]
  exact h

/-! ### R7. `LinearMap.comp_apply` · goal: `(f ∘ₗ g) x` → `f (g x)` -/
example {V : Type} [AddCommGroup V] [Module ℂ V] (f g : V →ₗ[ℂ] V) (x : V)
    (P : V → Prop) (h : P (f (g x))) : P ((f ∘ₗ g) x) := by
  rw [LinearMap.comp_apply]
  exact h

/-! ### R8. `hamiltonian_apply_localizedState` · goal: `H |n⟩` → `E0 • |n⟩ - t • (|n + 1⟩ + |n - 1⟩)` -/
example (T : TightBindingChain) (n : Fin T.N) (P : T.HilbertSpace → Prop)
    (h : P ((T.E0 : ℂ) • localizedState n -
      (T.t : ℂ) • (localizedState (n + 1) + localizedState (n - 1)))) :
    P (T.hamiltonian (localizedState n)) := by
  rw [hamiltonian_apply_localizedState]
  exact h

/-! ### R9. `map_sub` · goal: `f (x - y)` → `f x - f y` -/
example {V : Type} [AddCommGroup V] [Module ℂ V] (f : V →ₗ[ℂ] V) (x y : V)
    (P : V → Prop) (h : P (f x - f y)) : P (f (x - y)) := by
  rw [map_sub]
  exact h

/-! ### R10. `map_add` · goal: `f (x + y)` → `f x + f y` -/
example {V : Type} [AddCommGroup V] [Module ℂ V] (f : V →ₗ[ℂ] V) (x y : V)
    (P : V → Prop) (h : P (f x + f y)) : P (f (x + y)) := by
  rw [map_add]
  exact h

/-! ### R11. `map_smul` · goal: `f (c • x)` → `c • f x` -/
example {V : Type} [AddCommGroup V] [Module ℂ V] (f : V →ₗ[ℂ] V) (c : ℂ) (x : V)
    (P : V → Prop) (h : P (c • f x)) : P (f (c • x)) := by
  rw [map_smul]
  exact h

/-! ### R12. `add_sub_cancel_right` · goal: `a + b - b` → `a` (also in `Fin N`, where `+`, `-` wrap mod N) -/
example {G : Type} [AddGroup G] (a b : G) (P : G → Prop) (h : P a) : P (a + b - b) := by
  rw [add_sub_cancel_right]
  exact h

/-! ## Pushing an operator through a sum, then reindexing (Bloch) -/

/-! ### R13. Unfold `TightBindingChain.energyEigenstate` · goal: `ψ_k` → `∑ n, exp (i k n a) • |n⟩` -/
example (T : TightBindingChain) (k : T.QuantaWaveNumber) (P : T.HilbertSpace → Prop)
    (h : P (∑ n : Fin T.N, Complex.exp (Complex.I * k * n * T.a) • localizedState n)) :
    P (T.energyEigenstate k) := by
  rw [TightBindingChain.energyEigenstate]
  exact h

/-! ### R14. `map_sum` · goal: `f (∑ i, v i)` → `∑ i, f (v i)` -/
example {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (f : V →ₗ[ℂ] V) (v : ι → V)
    (P : V → Prop) (h : P (∑ i, f (v i))) : P (f (∑ i, v i)) := by
  rw [map_sum]
  exact h

/-! ### R15. `Finset.smul_sum` · goal: `r • ∑ i, v i` → `∑ i, r • v i` -/
example {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (r : ℂ) (v : ι → V)
    (P : V → Prop) (h : P (∑ i, r • v i)) : P (r • ∑ i, v i) := by
  rw [Finset.smul_sum]
  exact h

/-! ### R16. `smul_smul` · goal: `a • b • x` → `(a * b) • x` -/
example {V : Type} [AddCommGroup V] [Module ℂ V] (a b : ℂ) (x : V)
    (P : V → Prop) (h : P ((a * b) • x)) : P (a • b • x) := by
  rw [smul_smul]
  exact h

/-! ### R17. `rw [← (Equiv.subRight c).sum_comp]` · goal: `∑ i, g i` → `∑ i, g (i - c)` (reindex) -/
example {N : ℕ} [NeZero N] {V : Type} [AddCommGroup V] (g : Fin N → V) (c : Fin N)
    (P : V → Prop) (h : P (∑ i, g ((Equiv.subRight c) i))) : P (∑ i, g i) := by
  rw [← (Equiv.subRight c).sum_comp]
  exact h

/-! ### R18. `refine Finset.sum_congr rfl fun n _ => ?_` · goal `∑ f = ∑ g` → `f n = g n` -/
example {ι V : Type} [Fintype ι] [AddCommGroup V] (f g : ι → V) (h : ∀ n, f n = g n) :
    ∑ i, f i = ∑ i, g i := by
  refine Finset.sum_congr rfl fun n _ => ?_
  exact h n

/-! ### R19. `Equiv.subRight_apply` · goal: `(Equiv.subRight c) x` → `x - c` -/
example {G : Type} [AddGroup G] (c x : G) (P : G → Prop) (h : P (x - c)) :
    P ((Equiv.subRight c) x) := by
  rw [Equiv.subRight_apply]
  exact h

/-! ### R20. `sub_add_cancel` · goal: `a - b + b` → `a` -/
example {G : Type} [AddGroup G] (a b : G) (P : G → Prop) (h : P a) : P (a - b + b) := by
  rw [sub_add_cancel]
  exact h

/-! ### R21. `congr 1` · goal `c • v = d • v` → `c = d` (the equal vectors are closed by `rfl`) -/
example {V : Type} [AddCommGroup V] [Module ℂ V] (c d : ℂ) (v : V) (h : d = c) :
    c • v = d • v := by
  congr 1
  exact h.symm

/-! ### R22. `quantaWaveNumber_exp_sub_one` · goal: `exp (i k (n-1) a)` → `exp (i k n a) * exp (-i k a)` -/
example (T : TightBindingChain) (k : T.QuantaWaveNumber) (n : Fin T.N) (P : ℂ → Prop)
    (h : P (Complex.exp (Complex.I * k * n * T.a) * Complex.exp (-Complex.I * k * T.a))) :
    P (Complex.exp (Complex.I * k * (n - 1).val * T.a)) := by
  rw [quantaWaveNumber_exp_sub_one]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The identity `∑ n, |n⟩⟨n|` on a basis vector: R1, R2, R3, R4 -/
example (T : TightBindingChain) (p : Fin T.N) :
    (∑ n : Fin T.N, localizedComp n n) (localizedState p) = localizedState p := by
  rw [LinearMap.sum_apply]
  simp only [localizedComp_apply_localizedState]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]

/-! ### W2. Reindex `|n + 1⟩` back to `|n⟩` for any coefficients `g`: R17, R18, R19, R20 -/
example (T : TightBindingChain) (g : Fin T.N → ℂ) :
    ∑ n : Fin T.N, g n • localizedState (n + 1) = ∑ n : Fin T.N, g (n - 1) • localizedState n := by
  rw [← (Equiv.subRight (1 : Fin T.N)).sum_comp]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Equiv.subRight_apply, sub_add_cancel]

/-! ### W3. An operator identity checked on the basis: R5, R6, then W1's chain in one `simp only` -/
example {T : TightBindingChain} : (∑ n : Fin T.N, localizedComp n n) = LinearMap.id := by
  apply (localizedState (T := T)).toBasis.ext
  intro m
  rw [OrthonormalBasis.coe_toBasis, LinearMap.id_apply]
  simp only [LinearMap.sum_apply, localizedComp_apply_localizedState, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

end M171Guide
