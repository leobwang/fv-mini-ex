/- Guide for M101 (Two independent dice).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` (or `Q`) stands for "the rest of your goal": the step changes only the part shown inside `P (…)`.
A hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (fair coins instead of dice).
Assumed: Lean basics.
-/
import Mathlib

open MeasureTheory ProbabilityTheory

namespace M101Guide

/-! # Part R · Reference entries -/

/-! ## Independence of coordinates under a product measure -/

/-! ### R1. `iIndepFun_pi` · goal: mutual independence of the coordinates → measurability of each `X i`
Under `Measure.pi μ` (coordinate `i` has law `μ i`, all `μ i` probability measures) the maps
`ω ↦ X i (ω i)` are mutually independent. -/
example {ι Ω 𝓧 : Type} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace 𝓧] (μ : ι → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] (X : ι → Ω → 𝓧) (h : ∀ i, AEMeasurable (X i) (μ i)) :
    iIndepFun (fun i ω => X i (ω i)) (Measure.pi μ) := by
  apply iIndepFun_pi
  exact h

/-! ### R2. `Measurable.aemeasurable` · goal: `AEMeasurable f μ` → `Measurable f` -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (h : Measurable fun x : Ω => x) :
    AEMeasurable (fun x : Ω => x) μ := by
  apply Measurable.aemeasurable
  exact h

/-! ### R3. `measurable_id` · closes `Measurable id` (also `Measurable fun x => x`) -/
example {Ω : Type} [MeasurableSpace Ω] : Measurable fun x : Ω => x := by
  exact measurable_id

/-! ### R4. `iIndepFun.indepFun` · goal: `f i ⟂ᵢ[μ] f j` → `i ≠ j`, given `hf : iIndepFun f μ` -/
example {ι Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] (μ : Measure Ω) (f : ι → Ω → β)
    (hf : iIndepFun f μ) (i j : ι) (hij : i ≠ j) : f i ⟂ᵢ[μ] f j := by
  apply hf.indepFun
  exact hij

/-! ## Turning an event into a finite set of outcomes -/

/-! ### R5. `ext x` on sets (lemma `Set.ext`) · goal `s = t` → context gains `x`, goal `x ∈ s ↔ x ∈ t` -/
example {α : Type} (s t : Set α) (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  ext x
  exact h x

/-! ### R6. `Set.mem_setOf_eq` · goal: `x ∈ {y | p y}` → `p x` -/
example {α : Type} (p : α → Prop) (x : α) (Q : Prop → Prop) (h : Q (p x)) :
    Q (x ∈ {y | p y}) := by
  rw [Set.mem_setOf_eq]
  exact h

/-! ### R7. `Finset.coe_filter`, then `Finset.mem_univ`, `true_and` · goal: membership in a coerced
filter → the predicate. `Finset.univ.filter p` prints as `{x | p x}` too (a `Finset`, not a `Set`);
`↑` casts it to a `Set`. -/
example {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] (x : α) (Q : Prop → Prop)
    (h : Q (p x)) : Q (x ∈ (↑(Finset.univ.filter p) : Set α)) := by
  rw [Finset.coe_filter]
  rw [Set.mem_setOf_eq]
  simp only [Finset.mem_univ, true_and]
  exact h

/-! ## The mass of one outcome -/

/-! ### R8. `PMF.toMeasure_apply_singleton` · goal: the measure of `{a}` → the PMF's value at `a`,
plus side goal `MeasurableSet {a}` (closed by `measurableSet_singleton a`). -/
example {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α) (a : α)
    (P : ENNReal → Prop) (h : P (p a)) : P (p.toMeasure {a}) := by
  rw [PMF.toMeasure_apply_singleton p a]
  exact h
  exact measurableSet_singleton a

/-! ### R9. `PMF.uniformOfFintype_apply` · goal: the uniform PMF at `a` → `(card α)⁻¹` -/
example {α : Type} [Fintype α] [Nonempty α] (a : α) (P : ENNReal → Prop)
    (h : P (Fintype.card α : ENNReal)⁻¹) : P (PMF.uniformOfFintype α a) := by
  rw [PMF.uniformOfFintype_apply]
  exact h

/-! ### R10. `decide` on a count · closes `(Finset.univ.filter p).card = n` over a finite type
It enumerates every outcome, here all 9 maps `Fin 2 → Fin 3`. -/
example : (Finset.univ.filter fun ω : Fin 2 → Fin 3 => ω 0 = ω 1).card = 3 := by
  decide

/-! ## From `μ.real` of a finite set to a number -/

/-! ### R11. `measureReal_def` · goal: `μ.real s` → `(μ s).toReal` -/
example {α : Type} [MeasurableSpace α] (μ : Measure α) (s : Set α) (P : ℝ → Prop)
    (h : P (μ s).toReal) : P (μ.real s) := by
  rw [measureReal_def]
  exact h

/-! ### R12. `sum_measure_singleton` · `∑ x ∈ s, μ {x} = μ ↑s`; right to left: `rw [← …]` -/
example {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α) (s : Finset α)
    (P : ENNReal → Prop) (h : P (∑ x ∈ s, μ {x})) : P (μ ↑s) := by
  rw [← sum_measure_singleton]
  exact h

/-! ### R13. `Measure.pi_singleton` · goal: product measure of a point → product of the factors -/
example {ι α : Type} [Fintype ι] [MeasurableSpace α] (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)]
    (f : ι → α) (P : ENNReal → Prop) (h : P (∏ i, μ i {f i})) : P (Measure.pi μ {f}) := by
  rw [Measure.pi_singleton]
  exact h

/-! ### R14. `Finset.prod_const` · goal: product of a constant → a power -/
example {ι M : Type} [CommMonoid M] (s : Finset ι) (b : M) (P : M → Prop) (h : P (b ^ s.card)) :
    P (∏ _x ∈ s, b) := by
  rw [Finset.prod_const]
  exact h

/-! ### R15. `Finset.card_univ`, then `Fintype.card_fin` · goal: `univ.card` → `Fintype.card (Fin n)` → `n` -/
example (n : ℕ) (P : ℕ → Prop) (h : P n) : P (Finset.univ : Finset (Fin n)).card := by
  rw [Finset.card_univ]
  rw [Fintype.card_fin]
  exact h

/-! ### R16. `Finset.sum_const` · goal: sum of a constant → `card • constant` -/
example {ι M : Type} [AddCommMonoid M] (s : Finset ι) (b : M) (P : M → Prop) (h : P (s.card • b)) :
    P (∑ _x ∈ s, b) := by
  rw [Finset.sum_const]
  exact h

/-! ## `ENNReal.toReal`: from `[0, ∞]` to `ℝ` -/

/-! ### R17. `ENNReal.toReal_nsmul` · goal: `toReal` moves inside `n • _` -/
example (n : ℕ) (a : ENNReal) (P : ℝ → Prop) (h : P (n • a.toReal)) : P (n • a).toReal := by
  rw [ENNReal.toReal_nsmul]
  exact h

/-! ### R18. `ENNReal.toReal_pow` · goal: `toReal` moves inside `_ ^ n` -/
example (n : ℕ) (a : ENNReal) (P : ℝ → Prop) (h : P (a.toReal ^ n)) : P (a ^ n).toReal := by
  rw [ENNReal.toReal_pow]
  exact h

/-! ### R19. `ENNReal.toReal_inv` · goal: `toReal` moves inside `_⁻¹` (true also at `0` and `∞`) -/
example (a : ENNReal) (P : ℝ → Prop) (h : P a.toReal⁻¹) : P (a⁻¹).toReal := by
  rw [ENNReal.toReal_inv]
  exact h

/-! ### R20. `ENNReal.toReal_ofNat` · goal: `toReal` of a numeral `≥ 2` → the real numeral -/
example (P : ℝ → Prop) (h : P 5) : P (5 : ENNReal).toReal := by
  rw [ENNReal.toReal_ofNat]
  exact h

/-! ### R21. `nsmul_eq_mul` · goal: `n • a` (repeated addition) → `↑n * a` -/
example (n : ℕ) (a : ℝ) (P : ℝ → Prop) (h : P (↑n * a)) : P (n • a) := by
  rw [nsmul_eq_mul]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-- a fair coin, and three independent tosses -/
noncomputable abbrev coin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
noncomputable abbrev threeCoins : Measure (Fin 3 → Bool) := Measure.pi fun _ => coin

/-! ### W1. Tosses 0 and 2 are independent: R1 (with `X i = id`), R2 + R3, then R4 and `decide` -/
example : (fun ω : Fin 3 → Bool => ω 0) ⟂ᵢ[threeCoins] (fun ω => ω 2) :=
  (iIndepFun_pi (μ := fun _ : Fin 3 => coin) (X := fun _ (b : Bool) => b)
    (fun _ => measurable_id.aemeasurable)).indepFun (by decide)

/-! The same with tactics: build the family's fact first (R1–R3), then R4. `apply iIndepFun.indepFun`
straight on the goal fails: Lean cannot guess the family `f` from `fun ω => ω 0`. -/
example : (fun ω : Fin 3 → Bool => ω 0) ⟂ᵢ[threeCoins] (fun ω => ω 2) := by
  have hf := iIndepFun_pi (μ := fun _ : Fin 3 => coin) (X := fun _ (b : Bool) => b)
    (fun _ => measurable_id.aemeasurable)
  apply hf.indepFun
  decide

/-! ### W2. One face: `simp [coin]` does R8 and R9 by itself and evaluates `card Bool` -/
example (b : Bool) : coin {b} = 2⁻¹ := by
  simp [coin]

/-! ### W3. The counting chain on three coins: "toss 0 equals toss 1" has probability 1/2 -/
example : threeCoins.real {ω | ω 0 = ω 1} = 1 / 2 := by
  have hs : {ω : Fin 3 → Bool | ω 0 = ω 1} = ↑(Finset.univ.filter fun ω : Fin 3 → Bool => ω 0 = ω 1) := by
    ext ω; simp
  have hcoin : ∀ b : Bool, coin {b} = 2⁻¹ := by
    intro b; simp [coin]
  have hcard : (Finset.univ.filter fun ω : Fin 3 → Bool => ω 0 = ω 1).card = 4 := by
    decide
  rw [measureReal_def, hs, ← sum_measure_singleton]
  simp only [threeCoins, Measure.pi_singleton, hcoin, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, hcard]
  rw [ENNReal.toReal_nsmul]
  simp [ENNReal.toReal_inv]
  norm_num

end M101Guide
