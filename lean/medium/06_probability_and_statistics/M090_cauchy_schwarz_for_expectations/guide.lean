/- Guide for M090 (Cauchy–Schwarz for expectations).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Placeholders: `Ω` is a type with a σ-algebra (`[MeasurableSpace Ω]`), `μ : Measure Ω` a measure on
it, `f g : Ω → ℝ` real functions on `Ω` (random variables when `μ` is a probability measure).
Part W: worked combinations on objects that are NOT the exercise's.
Assumed: Lean basics.
-/
import Mathlib

open MeasureTheory
open ProbabilityTheory

namespace M090Guide

/-! # Part R · Reference entries -/

/-! ## The milestone `∀ t, 0 ≤ …` -/

/-! ### R1. `intro t` · goal `∀ t, P t` → context gains `t`, goal `P t` -/
example (P : ℝ → Prop) (h : ∀ s, P s) : ∀ t : ℝ, P t := by
  intro t
  exact h t

/-! ## Nonnegativity of an integral -/

/-! ### R2. `integral_nonneg` · `0 ≤ f → 0 ≤ ∫ ω, f ω ∂μ` · goal: integral → pointwise
`0 ≤ f` is the pointwise order on functions: it unfolds to `∀ ω, 0 ω ≤ f ω`, and `0 ω` is `0`. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ ∫ ω, f ω ∂μ := by
  apply integral_nonneg
  intro ω
  exact hf ω

/-! ### R3. `sq_nonneg` · `0 ≤ a ^ 2` · closes the goal -/
example (a : ℝ) : 0 ≤ a ^ 2 := by
  exact sq_nonneg a

/-! ## Rewriting the integrand -/

/-! ### R4. `funext ω` · goal: equation of functions → context gains `ω`, goal one value -/
example {Ω : Type} (f g : Ω → ℝ) (h : ∀ ω, f ω = g ω) : (fun ω => 2 * f ω) = fun ω => 2 * g ω := by
  funext ω
  rw [h ω]

/-! ### R5. `rw [e] at h` · context: `h` rewritten with a function equation `e`
`μ[F]` (notation, `open ProbabilityTheory`) is `∫ x, F x ∂μ`; the infoview prints it with the
unreduced `(fun ω => …) x`. After `rw`, Lean beta-reduces: the integrand is written out. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (P : ℝ → Prop)
    (e : (fun ω => f ω * g ω) = fun ω => g ω * f ω) (h : P (μ[fun ω => f ω * g ω])) :
    P (∫ ω, g ω * f ω ∂μ) := by
  rw [e] at h
  exact h

/-! ## Integrability facts -/

/-! ### R6. `Integrable.const_mul` · `Integrable f μ → ∀ c, Integrable (fun x => c * f x) μ`
Used with dot notation: `hf.const_mul c`. Closes the goal. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (c : ℝ) (hf : Integrable f μ) :
    Integrable (fun ω => c * f ω) μ := by
  exact hf.const_mul c

/-! ### R7. `Integrable.add` · `Integrable f μ → Integrable g μ → Integrable (f + g) μ`
`f + g` is the pointwise sum; Lean accepts it for `fun ω => f ω + g ω`. Closes the goal. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (fun ω => f ω + g ω) μ := by
  exact hf.add hg

/-! ## Splitting an integral -/

/-! ### R8. `integral_add hf hg` · `∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ` · goal
The same rewrite works on a hypothesis: `rw [integral_add hf hg] at h` (R5). -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) (P : ℝ → Prop) (h : P (∫ ω, f ω ∂μ + ∫ ω, g ω ∂μ)) :
    P (∫ ω, f ω + g ω ∂μ) := by
  rw [integral_add hf hg]
  exact h

/-! ### R9. `integral_const_mul` · `∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ` · goal
No integrability hypothesis: a non-integrable function has integral `0` by convention. -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (r : ℝ) (f : Ω → ℝ) (P : ℝ → Prop)
    (h : P (r * ∫ ω, f ω ∂μ)) : P (∫ ω, r * f ω ∂μ) := by
  rw [integral_const_mul]
  exact h

/-! ## Arithmetic -/

/-! ### R10. `linarith` · closes a linear (in)equality from hypotheses
Products such as `t * t * A` count as single unknowns, matched up to commutativity. -/
example (A B t : ℝ) (h : 0 ≤ t * t * A + B) : 0 ≤ A * (t * t) + B := by
  linarith

/-! ## The discriminant -/

/-! ### R11. `discrim_le_zero` · `(∀ x, 0 ≤ a * (x * x) + b * x + c) → discrim a b c ≤ 0`
`have := e` adds `e`'s statement under the name `this`. -/
example (a b c : ℝ) (h : ∀ x : ℝ, 0 ≤ a * (x * x) + b * x + c) (G : Prop)
    (k : discrim a b c ≤ 0 → G) : G := by
  have := discrim_le_zero h
  exact k this

/-! ### R12. `rw [discrim] at h` · context: `discrim a b c` → `b ^ 2 - 4 * a * c` -/
example (a b c : ℝ) (h : discrim a b c ≤ 0) : b ^ 2 - 4 * a * c ≤ 0 := by
  rw [discrim] at h
  exact h

/-! ### R13. `nlinarith` · closes a polynomial (in)equality from hypotheses
Like `linarith`, plus products of pairs of hypotheses; expands `(2 * b) ^ 2` itself. -/
example (a b c : ℝ) (h : (2 * b) ^ 2 - 4 * a * c ≤ 0) : b ^ 2 ≤ a * c := by
  nlinarith

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A square is integrated to something nonnegative: R2 with R3, in term mode -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) :
    0 ≤ ∫ ω, (f ω + g ω) ^ 2 ∂μ :=
  integral_nonneg fun _ => sq_nonneg _

/-! ### W2. Expand the integrand: R4, then `ring` -/
example {Ω : Type} (f g : Ω → ℝ) :
    (fun ω => (f ω + g ω) ^ 2) = fun ω => f ω ^ 2 + 2 * (f ω * g ω) + g ω ^ 2 := by
  funext ω
  ring

/-! ### W3. Split `∫ (3f + g)`: integrability facts first (R6), stated as `fun ω => …`, then R8, R9 -/
example {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) (hf : Integrable f μ)
    (hg : Integrable g μ) : ∫ ω, 3 * f ω + g ω ∂μ = 3 * ∫ ω, f ω ∂μ + ∫ ω, g ω ∂μ := by
  have i1 : Integrable (fun ω => 3 * f ω) μ := hf.const_mul 3
  rw [integral_add i1 hg]
  rw [integral_const_mul]

/-! ### W4. The discriminant argument on numbers: R11, R12, R13 -/
example (b : ℝ) (h : ∀ x : ℝ, 0 ≤ 1 * (x * x) + b * x + 1) : b ^ 2 ≤ 4 := by
  have := discrim_le_zero h
  rw [discrim] at this
  nlinarith

end M090Guide
