# H063 · Power iteration converges: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`constructor`, `refine ⟨w, h, ?_⟩`, `have`, `rw [h]`, `simp only [...]`,
`ring`, `ring_nf`, `exact`) are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `by`, `rw`, `simp`, `exact`, `have`,
`constructor`, `∧`/`∨`/`∃`, recursive `def` on `ℕ`, induction on paper.
**New here:** Mathlib's vectors `ι → ℝ` and matrices (`*ᵥ`, `ᵥ*`, `⬝ᵥ`, `•`, `ᵀ`), `Real.sqrt`,
field lemmas for `⁻¹` and `/`, the tactics `linarith`, `positivity`, `field_simp`, `set`, `obtain`,
`rcases`, `congr`, and limits of sequences as `Filter.Tendsto … atTop (𝓝 a)`.

**The mathematics.** Let `A` be a real symmetric 2×2 matrix with unit eigenvectors `u, v`,
`A u = μ₁ u`, `A v = μ₂ v`, and `|μ₂| < |μ₁|` (so `μ₁ ≠ 0`, `μ₁ ≠ μ₂`). Symmetry gives `u ⬝ᵥ v = 0`, so
`(a u + b v) ⬝ᵥ (p u + q v) = a p + b q`. The iterate `xₙ` is a positive multiple of
`aₙ u + bₙ v` with `aₙ = α μ₁ⁿ`, `bₙ = β μ₂ⁿ`. With `tₙ = bₙ² / aₙ²` (which tends to 0, since
`tₙ = (β/α)² ((μ₂/μ₁)²)ⁿ`):

- `rayleigh A xₙ = (μ₁ aₙ² + μ₂ bₙ²) / (aₙ² + bₙ²) = (μ₁ + tₙ μ₂) / (1 + tₙ) → μ₁`;
- for `n ≥ 1`, `xₙ ⬝ᵥ xₙ = 1`, so `(u ⬝ᵥ xₙ)² = aₙ² / (aₙ² + bₙ²) = 1 / (1 + tₙ) → 1`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change. A
  hypothesis that itself contains `, ` (such as `h : ∃ c, …`) is written next to the state, not inside it.
- `P` (or `Q`) is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. `G : Prop` is an arbitrary goal that the example finishes with
  `hG`; it only exists so the new hypothesis `h` can be shown.
- Placeholders are written as Lean binders. `{ι : Type} [Fintype ι]` is any finite index type (the exercise
  uses `Fin 2 = {0, 1}`); vectors are functions `ι → ℝ`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin 2 → ℝ` | a vector in ℝ²: a function from the index set `{0, 1}` to `ℝ` |
| `Matrix (Fin 2) (Fin 2) ℝ` | a real 2×2 matrix: a function `Fin 2 → Fin 2 → ℝ` |
| `A *ᵥ x` | `Matrix.mulVec`: matrix times column vector, `(A x)ᵢ = Σⱼ Aᵢⱼ xⱼ` |
| `v ᵥ* A` | `Matrix.vecMul`: row vector times matrix, `(vᵀA)ⱼ = Σᵢ vᵢ Aᵢⱼ` |
| `v ⬝ᵥ w` | `dotProduct`: `Σᵢ vᵢ wᵢ`, a real number |
| `c • x` | scalar multiplication (`HSMul.hSMul`); on two numbers `c • a = c * a` (R6) |
| `Aᵀ` | `Matrix.transpose`: `Aᵀ i j = A j i` |
| `v ⬝ᵥ A *ᵥ w` | `v ⬝ᵥ (A *ᵥ w)`: `*ᵥ` and `•` bind tighter than `⬝ᵥ` |
| `c • v ⬝ᵥ w` | `(c • v) ⬝ᵥ w`, **not** `c • (v ⬝ᵥ w)` (compare R5's two states) |
| `c • A *ᵥ x`, `A *ᵥ c • x` | `c • (A *ᵥ x)` and `A *ᵥ (c • x)`: both group to the right |
| `s * y ⬝ᵥ y`, `μ₂ * u ⬝ᵥ v` | `s * (y ⬝ᵥ y)`: `⬝ᵥ` binds tighter than `*`, `+`, `/` |
| `case zero`, `case succ` | the base case and the step after `induction` (R13) |
| `hy✝`, `this` | a hypothesis hidden by a newer one with the same name; the unnamed result of `have :` |
| `√x` | `Real.sqrt x`; for `x < 0` Lean defines `√x = 0` (R29) |
| `a⁻¹` | inverse; Lean defines `0⁻¹ = 0` (R30), so `x / 0 = 0` |
| `y : ℝ := f x` | a local definition made by `set` (R24): `y` *is* `f x` |
| `inst✝ : Fintype ι` | an anonymous type-class hypothesis: "`ι` is finite" |
| `Tendsto f atTop (𝓝 a)` | `Filter.Tendsto`: `f n → a` as `n → ∞`, i.e. `∀ ε > 0, ∃ N, ∀ n ≥ N, dist (f n) a < ε` |
| `atTop` | `Filter.atTop`, the filter of "all sufficiently large `n`" |
| `𝓝 a` | `nhds a`, the filter of neighbourhoods of `a` (`open Topology` gives the notation) |
| `fun x => c` | the constant sequence `c` |
| `f / g`, `f ∘ g` | pointwise quotient `fun n => f n / g n`; composition `fun n => f (g n)` |

`dist x y = |x − y|` on `ℝ`; Lean prints absolute value as `|a|` (`abs a`).

---

## Part 1 · `eigvec_orthogonal` (milestone)

Statement: if `Aᵀ = A`, `A *ᵥ u = μ₁ • u`, `A *ᵥ v = μ₂ • v` and `μ₁ ≠ μ₂`, then `u ⬝ᵥ v = 0`.
Proof on paper: `μ₂ (u ⬝ᵥ v) = u ⬝ᵥ A v = (A u) ⬝ᵥ v = μ₁ (u ⬝ᵥ v)`, so `(μ₁ − μ₂)(u ⬝ᵥ v) = 0`.

**R1 · `rw [Matrix.dotProduct_mulVec]`** changes the **goal**. The lemma is
`v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w`: `A` moves from the right factor onto the left one, as a row vector.
Placeholders: `{ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (v w : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ A *ᵥ w)` | `⊢ P (v ᵥ* A ⬝ᵥ w)` |

**R2 · `rw [← Matrix.mulVec_transpose]`** changes the **goal**. The lemma is `Aᵀ *ᵥ x = x ᵥ* A`; right to
left it turns a row-vector product back into a column one with the transpose. Then `rw [hA]` with
`hA : Aᵀ = A` removes the `ᵀ`. Placeholders: `(A : Matrix ι ι ℝ) (x : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (x ᵥ* A)` | `⊢ P (Aᵀ *ᵥ x)` |

**R3 · `rw [e] at h`** changes the **context**: it rewrites hypothesis `h` instead of the goal. Several
lemmas: `rw [e₁, e₂] at h`. Placeholders: `(hu : A *ᵥ u = μ • u)`, `(Q : (ι → ℝ) → Prop)`.

| Before | After |
|---|---|
| `h : Q (A *ᵥ u) ⊢ Q (μ • u)` | `h : Q (μ • u) ⊢ Q (μ • u)` |

**R4 · `rw [dotProduct_smul]`** changes the **goal**: `v ⬝ᵥ (c • w) = c • (v ⬝ᵥ w)`, a scalar comes out of
the right factor. Placeholders: `(c : ℝ) (v w : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ c • w)` | `⊢ P (c • (v ⬝ᵥ w))` |

**R5 · `rw [smul_dotProduct]`** changes the **goal**: `(c • v) ⬝ᵥ w = c • (v ⬝ᵥ w)`, a scalar comes out of
the left factor. Mind the printing: the Before state *is* `(c • v) ⬝ᵥ w`.

| Before | After |
|---|---|
| `⊢ P (c • v ⬝ᵥ w)` | `⊢ P (c • (v ⬝ᵥ w))` |

**R6 · `rw [smul_eq_mul]`** changes the **goal**: on two numbers `c • a = c * a`. After R4/R5 the scalar is
still written `•`; this turns it into ordinary `*` so `ring`, `linarith` and `field_simp` can use it.
Placeholders: `(c a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (c • a)` | `⊢ P (c * a)` |

**R7 · `linarith`** **closes** a goal `=`, `≤`, `<` (or `False`) that is a linear combination of the
hypotheses. It multiplies out first, and a product of unknowns such as `a * x` counts as one unknown; it never
multiplies two hypotheses together. Extra facts go in brackets: `linarith [abs_nonneg a]`.

| Before | After |
|---|---|
| `h : a * x = b * x + 2 ⊢ (a - b) * x = 2` | no goals |

**R8 · `rw [mul_eq_zero] at h`** changes the **context**. The lemma is `a * b = 0 ↔ a = 0 ∨ b = 0` (in any
ring without zero divisors, such as `ℝ`). Term form: `mul_eq_zero.mp h : a = 0 ∨ b = 0`.

| Before | After |
|---|---|
| `h : a * b = 0 ⊢ Q` | `h : a = 0 ∨ b = 0 ⊢ Q` |

**R9 · `rw [sub_ne_zero]`** changes the **goal**: `a - b ≠ 0 ↔ a ≠ b`. Term form: `sub_ne_zero.mpr hne`.

| Before | After |
|---|---|
| `⊢ a - b ≠ 0` | `⊢ a ≠ b` |

**R10 · `h.resolve_left hna`** (`Or.resolve_left`) **closes** a goal `B` from `h : A ∨ B` and `hna : ¬A`.
Chain: `(mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)`.

| Before | After |
|---|---|
| `h : A ∨ B, hna : ¬A ⊢ B` | no goals |

---

## Part 2 · `dot_comb` (milestone)

Statement: for an orthonormal pair (`u ⬝ᵥ u = 1`, `v ⬝ᵥ v = 1`, `u ⬝ᵥ v = 0`),
`(a • u + b • v) ⬝ᵥ (p • u + q • v) = a * p + b * q` and `u ⬝ᵥ (p • u + q • v) = p`.
Expand with R12, R4, R5, R6 inside one `simp only [...]` that also contains the four dot-product facts,
then `ring`.

**R11 · `rw [dotProduct_comm]`** changes the **goal**: `v ⬝ᵥ w = w ⬝ᵥ v`. You need it to get `v ⬝ᵥ u = 0`
from `u ⬝ᵥ v = 0`, because the expansion produces both.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ w)` | `⊢ P (w ⬝ᵥ v)` |

**R12 · `add_dotProduct`, `dotProduct_add`** change the **goal**: `(x + y) ⬝ᵥ w = x ⬝ᵥ w + y ⬝ᵥ w` and
`v ⬝ᵥ (x + y) = v ⬝ᵥ x + v ⬝ᵥ y`. Placeholders: `(x y v w : ι → ℝ)`.

| Before | After `rw [add_dotProduct]` | After `rw [dotProduct_add, dotProduct_add]` |
|---|---|---|
| `⊢ P ((x + y) ⬝ᵥ (v + w))` | `⊢ P (x ⬝ᵥ (v + w) + y ⬝ᵥ (v + w))` | `⊢ P (x ⬝ᵥ v + x ⬝ᵥ w + (y ⬝ᵥ v + y ⬝ᵥ w))` |

---

## Part 3 · `powerIter_eq` (milestone)

Statement: `∃ c, 0 < c ∧ powerIter A (α • u + β • v) n = c • ((α * μ₁ ^ n) • u + (β * μ₂ ^ n) • v)`.
Induction on `n`; the step multiplies by `A` (eigen-equations) and then by the positive factor
`(√(y ⬝ᵥ y))⁻¹`, which needs `0 < y ⬝ᵥ y`.

**R13 · `induction n with | zero => ?_ | succ n ih => ?_`** changes the **goal list**: one goal becomes the
base case and the step, and the step's context gains `n` and the induction hypothesis `ih`. Writing `?_`
leaves each case as a goal; you may instead write the proofs after `=>` on indented lines.

| Before | After |
|---|---|
| `⊢ P n` | `⊢ P 0`, `ih : P n ⊢ P (n + 1)` |

**R14 · `simp only [f]` on a recursive `def`** changes the **goal**: `f … 0` and `f … (n + 1)` become the body
of that case (Lean's equation lemmas for `f`). A `let y := e` inside the body is substituted, so `y` is
written out as `e` everywhere. Placeholders: `iter x₀ : ℕ → ℝ` defined by `iter x₀ 0 = x₀`,
`iter x₀ (n + 1) = let y := 3 * iter x₀ n; (√y)⁻¹ * y`. `simp [f]` (no `only`) unfolds and also simplifies.

| Before | After |
|---|---|
| `⊢ P (iter x₀ 0) ∧ P (iter x₀ (n + 1))` | `⊢ P x₀ ∧ P ((√(3 * iter x₀ n))⁻¹ * (3 * iter x₀ n))` |

**R15 · `obtain ⟨c, hc, hx⟩ := h`** changes the **context**: an existential with a conjunction is taken
apart into the witness and its two facts. Placeholders: `(A B : ℝ → Prop) (h : ∃ c, A c ∧ B c)`.

| Before | After |
|---|---|
| hypothesis `h : ∃ c, A c ∧ B c`, goal `⊢ G` | `c : ℝ, hc : A c, hx : B c ⊢ G` (and `h` is gone) |

**R16 · `rw [Matrix.mulVec_smul]`** changes the **goal**: `A *ᵥ (c • x) = c • (A *ᵥ x)`.

| Before | After |
|---|---|
| `⊢ P (A *ᵥ c • x)` | `⊢ P (c • A *ᵥ x)` |

**R17 · `rw [Matrix.mulVec_add]`** changes the **goal**: `A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y`.

| Before | After |
|---|---|
| `⊢ P (A *ᵥ (x + y))` | `⊢ P (A *ᵥ x + A *ᵥ y)` |

**R18 · `rw [smul_smul]`** changes the **goal**: `a • b • x = (a * b) • x` (`•` groups to the right).
After `rw [hu]` you get `(α * μ₁ ^ n) • μ₁ • u`; this merges the scalars into `(α * μ₁ ^ n * μ₁) • u`. Placeholders: `(a b : ℝ) (x : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a • b • x)` | `⊢ P ((a * b) • x)` |

**R19 · `congr 2`** changes the **goal list**: in an equation whose two sides have the same shape, it strips
two layers (`c • _`, then `_ + _`) and leaves one goal per differing argument. Equal arguments (`c = c`)
and goals that are a hypothesis are closed automatically. In the exercise the goals left are
`(α * μ₁ ^ n * μ₁) • u = (α * μ₁ ^ (n + 1)) • u` and the same for `v`; follow `congr 2` with `<;> ring_nf`, which
puts both scalars in one normal form and then closes each goal by `rfl`.

| Before | After |
|---|---|
| `⊢ c • (x + y) = c • (x' + y')` | `⊢ x = x'`, `⊢ y = y'` |

**R20 · `apply mul_pos`** changes the **goal list**: `mul_pos : 0 < a → 0 < b → 0 < a * b`, so the goal
becomes its two premises. Term form `mul_pos ha hb`. (`one_pos : 0 < 1` gives the base-case witness.)

| Before | After |
|---|---|
| `⊢ 0 < a * b` | `⊢ 0 < a`, `⊢ 0 < b` |

**R21 · `apply mul_ne_zero`, `pow_ne_zero n hb`** change the **goal list**. `mul_ne_zero : a ≠ 0 → b ≠ 0 →
a * b ≠ 0`; `pow_ne_zero n : a ≠ 0 → a ^ n ≠ 0`. Together: `mul_ne_zero hα (pow_ne_zero _ hμ) : α * μ₁ ^ n ≠ 0`.

| Before | After |
|---|---|
| `⊢ a * b ^ n ≠ 0` | `⊢ a ≠ 0`, `⊢ b ^ n ≠ 0` |

**R22 · `rw [mul_self_pos]`** changes the **goal**: `0 < a * a ↔ a ≠ 0` (term `mul_self_pos.mpr ha`).
Its partner `mul_self_nonneg b : 0 ≤ b * b` needs no hypothesis.

| Before | After |
|---|---|
| `⊢ 0 < a * a` | `⊢ a ≠ 0` |

**R23 · `apply add_pos_of_pos_of_nonneg`** changes the **goal list**: `0 < a → 0 ≤ b → 0 < a + b`. With R22:
`0 < a * a + b * b` when `a ≠ 0`, which is `0 < y ⬝ᵥ y` after `dot_comb`.

| Before | After |
|---|---|
| `⊢ 0 < a + b` | `⊢ 0 < a`, `⊢ 0 ≤ b` |

**R24 · `set y := e with hy`** changes the **context and the goal**: it adds the local definition
`y : ℝ := e` and `hy : y = e`, and replaces every `e` in the goal and in all hypotheses by `y`. Without
`with hy` no equation is added. Use it to name `A *ᵥ powerIter A x₀ n` or the ratio sequence `t`. If a
hypothesis is already called `hy`, `with hy` hides it (it becomes `hy✝`, unusable by name): then leave out
`with hy`.

| Before | After |
|---|---|
| `⊢ P (f x + f x)` | `y : ℝ := f x, hy : y = f x ⊢ P (y + y)` |

**R25 · `rw [inv_pos]`, `rw [Real.sqrt_pos]`** change the **goal**: `0 < a⁻¹ ↔ 0 < a`, `0 < √x ↔ 0 < x`.
Term form for the witness's positivity: `inv_pos.mpr (Real.sqrt_pos.mpr hpos)`.

| Before | After `rw [inv_pos]` | After `rw [Real.sqrt_pos]` |
|---|---|---|
| `⊢ 0 < (√x)⁻¹` | `⊢ 0 < √x` | `⊢ 0 < x` |

**R26 · `rw [mul_smul]`** changes the **goal**: `(a * b) • x = a • b • x`, the reverse of R18. It splits the
witness `(√(y ⬝ᵥ y))⁻¹ * c` so that `c • (…)` can be folded back into `y` with `rw [← hy]`.

| Before | After |
|---|---|
| `⊢ P ((a * b) • x)` | `⊢ P (a • b • x)` |

---

## Part 4 · `normalized` (milestone)

Statement: `x ⬝ᵥ x = 0 ∨ x ⬝ᵥ x = 1` for `x = powerIter A x₀ (n + 1)`. After unfolding, `x = s • y` with
`s = (√(y ⬝ᵥ y))⁻¹`, so `x ⬝ᵥ x = s * (s * (y ⬝ᵥ y))`. If `y ⬝ᵥ y ≤ 0` then `√(y ⬝ᵥ y) = 0` and `s = 0`;
otherwise `s * s * (y ⬝ᵥ y) = 1`.

**R27 · `rcases le_or_gt a b with h | h`** changes the **goal list**: `le_or_gt a b : a ≤ b ∨ a > b`, and
`rcases` gives one goal per side. Lean prints `a > b` as `b < a`.

| Before | After |
|---|---|
| `⊢ Q` | `h : a ≤ b ⊢ Q`, `h : b < a ⊢ Q` |

**R28 · `left` / `right`** change the **goal**: `A ∨ B` becomes `A` (`left`) or `B` (`right`).

| Before | After `right` |
|---|---|
| `⊢ A ∨ B` | `⊢ B` |

**R29 · `rw [Real.sqrt_eq_zero'.mpr hx]`** changes the **goal**. `Real.sqrt_eq_zero' : √x = 0 ↔ x ≤ 0`;
`.mpr hx` with `hx : x ≤ 0` is the equation `√x = 0`. Placeholders: `(x : ℝ) (hx : x ≤ 0)`.

| Before | After |
|---|---|
| `⊢ P √x` | `⊢ P 0` |

**R30 · `rw [inv_zero]`, `rw [zero_mul]`** change the **goal**: `0⁻¹ = 0`, `0 * a = 0` (and `mul_zero :
a * 0 = 0`).

| Before | After `rw [inv_zero]` | After `rw [zero_mul]` |
|---|---|---|
| `⊢ P (0⁻¹ * a)` | `⊢ P (0 * a)` | `⊢ P 0` |

**R31 · `rw [← mul_assoc]`** changes the **goal**: `mul_assoc : a * b * c = a * (b * c)` (`*` groups to the
left); right to left it regroups `s * (s * d)` as `s * s * d`.

| Before | After |
|---|---|
| `⊢ P (a * (b * c))` | `⊢ P (a * b * c)` |

**R32 · `rw [← mul_inv]`** changes the **goal**: `mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹`; right to left it merges
two inverses, giving `(√d * √d)⁻¹`.

| Before | After |
|---|---|
| `⊢ P (a⁻¹ * b⁻¹)` | `⊢ P (a * b)⁻¹` |

**R33 · `rw [Real.mul_self_sqrt hx]`** changes the **goal**: `0 ≤ x → √x * √x = x`. With `h : 0 < d`, pass
`h.le : 0 ≤ d`.

| Before | After |
|---|---|
| `⊢ P (√x * √x)` | `⊢ P x` |

**R34 · `rw [inv_mul_cancel₀ ha]`** changes the **goal**: `a ≠ 0 → a⁻¹ * a = 1`. With `h : 0 < d`, pass
`h.ne' : d ≠ 0`.

| Before | After |
|---|---|
| `⊢ P (a⁻¹ * a)` | `⊢ P 1` |

---

## Part 5 · `ratio_tendsto` (milestone)

Statement: `|μ₂| < |μ₁|` implies `(β * μ₂ ^ n) ^ 2 / (α * μ₁ ^ n) ^ 2 → 0`. Write the term as
`(β / α) ^ 2 * ((μ₂ / μ₁) ^ 2) ^ n`; the geometric factor tends to 0 because `(μ₂ / μ₁) ^ 2 < 1`.
(If `α = 0` both sides are `0` in Lean, since `x / 0 = 0`; no case split is needed.)

**R35 · `rintro rfl`** changes the **goal and the context**: a goal `x ≠ 0` is `x = 0 → False`; `rintro rfl`
assumes `x = 0` and substitutes `0` for `x` everywhere.

| Before | After |
|---|---|
| `hx : P x ⊢ x ≠ 0` | `hx : P 0 ⊢ False` |

**R36 · `rw [abs_zero] at h`** changes the **context**: `abs_zero : |0| = 0`. Then
`linarith [abs_nonneg a]` (`abs_nonneg a : 0 ≤ |a|`) closes `False`. The hypotheses contain `|`, which a table
cell cannot hold, so here they are in words: `h` goes from `|a| < |0|` to `|a| < 0`; the goal stays:

| Before | After |
|---|---|
| `⊢ False` | `⊢ False` |

**R37 · `rw [div_pow]`** changes the **goal**: `(a / b) ^ n = a ^ n / b ^ n`; right to left
(`rw [← div_pow]`) merges `a ^ n / b ^ n` into `(a / b) ^ n`.

| Before | After |
|---|---|
| `⊢ P ((a / b) ^ n)` | `⊢ P (a ^ n / b ^ n)` |

**R38 · `rw [div_lt_one hb]`** changes the **goal**: `0 < b → (a / b < 1 ↔ a < b)`. The argument `hb` can be
`(by positivity)` (R39).

| Before | After |
|---|---|
| `⊢ a / b < 1` | `⊢ a < b` |

**R39 · `positivity`** **closes** a goal `0 < e` or `0 ≤ e` by the syntax of `e`: squares and even powers
are `≥ 0`, sums and products of positives are positive, and `x ^ 2 > 0` when `x ≠ 0` is a hypothesis. It does
not prove `0 < b - a` and ignores hypotheses such as `0 < a - b`.

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ 0 < a ^ 2 + b ^ 2` | no goals |

**R40 · `rw [sq_lt_sq]`** changes the **goal**: `sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b|`. Use `sq_lt_sq.mpr
hgap`. The After state contains `|`, so both states are in this block:

```lean-goal
⊢ a ^ 2 < b ^ 2
⊢ |a| < |b|
```

**R41 · `have h := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1`** changes the **context**. The lemma:
`0 ≤ r → r < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)`, the geometric sequence tends to 0.
Placeholders: `(r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1)`.

| Before | After |
|---|---|
| `⊢ G` | `h : Tendsto (fun n => r ^ n) atTop (𝓝 0) ⊢ G` |

**R42 · `have h := hf.const_mul b`** (`Filter.Tendsto.const_mul`) changes the **context**: from
`hf : Tendsto f atTop (𝓝 a)`, the sequence `b * f n` tends to `b * a`. With `a = 0`, clean the limit with
`rw [mul_zero] at h`. Placeholders: `(f : ℕ → ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `hf : Tendsto f atTop (𝓝 a) ⊢ G` | `h : Tendsto (fun x => b * f x) atTop (𝓝 (b * a)) ⊢ G` |

**R43 · `refine hf.congr fun n => ?_`** (`Filter.Tendsto.congr`) changes the **goal**: to show `g → a` it is
enough that `f → a` and `f n = g n` for every `n`; the goal becomes that pointwise equation. With a
pointwise lemma `hR : ∀ n, g n = f n`: `exact hf.congr fun n => (hR n).symm`.

| Before | After |
|---|---|
| `⊢ Tendsto g atTop (𝓝 a)` | `n : ℕ ⊢ f n = g n` |

**R44 · `rw [mul_div_mul_comm]`** changes the **goal**: `a * b / (c * d) = a / c * (b / d)`.

| Before | After |
|---|---|
| `⊢ P (a * b / (c * d))` | `⊢ P (a / c * (b / d))` |

**R45 · `rw [mul_pow]`, `rw [← pow_mul]`** change the **goal**: `(a * b) ^ n = a ^ n * b ^ n` and
`pow_mul : a ^ (m * n) = (a ^ m) ^ n`. Right to left, `← pow_mul` collapses a power of a power. Then
`mul_comm n 2` turns `n * 2` into `2 * n` if needed.

| Before | After `rw [mul_pow]` | After `rw [← pow_mul]` |
|---|---|---|
| `⊢ P ((a * b ^ m) ^ n)` | `⊢ P (a ^ n * (b ^ m) ^ n)` | `⊢ P (a ^ n * b ^ (m * n))` |

---

## Part 6 · `power_iteration`

Statement: `rayleigh A xₙ → μ₁` and `(u ⬝ᵥ xₙ) ^ 2 → 1`, for `xₙ = powerIter A (α • u + β • v) n`.
Uses all five milestones: first rewrite each target as a function of `tₙ` (pointwise lemmas `hR`, `hC`), then
build the limit from `t → 0` (R49–R52) and transfer it with R43.

**R46 · `exact lt_irrefl a h`** **closes** `False` from `h : a < a` (`lt_irrefl a : ¬a < a`). After
`rintro rfl` on `μ₁ ≠ μ₂`, `hgap` reads `|μ₁| < |μ₁|`.

| Before | After |
|---|---|
| `h : a < a ⊢ False` | no goals |

**R47 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero from
the context (put `have := ha n` there first) and normalises both sides. The exact output form is up to
`field_simp`; often it closes the goal itself.

| Before | After |
|---|---|
| `⊢ x / a = y / b` | `⊢ x * b = a * y` |

**R48 · `rw [eq_div_iff hc]`** changes the **goal**: `c ≠ 0 → (a = b / c ↔ a * c = b)`. The argument can be
`(by positivity)`.

| Before | After |
|---|---|
| `⊢ a = b / c` | `⊢ a * c = b` |

**R49 · `tendsto_const_nhds (x := c)`** changes the **context**: the constant sequence `c` tends to `c`.
`(x := c)` names the constant; without it Lean must infer it from the surrounding term, which fails at the
start of a `.add` chain.

| Before | After |
|---|---|
| `⊢ G` | `h : Tendsto (fun x => c) atTop (𝓝 c) ⊢ G` |

**R50 · `have h := hf.add hg`** (`Filter.Tendsto.add`) changes the **context**: limits add.

| Before | After |
|---|---|
| `⊢ G` | `h : Tendsto (fun x => f x + g x) atTop (𝓝 (a + b)) ⊢ G` |

**R51 · `have h := hf.mul_const b`** (`Filter.Tendsto.mul_const`) changes the **context**: `f n * b → a * b`.

| Before | After |
|---|---|
| `⊢ G` | `h : Tendsto (fun x => f x * b) atTop (𝓝 (a * b)) ⊢ G` |

**R52 · `have h := hf.div hg hb`** (`Filter.Tendsto.div`) changes the **context**: limits divide when the
denominator's limit `b ≠ 0` (prove it with `(by norm_num)`). The result is printed `f / g`, the pointwise
quotient, which is definitionally `fun n => f n / g n`, so `exact` and R43 accept it.

| Before | After |
|---|---|
| `⊢ G` | `h : Tendsto (f / g) atTop (𝓝 (a / b)) ⊢ G` |

**R53 · `rw [← tendsto_add_atTop_iff_nat 1]`** changes the **goal**. The lemma:
`Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f atTop l`. Right to left you only need the limit from
index `1` on, where `xₙ` is a unit vector (Part 4).

| Before | After |
|---|---|
| `⊢ Tendsto f atTop (𝓝 L)` | `⊢ Tendsto (fun n => f (n + 1)) atTop (𝓝 L)` |

**R54 · `have h := hf.comp (tendsto_add_atTop_nat 1)`** changes the **context**.
`tendsto_add_atTop_nat 1 : Tendsto (fun a => a + 1) atTop atTop`; composing (`Filter.Tendsto.comp`) gives the
shifted sequence `f (n + 1) → L`, printed with `∘`.

| Before | After |
|---|---|
| `hf : Tendsto f atTop (𝓝 L) ⊢ G` | `h : Tendsto (f ∘ fun a => a + 1) atTop (𝓝 L) ⊢ G` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a quotient limit.** With `hs : Tendsto s atTop (𝓝 0)`, one `have` chains R49, R51, R50, R49, R50, R52:
`(tendsto_const_nhds (x := (3 : ℝ))).add (hs.mul_const 5) |>.div ((tendsto_const_nhds (x := (2 : ℝ))).add hs) (by norm_num)`.
Its limit is not yet in normal form; `simp only [zero_mul, add_zero] at h` fixes that (add `div_one` when the
denominator becomes `1 + 0`):

| Step | State |
|---|---|
| after `have h := …` | `h : Tendsto ((fun x => 3 + s x * 5) / fun x => 2 + s x) atTop (𝓝 ((3 + 0 * 5) / (2 + 0))) ⊢ Tendsto (fun n => (3 + s n * 5) / (2 + s n)) atTop (𝓝 (3 / 2))` |
| after `simp only … at h` | `h : Tendsto ((fun x => 3 + s x * 5) / fun x => 2 + s x) atTop (𝓝 (3 / 2)) ⊢ Tendsto (fun n => (3 + s n * 5) / (2 + s n)) atTop (𝓝 (3 / 2))` |

**W2: a rescaled iteration by induction.** `halve (n + 1) = let y := 4 * halve n; (√2)⁻¹ * y`. Claim
`∃ c, 0 < c ∧ halve n = c * 4 ^ n`. R13 gives the two cases:

| Before | After |
|---|---|
| `⊢ ∃ c, 0 < c ∧ halve n = c * 4 ^ n` | `⊢ ∃ c, 0 < c ∧ halve 0 = c * 4 ^ 0`, `⊢ ∃ c, 0 < c ∧ halve (n + 1) = c * 4 ^ (n + 1)` with `ih : ∃ c, 0 < c ∧ halve n = c * 4 ^ n` |

Base: `⟨1, one_pos, by simp [halve]⟩` (R14). Step: R15 on `ih`, witness `(√2)⁻¹ * c` with positivity from
R20 and R25, then `simp only [halve, hx]` (R14) and `ring`.

**W3: a dot product with an eigenvector.** From `hu : A *ᵥ u = μ • u`, `hw : w ⬝ᵥ u = 2`:
`rw [hu, dotProduct_smul, hw, smul_eq_mul] at h` (R3 with R4, R6), then `linarith` (R7).

| Before | After |
|---|---|
| `h : w ⬝ᵥ A *ᵥ u = 6 ⊢ μ = 3` | `h : μ * 2 = 6 ⊢ μ = 3` |

---

## Traps

- Symmetry `Aᵀ = A` is used **only** to get `u ⬝ᵥ v = 0` (Part 1). The start vector is general: `u, v` form a
  basis, so every `x₀` is some `α • u + β • v`.
- Printing: `c • v ⬝ᵥ w` is `(c • v) ⬝ᵥ w` and `v ⬝ᵥ A *ᵥ w` is `v ⬝ᵥ (A *ᵥ w)`. Use `smul_dotProduct` for the
  first, `dotProduct_smul` for a scalar on the right (R4, R5).
- `√x = 0` for `x ≤ 0` and `0⁻¹ = 0`: a `powerIter` step can produce the zero vector. That is why `normalized`
  has a `= 0` case, and why `powerIter_eq` must prove `0 < y ⬝ᵥ y` (from `α ≠ 0`, `μ₁ ≠ 0`) to keep `c > 0`.
- `(u ⬝ᵥ x₀) ^ 2 = 1 / (1 + t 0)` is false in general (`x₀` is not a unit vector). Prove the formula for
  `n + 1` and shift with R53, R54.
- After R50–R52 the limit reads `(μ₁ + 0 * μ₂) / (1 + 0)`, not `μ₁`. Normalise it with
  `simp only [zero_mul, add_zero, div_one] at h` before `h.congr` (W1).
- `tendsto_const_nhds` alone cannot guess its constant at the head of a chain; write `(x := μ₁)` (R49).
- `field_simp` only clears a denominator it can prove nonzero; put `have := ha n` (`α * μ₁ ^ n ≠ 0`) in the
  context first. Its output form may differ from your expectation: read the goal it leaves.
- `linarith` does not multiply hypotheses: to refute `c * (c * d) = 0` it needs `0 < c * (c * d)` as a
  hypothesis (R20, R23, R22).
- `set y := e with hy` when `hy` already exists hides the old `hy` (it becomes `hy✝`). In `powerIter_eq` the
  fact `hy : A *ᵥ xₙ = c • (…)` must survive, so write `set y := A *ᵥ xₙ` without `with`.
- `set` rewrites hypotheses too. Introduce it after the `have`s you still want to state with the original
  expression, or state them with the new name.
- `congr 2` closes goals that are hypotheses or `rfl` without telling you; the goals left are the hard ones
  (R19).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| move `A` across `⬝ᵥ` (symmetric `A`) | `rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]` | R1, R2 |
| rewrite a hypothesis | `rw [e] at h` | R3 |
| scalar out of a dot product | `dotProduct_smul` (right), `smul_dotProduct` (left), then `smul_eq_mul` | R4–R6 |
| linear consequence of hypotheses | `linarith [extra facts]` | R7 |
| `(a - b) * x = 0`, `a ≠ b` ⟹ `x = 0` | `(mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)` | R8–R10 |
| swap a dot product | `dotProduct_comm` | R11 |
| expand dot products of sums | `simp only [dotProduct_add, add_dotProduct, …]` then `ring` | R12 |
| induction with named cases | `induction n with \| zero => ?_ \| succ n ih => ?_` | R13 |
| unfold a recursive def | `simp only [f]` / `simp [f]` | R14 |
| destructure `∃ c, A ∧ B` | `obtain ⟨c, hc, hx⟩ := h` | R15 |
| `A *ᵥ` through `•` and `+` | `Matrix.mulVec_smul`, `Matrix.mulVec_add` | R16, R17 |
| merge / split scalars | `smul_smul` / `mul_smul` | R18, R26 |
| same-shape equation → pieces | `congr 2 <;> ring_nf` | R19 |
| positivity of products and sums | `mul_pos`, `add_pos_of_pos_of_nonneg`, `mul_self_pos.mpr`, `mul_self_nonneg` | R20, R22, R23 |
| nonzero products and powers | `mul_ne_zero ha (pow_ne_zero _ hb)` | R21 |
| name a subterm | `set y := e with hy` | R24 |
| `0 < (√x)⁻¹` | `inv_pos.mpr (Real.sqrt_pos.mpr h)` | R25 |
| case split `≤` / `>` | `rcases le_or_gt a b with h \| h` | R27 |
| pick a side of `∨` | `left` / `right` | R28 |
| `√x = 0` for `x ≤ 0` | `rw [Real.sqrt_eq_zero'.mpr h, inv_zero, zero_mul]` | R29, R30 |
| `s * (s * d) = 1` for `s = (√d)⁻¹` | `rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt h.le, inv_mul_cancel₀ h.ne']` | R31–R34 |
| `x ≠ 0` by contradiction | `rintro rfl` | R35 |
| `abs` facts | `abs_zero`, `abs_nonneg`, `sq_lt_sq` | R36, R40 |
| powers of quotients | `div_pow`, `mul_div_mul_comm`, `mul_pow`, `pow_mul` | R37, R44, R45 |
| `a / b < 1` | `rw [div_lt_one (by positivity)]` | R38, R39 |
| `0 < e` by shape | `positivity` | R39 |
| `rⁿ → 0` | `tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1` | R41 |
| combine limits | `.const_mul`, `.add`, `.mul_const`, `.div hg (by norm_num)`, `tendsto_const_nhds (x := c)` | R42, R49–R52 |
| transfer a limit pointwise | `h.congr fun n => (hR n).symm` | R43 |
| `False` from `a < a` | `lt_irrefl a h` | R46 |
| clear denominators | `field_simp` | R47 |
| `a = b / c` | `rw [eq_div_iff hc]` | R48 |
| limit from index 1 on | `rw [← tendsto_add_atTop_iff_nat 1]`, `ht.comp (tendsto_add_atTop_nat 1)` | R53, R54 |
| see the state | infoview | |
