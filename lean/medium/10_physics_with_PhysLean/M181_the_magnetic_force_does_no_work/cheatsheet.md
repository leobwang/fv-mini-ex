# M181 · The magnetic force does no work: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's Euclidean space `ℝ³`
(`EuclideanSpace ℝ (Fin 3)`) with its inner product `⟪x, y⟫_ℝ`, finite sums `∑`, Mathlib's cross product
`⨯₃` and physlib's `⨯ₑ₃` on `ℝ³`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `EuclideanSpace ℝ (Fin 3)` | `ℝ³` with the dot product. Formally a wrapper `WithLp 2 (Fin 3 → ℝ)` around plain functions `Fin 3 → ℝ`; the `2` selects the Euclidean (L²) norm |
| `v.ofLp i` | component `i` of `v` (`i : Fin 3 = {0, 1, 2}`). You type `v i`; Lean inserts `.ofLp`, which strips the wrapper |
| `⟪x, y⟫_ℝ` | `inner ℝ x y`, the real inner product (dot product). The notation needs `open InnerProductSpace` |
| `⟪x, y⟫_ℝ` with `x y : ℝ` | the inner product of two reals, which is `y * x` (R4) |
| `r • x` | scalar `r : ℝ` times vector `x` |
| `∑ i, f i` | `f 0 + f 1 + f 2` for `i : Fin 3`: the sum over all values of `i` |
| `a ⨯₃ b`, `crossProduct a b` | Mathlib's cross product of `a b : Fin 3 → R`. The notation needs `open Matrix` |
| `a ⨯ₑ₃ b` | physlib's cross product on `EuclideanSpace ℝ (Fin 3)` (needs `open Space`). It is *notation*, not a definition |
| `(fun a b => (WithLp.equiv 2 (Fin 3 → ℝ)).symm ((crossProduct ((WithLp.equiv 2 (Fin 3 → ℝ)) a)) ((WithLp.equiv 2 (Fin 3 → ℝ)) b))) v B` | how the infoview prints `v ⨯ₑ₃ B`: strip the wrappers of `v`, `B`, take `⨯₃`, put the wrapper back |
| `WithLp.equiv 2 (Fin 3 → ℝ)`, `.symm` | the bijection wrapper → plain function, and its inverse |
| `WithLp.toLp 2 f` | the plain function `f : Fin 3 → ℝ` wrapped back into `EuclideanSpace ℝ (Fin 3)` (inverse of `.ofLp`); `simp` produces it from `(WithLp.equiv 2 _).symm f` (Traps) |
| `(crossProduct v.ofLp) B.ofLp i` | component `i` of `v ⨯₃ B` on plain functions; `simp` leaves this when `cross_apply` is not given to it |
| `![x, y, z]` | the vector `Fin 3 → R` with components `x, y, z` |
| `!₂[x, y, z]` | the same vector as an element of `EuclideanSpace ℝ (Fin 3)` |
| `(starRingEnd ℝ) x` | the conjugate of `x`; on `ℝ` it is `x` itself |

---

## Part 1 · `lorentzForce_power`

Statement: for `q : ℝ` and `E B v : EuclideanSpace ℝ (Fin 3)`, `⟪v, q • (E + v ⨯ₑ₃ B)⟫_ℝ = q * ⟪v, E⟫_ℝ`. In
words: the power `v · F` delivered by the Lorentz force is `q (v · E)`. It follows from linearity of the inner
product in its second argument and the fact `⟪v, v ⨯ₑ₃ B⟫_ℝ = 0`, which you prove by components.

### The fact `⟪v, v ⨯ₑ₃ B⟫_ℝ = 0`, by components

**R1 · `PiLp.inner_apply`** changes the **goal**: the inner product on `EuclideanSpace` becomes the sum of the
componentwise inner products. The lemma is `⟪x, y⟫ = ∑ i, ⟪x.ofLp i, y.ofLp i⟫`. Placeholders:
`{ι : Type} [Fintype ι] (x y : EuclideanSpace ℝ ι)`; `[Fintype ι]` says `ι` is finite, as `Fin 3` is.
`simp` does **not** apply it by itself; name it (`simp only [PiLp.inner_apply]`).

| Before | After |
|---|---|
| `x y : EuclideanSpace ℝ ι ⊢ P ⟪x, y⟫_ℝ` | `⊢ P (∑ i, ⟪x.ofLp i, y.ofLp i⟫_ℝ)` |

**R2 · `Fin.sum_univ_three`** changes the **goal**: a sum over `Fin 3` becomes three terms. The lemma is
`∑ i, f i = f 0 + f 1 + f 2`. Placeholders: `{β : Type} [AddCommMonoid β] (f : Fin 3 → β)`; `ℝ` is an
`AddCommMonoid` (a commutative `+` with `0`).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1 + f 2)` |

**R3 · `simp [cross_apply]`** changes the **goal**: a component of `a ⨯ₑ₃ b` becomes its formula. The lemma
is `cross_apply : a ⨯₃ b = ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]` for
`a b : Fin 3 → R`. On `EuclideanSpace` it cannot be used with `rw` directly: `simp` first removes the
`WithLp.equiv` wrappers (`WithLp.equiv_apply`, `WithLp.equiv_symm_apply`), then applies `cross_apply`, then
reads off one component of the `![…]` literal (`cons_val_zero`, `cons_val_one`, `cons_val`). Placeholders:
`(a b : EuclideanSpace ℝ (Fin 3))`. Components 1 and 2 are `a 2 * b 0 - a 0 * b 2` and `a 0 * b 1 - a 1 * b 0`.

| Before | After |
|---|---|
| `⊢ P (((fun a b => (WithLp.equiv 2 (Fin 3 → ℝ)).symm ((crossProduct ((WithLp.equiv 2 (Fin 3 → ℝ)) a)) ((WithLp.equiv 2 (Fin 3 → ℝ)) b))) a b).ofLp 0)` | `⊢ P (a.ofLp 1 * b.ofLp 2 - a.ofLp 2 * b.ofLp 1)` |

**R4 · `RCLike.inner_apply`, then `conj_trivial`** change the **goal**: the inner product of two reals becomes
a product. `RCLike.inner_apply : ⟪x, y⟫ = y * (starRingEnd 𝕜) x` holds for `𝕜 = ℝ` or `ℂ` (`RCLike 𝕜`), and
`conj_trivial : (starRingEnd ℝ) x = x`. `simp` applies both by itself (so R2–R4 all happen in one `simp` call).
Placeholders: `(x y : ℝ)`.

| Before | After `rw [RCLike.inner_apply]` | After `rw [conj_trivial]` |
|---|---|---|
| `⊢ P ⟪x, y⟫_ℝ` | `⊢ P (y * (starRingEnd ℝ) x)` | `⊢ P (y * x)` |

**R5 · `ring`** **closes** an equation that holds in every commutative ring. After R1–R4 your goal is a sum of
three products of differences, and the six monomials cancel in pairs. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ (a * b - b * a) * c + (b * c - c * b) * a = 0` | no goals |

### The main goal: linearity

**R6 · `unfold D`** changes the **goal**: the defined name `D` is replaced by its body, with the arguments
substituted. Placeholders: `double` defined by `double x := (2 : ℝ) • x` (`(2 : ℝ) • x` prints as `2 • x`).

| Before | After |
|---|---|
| `⊢ P (double x)` | `⊢ P (2 • x)` |

**R7 · `rw [real_inner_smul_right]`** changes the **goal**: a scalar in the second slot comes out. The lemma is
`⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ`. Placeholders: `{F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
(x y : F) (r : ℝ)`; the two brackets say `F` is a real inner-product space, as `EuclideanSpace ℝ (Fin 3)` is.

| Before | After |
|---|---|
| `⊢ P ⟪x, r • y⟫_ℝ` | `⊢ P (r * ⟪x, y⟫_ℝ)` |

**R8 · `rw [inner_add_right]`** changes the **goal**: a sum in the second slot splits. The lemma is
`⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫`. Placeholders: as R7, `(x y z : F)`.

| Before | After |
|---|---|
| `⊢ P ⟪x, y + z⟫_ℝ` | `⊢ P (⟪x, y⟫_ℝ + ⟪x, z⟫_ℝ)` |

Then `rw [h]` with your fact `h` replaces `⟪v, v ⨯ₑ₃ B⟫_ℝ` by `0` (TACTIC_STATES, "Rewriting").

**R9 · `rw [add_zero]`** changes the **goal**: `a + 0` becomes `a` (`zero_add` does `0 + a`). The lemma is
`a + 0 = a`. Placeholders: `{α : Type} [AddZeroClass α] (a : α)` (α has `+` and `0`, as `ℝ` does). When the
goal becomes `t = t`, `rw` closes it by `rfl` on its own.

| Before | After |
|---|---|
| `⊢ P (a + 0)` | `⊢ P a` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a dot product by components.** `⟪a, a⟫_ℝ = a 2 ^ 2 + a 1 ^ 2 + a 0 ^ 2`: R1, then
`simp [Fin.sum_univ_three]` (R2, R4), then R5:

```lean-goal
⊢ ⟪a, a⟫_ℝ = a.ofLp 2 ^ 2 + a.ofLp 1 ^ 2 + a.ofLp 0 ^ 2
⊢ ∑ i, ⟪a.ofLp i, a.ofLp i⟫_ℝ = a.ofLp 2 ^ 2 + a.ofLp 1 ^ 2 + a.ofLp 0 ^ 2
⊢ a.ofLp 0 ^ 2 + a.ofLp 1 ^ 2 + a.ofLp 2 ^ 2 = a.ofLp 2 ^ 2 + a.ofLp 1 ^ 2 + a.ofLp 0 ^ 2
```

**W2: components of cross products.** `(a ⨯ₑ₃ b) 2 + (b ⨯ₑ₃ a) 2 = 0`: R3 turns both components into formulas,
R5 closes:

```lean-goal
⊢ a.ofLp 0 * b.ofLp 1 - a.ofLp 1 * b.ofLp 0 + (b.ofLp 0 * a.ofLp 1 - b.ofLp 1 * a.ofLp 0) = 0
```

**W3: linearity chain.** With `mix r u w := r • (w + u)` and `h : ⟪x, w⟫_ℝ = 0`, the goal
`⟪x, mix r u w⟫_ℝ = r * ⟪x, u⟫_ℝ` goes through R6, R7, R8, `rw [h]`, then `rw [zero_add]` closes it:

```lean-goal
⊢ ⟪x, mix r u w⟫_ℝ = r * ⟪x, u⟫_ℝ
⊢ ⟪x, r • (w + u)⟫_ℝ = r * ⟪x, u⟫_ℝ
⊢ r * ⟪x, w + u⟫_ℝ = r * ⟪x, u⟫_ℝ
⊢ r * (⟪x, w⟫_ℝ + ⟪x, u⟫_ℝ) = r * ⟪x, u⟫_ℝ
⊢ r * (0 + ⟪x, u⟫_ℝ) = r * ⟪x, u⟫_ℝ
```

---

## Traps

- Plain `simp [Fin.sum_univ_three, cross_apply]` on `⟪v, v ⨯ₑ₃ B⟫_ℝ = 0` does not expand the inner product: it
  stops at `⟪v, !₂[…]⟫_ℝ = 0`. Run `simp only [PiLp.inner_apply]` (R1) first.
- Do not `simp` the main goal. `simp` rewrites `v ⨯ₑ₃ B` into `WithLp.toLp 2 (…)`, and then `rw [h]` no longer
  finds `⟪v, v ⨯ₑ₃ B⟫_ℝ`. Use `rw` with R7, R8: they keep the cross product in the form `h` states it.
- `⨯ₑ₃` is notation, so `unfold` and `rw [cross_apply]` do not see it on `EuclideanSpace`; `simp [cross_apply]`
  (R3) does.
- The physlib/Mathlib lemmas stating `⟪v, v ⨯ₑ₃ B⟫_ℝ = 0` outright are banned; prove it by components.
- `have h : T := by …`: the proof lines are indented further than `have`, or they run against the outer goal.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| add the fact first | `have h : ⟪v, v ⨯ₑ₃ B⟫_ℝ = 0 := by …` | TACTIC_STATES |
| `⟪x, y⟫_ℝ` on `ℝ³` → sum of components | `simp only [PiLp.inner_apply]` | R1 |
| `∑` over `Fin 3` → 3 terms | `Fin.sum_univ_three` | R2 |
| components of `a ⨯ₑ₃ b` | `simp [cross_apply]` | R3 |
| `⟪x, y⟫_ℝ` of reals → `y * x` | done by `simp` (`RCLike.inner_apply`, `conj_trivial`) | R4 |
| polynomial identity, terms cancel | `ring` | R5 |
| definition → body | `unfold lorentzForce` | R6 |
| `⟪x, r • y⟫_ℝ → r * ⟪x, y⟫_ℝ` | `rw [real_inner_smul_right]` | R7 |
| `⟪x, y + z⟫ → ⟪x, y⟫ + ⟪x, z⟫` | `rw [inner_add_right]` | R8 |
| use the fact | `rw [h]` | TACTIC_STATES |
| `a + 0 → a` | `rw [add_zero]` | R9 |
| see the state | infoview | |
