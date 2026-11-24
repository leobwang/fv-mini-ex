# M169 · Hermitian Hamiltonians have real eigenvalues: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's complex inner product
`⟪x, y⟫_ℂ` and its scalar rules, the complex conjugate `starRingEnd ℂ`, cancellation in a field, and
physlib's tight-binding chain (only its Hilbert space, its Hamiltonian, and the fact that the
Hamiltonian is Hermitian).

The math: from $H\psi = E\psi$ and $\langle H\psi, \psi\rangle = \langle \psi, H\psi\rangle$,
$\bar E \langle\psi,\psi\rangle = E \langle\psi,\psi\rangle$; since $\psi \ne 0$,
$\langle\psi,\psi\rangle \ne 0$ cancels, so $\bar E = E$, i.e. $\operatorname{Im} E = 0$.
Here $\bar E$ is the complex conjugate of $E$ and the inner product is conjugate-linear in its first slot.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal or hypothesis" (`P : α → Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger expression.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Field K]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- `{V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]` reads "`V` is a complex inner product
  space". `T.HilbertSpace` is one, so every entry stated for `V` applies to it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `T : TightBindingChain` | physlib's tight-binding chain: `N` sites, spacing `a`, on-site energy `E0`, hopping `t` |
| `T.HilbertSpace` | its state space, `ℂ^N` (physlib's `FiniteHilbertSpace (Fin T.N)`), a complex inner product space |
| `T.hamiltonian` | the Hamiltonian, a `ℂ`-linear map `T.HilbertSpace →ₗ[ℂ] T.HilbertSpace` |
| `T.hamiltonian ψ` | the map applied to `ψ` (Lean silently coerces the linear map to a function) |
| `E • ψ` | the scalar `E : ℂ` times the vector `ψ` |
| `⟪x, y⟫_ℂ` | the inner product of `x` and `y`, a complex number; conjugate-linear in `x`, linear in `y`. The notation needs `open InnerProductSpace` (already in the file) |
| `(starRingEnd ℂ) z` | the complex conjugate `conj z` = $\bar z$ (Mathlib's name for it) |
| `z.im` | the imaginary part of `z : ℂ`, a real number (`Complex.im z`) |
| `ψ ≠ 0` | `ψ` is not the zero vector (`≠` is `¬ (ψ = 0)`) |
| `↑r` (W3) | the real number `r : ℝ` cast into `ℂ` |
| `?b`, `case hb` | an unknown that `apply` could not fill, and the extra goal it opens for it (Traps) |
| `𝕜`, `[RCLike 𝕜]` | in the full statement of a Mathlib inner-product lemma (hover or `#check`): the scalar field, `ℝ` or `ℂ`. Here always `ℂ` |

---

## Part 1 · `eigenvalue_real`

Statement: for a tight-binding chain `T`, a vector `ψ ≠ 0` and `E : ℂ` with `T.hamiltonian ψ = E • ψ`,
the eigenvalue has imaginary part `0`. Get the hermiticity equation at `φ = ψ` (R1), rewrite it into
scalars (R2–R4), then turn the goal into `conj E = E` (R7) and cancel `⟪ψ, ψ⟫_ℂ` (R6 with R5).

### Getting an equation to work on

**R1 · `have h := T.hamiltonian_hermitian ψ φ`** changes the **context**: it adds the hermiticity
equation. The lemma is
`TightBindingChain.hamiltonian_hermitian (T) (ψ φ : T.HilbertSpace) : ⟪T.hamiltonian ψ, φ⟫_ℂ = ⟪ψ, T.hamiltonian φ⟫_ℂ`.
Writing `T.hamiltonian_hermitian` fills `T` by dot notation; the two vectors are explicit, so you choose
them. Without `: type`, `have` uses the type of the term. Placeholders: `(T : TightBindingChain) (ψ φ : T.HilbertSpace)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, context gains `h : ⟪T.hamiltonian ψ, φ⟫_ℂ = ⟪ψ, T.hamiltonian φ⟫_ℂ` |

**R2 · `rw [hab] at h`** changes the **context**: it rewrites the hypothesis `h` instead of the goal,
replacing every `a` in `h` by `b`. The goal is unchanged. Placeholders: `{α : Type} (a b : α) (hab : a = b)`.

| Before | After |
|---|---|
| `h : P a ⊢ G` | `h : P b ⊢ G` |

### Pulling scalars out of the inner product

**R3 · `rw [inner_smul_left]`** changes the **goal** (with `at h`: the **context**, as in R2). The lemma is
`inner_smul_left (x y : V) (r : ℂ) : ⟪r • x, y⟫_ℂ = (starRingEnd ℂ) r * ⟪x, y⟫_ℂ`: a scalar leaves the
first slot **conjugated**. (Mathlib states it for any scalar field `𝕜` that is `ℝ` or `ℂ`; with `𝕜 = ℂ`
it is the line above.) Placeholders: `{V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x y : V) (r : ℂ)`.
The guide shows it on the goal; in this problem you use it `at h`.

| Before | After |
|---|---|
| `⊢ P ⟪r • x, y⟫_ℂ` | `⊢ P ((starRingEnd ℂ) r * ⟪x, y⟫_ℂ)` |

**R4 · `rw [inner_smul_right]`** changes the **goal** (with `at h`: the **context**). The lemma is
`inner_smul_right (x y : V) (r : ℂ) : ⟪x, r • y⟫_ℂ = r * ⟪x, y⟫_ℂ`: a scalar leaves the second slot
**unchanged**. Placeholders as in R3.

| Before | After |
|---|---|
| `⊢ P ⟪x, r • y⟫_ℂ` | `⊢ P (r * ⟪x, y⟫_ℂ)` |

**W1: R2 → R3 → R4 on one hypothesis.** With `hx : x = c • y` and `h : ⟪x, x⟫_ℂ = 1`, the goal stays

```lean-goal
⊢ (starRingEnd ℂ) c * (c * ⟪y, y⟫_ℂ) = 1
```

while the three rewrites take `h` through:

| Step | `h` becomes |
|---|---|
| start | `h : ⟪x, x⟫_ℂ = 1` |
| `rw [hx] at h` (R2) | `h : ⟪c • y, c • y⟫_ℂ = 1` |
| `rw [inner_smul_left] at h` (R3) | `h : (starRingEnd ℂ) c * ⟪y, c • y⟫_ℂ = 1` |
| `rw [inner_smul_right] at h` (R4) | `h : (starRingEnd ℂ) c * (c * ⟪y, y⟫_ℂ) = 1` |

`rw [hx, inner_smul_left, inner_smul_right] at h` does all three in one line.

### Cancelling and reading off realness

**R7 · `rw [← Complex.conj_eq_iff_im]`** changes the **goal**. The lemma is
`Complex.conj_eq_iff_im {z : ℂ} : (starRingEnd ℂ) z = z ↔ z.im = 0` ("`z` is real iff it equals its
conjugate"). `rw` accepts an `↔`; with `←` it replaces the right side `z.im = 0` by the left side.
Placeholders: `(z : ℂ)`. Term form: `Complex.conj_eq_iff_im.mp hz : z.im = 0` from `hz : (starRingEnd ℂ) z = z`.

| Before | After |
|---|---|
| `⊢ z.im = 0` | `⊢ (starRingEnd ℂ) z = z` |

**R6 · `apply mul_right_cancel₀ hb`** changes the **goal**. The lemma is
`mul_right_cancel₀ : b ≠ 0 → a * b = c * b → a = c`; `a b c` are implicit and Lean finds them from the goal
and from `hb`. Given `hb`, `apply` leaves the equation with the common factor. The lemma needs
`[Mul M₀] [Zero M₀] [IsRightCancelMulZero M₀]` (no zero divisors on the right); every field qualifies, `ℂ`
included. Placeholders: `{K : Type} [Field K] (a b c : K) (hb : b ≠ 0)`.

| Before | After |
|---|---|
| `hb : b ≠ 0 ⊢ a = c` | `hb : b ≠ 0 ⊢ a * b = c * b` |

**R5 · `rw [inner_self_ne_zero]`** changes the **goal**. The lemma is
`inner_self_ne_zero {x : V} : ⟪x, x⟫_ℂ ≠ 0 ↔ x ≠ 0` (positive definiteness of the inner product). Use it to
get the `hb` of R6. Term form: `inner_self_ne_zero.mpr hx : ⟪x, x⟫_ℂ ≠ 0` from `hx : x ≠ 0`
(`.mpr` is the `←` direction of an `↔`). Placeholders: `{V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : V)`.

| Before | After |
|---|---|
| `hx : x ≠ 0 ⊢ ⟪x, x⟫_ℂ ≠ 0` | `hx : x ≠ 0 ⊢ x ≠ 0` |

**W2: cancel a nonzero `⟪y, y⟫_ℂ`.** From `hy : y ≠ 0` and `h : a * ⟪y, y⟫_ℂ = 2 * ⟪y, y⟫_ℂ`, prove `a = 2`:
`have hn : ⟪y, y⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hy` (R5), then, with `hn` in the context,
`apply mul_right_cancel₀ hn` (R6):

| Before | After |
|---|---|
| `⊢ a = 2` | `⊢ a * ⟪y, y⟫_ℂ = 2 * ⟪y, y⟫_ℂ` |

and `exact h` closes it.

**W3: a real cast is real.** For `r : ℝ`, R7 turns `(↑r).im = 0` into a conjugate equation, which
`Complex.conj_ofReal r : (starRingEnd ℂ) ↑r = ↑r` closes:

```lean-goal
⊢ (↑r).im = 0
⊢ (starRingEnd ℂ) ↑r = ↑r
```

---

## Traps

- `⟪x, y⟫_ℂ` is conjugate-linear in the **first** slot: pulling `E` out of `⟪E • ψ, ψ⟫_ℂ` gives
  `(starRingEnd ℂ) E`, not `E` (R3). `inner_smul_right` never matches `⟪E • ψ, ψ⟫_ℂ`: on
  `h : ⟪E • ψ, ψ⟫_ℂ = ⟪ψ, E • ψ⟫_ℂ` it only rewrites the right side, so the left still needs R3.
- `rw [hE] at h` rewrites **both** occurrences of `T.hamiltonian ψ` in `h`; that is what you want. Do it
  before R3/R4, which only match a literal `r • x`.
- `rw [...]` alone rewrites the goal; the hermiticity equation is a hypothesis, so write `at h`.
- `mul_right_cancel₀` cancels a factor on the **right** (`a * b = c * b`). After R3 and R4 the common
  factor `⟪ψ, ψ⟫_ℂ` is on the right of both sides, so this is the matching lemma (`mul_left_cancel₀` is for
  `b * a = b * c`).
- `apply mul_right_cancel₀` without the `≠ 0` argument leaves the factor as an unknown `?b`; pass it.
- `inner_self_ne_zero` and `Complex.conj_eq_iff_im` are `↔`s: use `.mpr`/`.mp` in a term, or `rw` in tactic
  mode. `exact inner_self_ne_zero hψ` is a type error.
- `conj_eigenvalue_eq_self` is BANNED: Mathlib's `LinearMap.IsSymmetric.conj_eigenvalue_eq_self` is this
  theorem for any symmetric operator, so it would hand you `conj E = E`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| hermiticity at `φ = ψ` | `have h := T.hamiltonian_hermitian ψ ψ` | R1 |
| use `hE` inside `h` | `rw [hE] at h` | R2 |
| `⟪r • x, y⟫_ℂ → conj r * ⟪x, y⟫_ℂ` | `rw [inner_smul_left] at h` | R3 |
| `⟪x, r • y⟫_ℂ → r * ⟪x, y⟫_ℂ` | `rw [inner_smul_right] at h` | R4 |
| `x ≠ 0 → ⟪x, x⟫_ℂ ≠ 0` | `inner_self_ne_zero.mpr hx` | R5 |
| `a * b = c * b`, `b ≠ 0` ⟹ `a = c` | `apply mul_right_cancel₀ hb` / `mul_right_cancel₀ hb h` | R6 |
| `z.im = 0` ⟺ `conj z = z` | `rw [← Complex.conj_eq_iff_im]` / `Complex.conj_eq_iff_im.mp` | R7 |
| add a fact | `have hn : T := …` | TACTIC_STATES |
| see the state | infoview | |
