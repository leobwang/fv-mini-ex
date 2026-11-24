# E127 · Divergence of the position field: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `Space d`, its standard basis
`basis`, the partial derivative `∂[i]` and the divergence `∇ ⬝`; Mathlib's `EuclideanSpace`, finite sums
`∑`, `Finset.univ` and its size, `ℕ`-scalar multiplication `•`, and the cast `↑d : ℝ`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid M]`
  is a requirement on `M` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Space d` | a point of ℝᵈ: a structure with one field `val : Fin d → ℝ`. `Space` alone is `Space 3` |
| `x.val i` | the `i`-th coordinate of the point `x` (`i : Fin d`, counted from 0) |
| `EuclideanSpace ℝ (Fin d)` | Mathlib's ℝᵈ with the Euclidean norm; its elements are wrapped functions `Fin d → ℝ` |
| `v.ofLp i` | entry `i` of `v : EuclideanSpace ℝ (Fin d)`; you write `v i`, the infoview prints `v.ofLp i` |
| `basis`, `basis.repr y` | physlib's standard orthonormal basis of `Space d`; `basis.repr y` is the coordinate vector of `y` in `EuclideanSpace ℝ (Fin d)`. So `fun y => basis.repr y` is the field $\vec x \mapsto \vec x$ |
| `∂[i] f x`, printed `Space.deriv i f x` | the partial derivative $\partial f / \partial x_i$ at `x` |
| `∇ ⬝ f`, printed `div f x` (with `open Space`) | the divergence $\nabla\cdot f = \sum_i \partial f_i/\partial x_i$, `Space.div f` |
| `∑ i, g i` | Mathlib's finite sum over every `i : Fin d`; short for `∑ i ∈ Finset.univ, g i` |
| `∑ x_1, …` | the same sum; Lean renamed the bound index to `x_1` because `x` is already taken |
| `Finset.univ` | the finite set of all elements of a finite type; `Finset.univ.card` is its size |
| `Fintype.card α` | the number of elements of the finite type `α` |
| `n • a` | `n : ℕ` copies of `a` added together (`ℕ`-scalar multiplication) |
| `↑d` | the natural number `d` cast into `ℝ` (the right side of the spec is this cast) |

---

## Part 1 · `div_position`

Statement: `(∇ ⬝ (fun y => basis.repr y)) x = ↑d`. In maths, $\nabla\cdot\vec x = \sum_{i<d} \partial x_i/\partial x_i
= \sum_{i<d} 1 = d$. The proof follows that line exactly: unfold (R1), read off coordinates and
differentiate (R2–R4), count (R5–R9).

### Divergence → a sum of Kronecker deltas

**R1 · `rw [Space.div]`** changes the **goal**: the divergence is unfolded to its definition
`Space.div f x = ∑ i, ∂[i] (fun x => (f x).ofLp i) x`. Placeholders:
`{d : ℕ} (f : Space d → EuclideanSpace ℝ (Fin d)) (x : Space d)`.

| Before | After |
|---|---|
| `⊢ P (div f x)` | `⊢ P (∑ i, Space.deriv i (fun x => (f x).ofLp i) x)` |

**R2 · `simp only [Space.basis_repr_apply]`** changes the **goal**. The lemma is
`Space.basis_repr_apply : (basis.repr p).ofLp i = p.val i`: entry `i` of the coordinate vector is the
coordinate. Placeholders: `{d : ℕ} (μ : Fin d)`. The term sits under `fun y =>`, so use `simp only`; `rw`
fails with "did not find an occurrence of the pattern" because its pattern mentions the bound `y`.

| Before | After |
|---|---|
| `⊢ P fun y => (basis.repr y).ofLp μ` | `⊢ P fun y => y.val μ` |

**R3 · `Space.deriv_component`** changes the **goal**. The lemma is
`Space.deriv_component : ∂[ν] (fun x => x.val μ) x = if ν = μ then 1 else 0`, the Kronecker delta
$\partial x_\mu/\partial x_\nu = \delta_{\nu\mu}$. Placeholders: `{d : ℕ} (μ ν : Fin d) (x : Space d)`. Shown with
`rw`; in the exercise it sits inside `∑ i, …`, so put it in the same `simp only [...]` as R2. When both
indices are the same variable `i`, `simp` rewrites `i = i` to `True` by itself.

| Before | After |
|---|---|
| `⊢ P (Space.deriv ν (fun y => y.val μ) x)` | `⊢ P (if ν = μ then 1 else 0)` |

**R4 · `if_true`** changes the **goal**. The lemma is `if_true : (if True then a else b) = a`.
Placeholders: `{α : Type} (a b : α)`. Add it to the `simp only [...]` of R2, R3.

| Before | After |
|---|---|
| `⊢ P (if True then a else b)` | `⊢ P a` |

After R1–R4 the goal is `∑ x, 1 = ↑d`: a sum of `d` ones in `ℝ`.

### A sum of ones → its number of terms

**R5 · `rw [Finset.sum_const]`** changes the **goal**. The lemma is
`Finset.sum_const : ∑ _x ∈ s, b = s.card • b`: a sum of a constant is (number of terms) `•` constant.
`∑ _i : ι, b` means `s = Finset.univ`. Placeholders: `{ι M : Type} [Fintype ι] [AddCommMonoid M] (b : M)`
(`ι` is finite, as `Fin d` is; `M` has a commutative `+` and `0`, as `ℝ` has).

| Before | After |
|---|---|
| `⊢ P (∑ _i, b)` | `⊢ P (Finset.univ.card • b)` |

**R6 · `rw [Finset.card_univ]`** changes the **goal**. The lemma is
`Finset.card_univ : Finset.univ.card = Fintype.card α`. Placeholders: `{α : Type} [Fintype α]`.

| Before | After |
|---|---|
| `⊢ P Finset.univ.card` | `⊢ P (Fintype.card α)` |

**R7 · `rw [Fintype.card_fin]`** changes the **goal**. The lemma is `Fintype.card_fin : Fintype.card (Fin n) = n`.
Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Fintype.card (Fin n))` | `⊢ P n` |

**R8 · `rw [nsmul_eq_mul]`** changes the **goal**. The lemma is `nsmul_eq_mul : n • a = ↑n * a`: `n` copies
of `a` is the cast `↑n` times `a`. Placeholders: `{α : Type} [NonAssocSemiring α] (n : ℕ) (a : α)` (`α` has
`+`, `*`, `0`, `1` with the usual laws, not necessarily commutative `*`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (n • a)` | `⊢ P (↑n * a)` |

**R9 · `rw [mul_one]`** changes the **goal**, and here **closes** it: after the rewrite the goal is
`↑d = ↑d`, which `rw` closes by `rfl`. The lemma is `mul_one : a * 1 = a`. Placeholders:
`{α : Type} [MulOneClass α] (a : α)` (`α` has `*` with unit `1`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a constant sum of twos.** `∑ _i : Fin n, (2 : ℝ) = ↑n * 2` with R5, R6, R7, R8; the last `rw` closes
`↑n * 2 = ↑n * 2` by `rfl`:

```lean-goal
⊢ ∑ _i, 2 = ↑n * 2
⊢ Finset.univ.card • 2 = ↑n * 2
⊢ Fintype.card (Fin n) • 2 = ↑n * 2
⊢ n • 2 = ↑n * 2
```

**W2: an off-diagonal partial derivative in `Space 3`.** `∂[0] (fun y => basis.repr y 1) x = 0`. One
`simp only [Space.basis_repr_apply, Space.deriv_component]` does R2 and R3; `simp` then decides `0 = 1` is
false in `Fin 3` and closes the goal:

```lean-goal
⊢ Space.deriv 0 (fun y => (basis.repr y).ofLp 1) x = 0
⊢ (if 0 = 1 then 1 else 0) = 0
```

**W3: `simp` alone** closes W1's goal `∑ _i : Fin n, (2 : ℝ) = ↑n * 2`, doing R5–R8 in one step. The
explicit `rw` chain of W1 shows what it did; on a sum of ones `simp` also does R9.

---

## Traps

- `rw [Space.basis_repr_apply]` fails: the coordinate sits under `fun y =>` inside `∂[i]` and `∑`, and `rw`
  cannot rewrite a pattern containing a bound variable. Use `simp only [...]` (R2).
- The right side `d` of the statement is the cast `↑d : ℝ`, not the natural number. R8 produces `↑n * 1`
  with the same cast, so the chain ends in `↑d = ↑d`.
- `Finset.sum_const` is stated for `∑ _x ∈ s, b`; `∑ x, 1` over `Fin d` is the case `s = Finset.univ`, so
  R5 leaves `Finset.univ.card`, which needs R6 and R7 to become `d`.
- If you type `Finset.univ.card` yourself (in a `have` or `show`) with nothing fixing the element type,
  Lean fails with "typeclass instance problem is stuck": write `(Finset.univ : Finset (Fin d)).card`.
- `∂[i]` and `∇ ⬝` never appear in the infoview: look for `Space.deriv i` and `div`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold `∇ ⬝ f` | `rw [Space.div]` | R1 |
| `(basis.repr y) i` → `y.val i` (under binders) | `simp only [Space.basis_repr_apply]` | R2 |
| `∂[ν] (fun x => x.val μ) x` → Kronecker delta | `Space.deriv_component` (in the same `simp only`) | R3 |
| `if True then a else b` → `a` | `if_true` (in the same `simp only`) | R4 |
| `∑ _x ∈ s, b` → `s.card • b` | `rw [Finset.sum_const]` | R5 |
| `Finset.univ.card` → `Fintype.card α` | `rw [Finset.card_univ]` | R6 |
| `Fintype.card (Fin n)` → `n` | `rw [Fintype.card_fin]` | R7 |
| `n • a` → `↑n * a` | `rw [nsmul_eq_mul]` | R8 |
| `a * 1` → `a` | `rw [mul_one]` | R9 |
| constant sum over `Fin n` → `↑n * b`, all at once | `simp` | W3 |
| see the state | infoview | |
