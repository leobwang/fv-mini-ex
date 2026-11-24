# E111 · Kronecker products of gates: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033); `rw [h]` and `rw [← h]` (TACTIC_STATES, "Rewriting").
**New here:** Mathlib's matrices indexed by arbitrary finite types, the Kronecker product `⊗ₖ`
(`Matrix.kroneckerMap`) and its mixed-product rule, and how `rw` picks which occurrence to rewrite.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommSemiring α]` is
  a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℂ` | the complex numbers (Mathlib's `Complex`) |
| `Matrix m m ℂ` | square matrices with complex entries whose rows and columns are indexed by the type `m`; a matrix *is* a function `m → m → ℂ` |
| `[Fintype m]` | `m` is finite, so the sums in a matrix product `∑ j, M i j * N j k` make sense |
| `[DecidableEq m]` | equality on `m` can be decided, so the identity `1 i j = if i = j then 1 else 0` can be defined |
| `inst✝³ : Fintype m` (context) | an unnamed bracket assumption from the statement (`[Fintype m]`, `[DecidableEq n]`, …); Lean uses it automatically, you never mention it |
| `1` (a matrix) | the identity matrix of the size the context demands |
| `m × n` | pairs `(i, k)` with `i : m`, `k : n`; the index type of a two-part system |
| `A ⊗ₖ B` | the Kronecker product, typed `\otimes\_k`, available after `open scoped Kronecker`. For `A : Matrix m m ℂ`, `B : Matrix n n ℂ` it is a `Matrix (m × n) (m × n) ℂ`: `A` acts on the first part, `B` on the second (physicists write $A \otimes B$) |
| `kroneckerMap (fun x1 x2 => x1 * x2) A B` | how the infoview prints `A ⊗ₖ B`. `Matrix.kroneckerMap f A B` combines every entry of `A` with every entry of `B` through `f`; with `f = (· * ·)` it is `⊗ₖ` |
| `(A ⊗ₖ B) (i, k) (j, l)` | the entry `A i j * B k l` (W3, `Matrix.kronecker_apply`) |
| `A ⊗ₖ B * C ⊗ₖ D` | `(A ⊗ₖ B) * (C ⊗ₖ D)`: `⊗ₖ` binds tighter than `*` |
| `A * B * C` | `(A * B) * C`: `*` groups to the left |

---

## Part 1 · `kron_involution`

Statement: for finite index types `m, n`, `A : Matrix m m ℂ`, `B : Matrix n n ℂ` with `A * A = 1` and
`B * B = 1` (both are involutions, like the Pauli gates), `(A ⊗ₖ B) * (A ⊗ₖ B) = 1`. In math:
$(A \otimes B)^2 = A^2 \otimes B^2 = 1 \otimes 1 = 1$. The sizes are unknown, so no entry computation:
three rewrites.

**R1 · `rw [← Matrix.mul_kronecker_mul]`** changes the **goal**. The lemma (the *mixed-product rule*) is
`Matrix.mul_kronecker_mul : (A * C) ⊗ₖ (B * D) = A ⊗ₖ B * C ⊗ₖ D` (Mathlib's own variable names are
`A B A' B'`; `#check` prints both sides with `kroneckerMap`); `←` uses it right to left, so a
product of two Kronecker products becomes one Kronecker product of two products. `rw` rewrites the first
product of that shape it finds (and every identical copy); call it once per distinct product.
Placeholders: `{α : Type} [CommSemiring α]` (commutative `+` and `*` with `0`, `1`; `ℕ`, `ℤ`, `ℝ`, `ℂ`
qualify), `{k l : Type} [Fintype k] [Fintype l]`, `(A C : Matrix k k α) (B D : Matrix l l α)`. The lemma
also holds for rectangular matrices.

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A B * kroneckerMap (fun x1 x2 => x1 * x2) C D)` | `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) (A * C) (B * D))` |

In the exercise's notation: `⊢ P (A ⊗ₖ B * C ⊗ₖ D)` becomes `⊢ P ((A * C) ⊗ₖ (B * D))`. After R1 the
factors `A * A` and `B * B` sit literally inside the goal, so `rw [hA]` and `rw [hB]` find them.

**R2 · `rw [Matrix.one_kronecker_one]`** changes the **goal**. The lemma is
`Matrix.one_kronecker_one : 1 ⊗ₖ 1 = 1`: the identity on each part gives the identity on the pair.
Placeholders: `{α : Type} [MulZeroOneClass α]` (`*` with `0` and `1`; every type above qualifies),
`{k l : Type} [DecidableEq k] [DecidableEq l]`.

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) 1 1)` | `⊢ P 1` |

When the goal becomes `1 = 1`, `rw` closes it by itself (it tries `rfl` after rewriting).

**W1 (three gates, not the exercise's).** R1 twice merges `(A ⊗ₖ B) * (C ⊗ₖ D) * (E ⊗ₖ F)`. `*` groups to
the left, so the first call merges the inner product and the second merges the result with `E ⊗ₖ F`; the
second `rw` then closes the goal by `rfl`:

```lean-goal
⊢ kroneckerMap (fun x1 x2 => x1 * x2) A B * kroneckerMap (fun x1 x2 => x1 * x2) C D * kroneckerMap (fun x1 x2 => x1 * x2) E F = kroneckerMap (fun x1 x2 => x1 * x2) (A * C * E) (B * D * F)
⊢ kroneckerMap (fun x1 x2 => x1 * x2) (A * C) (B * D) * kroneckerMap (fun x1 x2 => x1 * x2) E F = kroneckerMap (fun x1 x2 => x1 * x2) (A * C * E) (B * D * F)
```

---

## Part 2 · `local_gates_commute`

Statement: `(A ⊗ₖ 1) * (1 ⊗ₖ B) = (1 ⊗ₖ B) * (A ⊗ₖ 1)`. A gate on the first part commutes with a gate on
the second, because both sides equal $A \otimes B$. Merge each side with R1 (two calls: the left product
and the right product are different, so one `rw` only rewrites one of them), then remove the identity
factors with R3 and R4.

**R3 · `rw [Matrix.mul_one]`** changes the **goal**. The lemma is `Matrix.mul_one : M * 1 = M`.
Placeholders: `{α : Type} [NonAssocSemiring α]` (`+`, `*`, `0`, `1` with distributivity; `ℂ` qualifies),
`{k : Type} [Fintype k] [DecidableEq k]`, `(M : Matrix k k α)`.

| Before | After |
|---|---|
| `⊢ P (M * 1)` | `⊢ P M` |

**R4 · `rw [Matrix.one_mul]`** changes the **goal**. The lemma is `Matrix.one_mul : 1 * M = M`. Placeholders
as in R3.

| Before | After |
|---|---|
| `⊢ P (1 * M)` | `⊢ P M` |

`rw [Matrix.mul_one]` fixes `M` at the first `_ * 1` it meets and rewrites only copies of that one. After
merging both sides there are four different identity factors (`A * 1`, `1 * B`, `1 * A`, `B * 1`), so you
need one `rw` per factor, or `simp only [Matrix.mul_one, Matrix.one_mul]`, which rewrites them all.

**W2 (two gates on the first part, not the exercise's).** R1 leaves `1 * 1` in the second slot; R4 removes
it and `rw` closes the goal by `rfl`:

```lean-goal
⊢ kroneckerMap (fun x1 x2 => x1 * x2) A 1 * kroneckerMap (fun x1 x2 => x1 * x2) C 1 = kroneckerMap (fun x1 x2 => x1 * x2) (A * C) 1
⊢ kroneckerMap (fun x1 x2 => x1 * x2) (A * C) (1 * 1) = kroneckerMap (fun x1 x2 => x1 * x2) (A * C) 1
```

**W3 (what `⊗ₖ` is).** `rw [Matrix.kronecker_apply]` turns an entry of a Kronecker product into a product
of entries. Not needed here (no entries are computed), but it is the definition behind R1–R2:

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A B (i, a) (j, b))` | `⊢ P (A i j * B a b)` |

---

## Traps

- You write `A ⊗ₖ B`, the infoview shows `kroneckerMap (fun x1 x2 => x1 * x2) A B`. Same term; read it as
  `A ⊗ₖ B`.
- `rw [Matrix.mul_kronecker_mul]` (no `←`) looks for `(_ * _) ⊗ₖ (_ * _)`, which is not in the goal at the
  start: `rewrite` fails with "Did not find an occurrence of the pattern". The goal has the right-hand side,
  so write `←`.
- One `rw [← Matrix.mul_kronecker_mul]` merges one product. In Part 2 the two sides are different products:
  rewrite twice.
- `rw [hA]` before R1 fails: `A * A` does not occur in `A ⊗ₖ B * A ⊗ₖ B`; only R1 creates it.
- `⊗ₖ` needs `open scoped Kronecker` (the problem file has it). Without it, `⊗ₖ` is a parse error.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `(A ⊗ₖ B) * (C ⊗ₖ D) → (A * C) ⊗ₖ (B * D)` | `rw [← Matrix.mul_kronecker_mul]` | R1 |
| use `A * A = 1` inside a factor | `rw [hA]` (after R1) | TACTIC_STATES |
| `1 ⊗ₖ 1 → 1` | `rw [Matrix.one_kronecker_one]` | R2 |
| `M * 1 → M` | `rw [Matrix.mul_one]` | R3 |
| `1 * M → M` | `rw [Matrix.one_mul]` | R4 |
| all identity factors at once | `simp only [Matrix.mul_one, Matrix.one_mul]` | R3, R4 |
| entry of `A ⊗ₖ B` | `rw [Matrix.kronecker_apply]` | W3 |
| finish `X = X` | nothing: `rw` closes it by `rfl` | |
| see the state | infoview | |
