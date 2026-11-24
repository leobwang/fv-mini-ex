# M121 · Condition number bound: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's matrix–vector product `*ᵥ`, the
∞-norm on vectors and the induced operator norm on matrices, and the tactics `calc`, `field_simp`,
`gcongr` for inequalities over `ℝ`.

The math. For a square system with `B A = 1` (`B` is a left inverse of `A`):
`x' - x = B (b' - b)`, so `‖x' - x‖ ≤ ‖B‖ ‖b' - b‖`; and `b = A x`, so `‖b‖ ≤ ‖A‖ ‖x‖`. Multiply:
`‖x' - x‖ · ‖b‖ ≤ ‖A‖ ‖B‖ ‖b' - b‖ · ‖x‖`, then divide by `‖x‖ ‖b‖ > 0`. The number `κ = ‖A‖ ‖B‖` is the
condition number.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : (Fin k → α) → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommRing α]` is a
  requirement on `α` (a *type class*); `ℝ`, `ℚ`, `ℤ`, `ℂ` meet `CommRing`. The lemmas need less (e.g.
  `Matrix.mulVec_sub` only `[NonUnitalNonAssocRing α]`), so they apply to all of these.
- `k : ℕ` is a dimension; `Fin k = {0, …, k-1}` indexes rows, columns and vector entries.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix (Fin n) (Fin n) ℝ` | `n × n` real matrices; `A i j` is the entry in row `i`, column `j` |
| `Fin n → ℝ` | a vector in `ℝⁿ`, as a function from indices to entries |
| `A *ᵥ v` | `Matrix.mulVec A v`: matrix times column vector, `(A *ᵥ v) i = ∑ j, A i j * v j`. Needs `open Matrix` |
| `M *ᵥ N *ᵥ v` | `M *ᵥ (N *ᵥ v)`: `*ᵥ` groups to the right |
| `(M * N) *ᵥ v` | matrix product first, then times `v` |
| `1` (a matrix) | the identity matrix |
| `0` (a vector) | the zero vector, `fun _ => 0` |
| `‖v‖`, `v : Fin n → ℝ` | the sup norm `maxᵢ |v i|` (`0` when `n = 0`) |
| `‖A‖`, `A` a matrix | the ∞-operator norm, `maxᵢ ∑ⱼ |A i j|` (max row sum); it satisfies `‖A *ᵥ v‖ ≤ ‖A‖ ‖v‖` (R8). This meaning is switched on by `open scoped Matrix.Norms.Operator`; without it `‖A‖` does not type-check |
| `a ≠ b` | `a = b → False` |
| `case hbc` | a goal label `gcongr` gives; ignore it |

---

## Part 1 · `relative_error_le_cond`

Statement: for `A B : Matrix (Fin n) (Fin n) ℝ` with `hBA : B * A = 1`, vectors with `hx : A *ᵥ x = b`,
`hx' : A *ᵥ x' = b'` and `hb : b ≠ 0`:
`‖x' - x‖ / ‖x‖ ≤ ‖A‖ * ‖B‖ * (‖b' - b‖ / ‖b‖)`.
Note that `x ≠ 0` is not given: you derive it from `hb`.

### Milestone `x' - x = B *ᵥ (b' - b)`: matrix–vector algebra

After `rw [← hx, ← hx']` (generic `rw ←`) the right side is `B *ᵥ (A *ᵥ x' - A *ᵥ x)`. Then:

**R1 · `rw [← Matrix.mulVec_sub]`** changes the **goal**. The lemma is
`Matrix.mulVec_sub : M *ᵥ (u - v) = M *ᵥ u - M *ᵥ v`; `←` uses it right to left, pulling the common matrix
out of a difference. Placeholders: `{α : Type} [CommRing α] {k : ℕ} (M : Matrix (Fin k) (Fin k) α)
(u v : Fin k → α)`.

| Before | After |
|---|---|
| `⊢ P (M *ᵥ u - M *ᵥ v)` | `⊢ P (M *ᵥ (u - v))` |

**R2 · `rw [Matrix.mulVec_mulVec]`** changes the **goal**. The lemma is
`Matrix.mulVec_mulVec : M *ᵥ N *ᵥ v = (M * N) *ᵥ v`: two matrix–vector products become one with the
matrix product. Placeholders: `(M N : Matrix (Fin k) (Fin k) α) (v : Fin k → α)`.

| Before | After |
|---|---|
| `⊢ P (M *ᵥ N *ᵥ v)` | `⊢ P ((M * N) *ᵥ v)` |

Now `B * A` appears literally, so `rw [hBA]` turns it into `1`.

**R3 · `rw [Matrix.one_mulVec]`** changes the **goal**. The lemma is `Matrix.one_mulVec : 1 *ᵥ v = v`, with
`1` the identity matrix. Placeholders: `(v : Fin k → α)`. If both sides become identical, `rw` closes the
goal by `rfl`.

| Before | After |
|---|---|
| `⊢ P (1 *ᵥ v)` | `⊢ P v` |

### Milestone `x ≠ 0`

**R4 · `rintro rfl`** changes the **goal and the context**. `u ≠ 0` means `u = 0 → False`; `rintro rfl`
introduces the equation `u = 0` and substitutes it, so `u` disappears and every hypothesis that mentioned
it now mentions `0`. Placeholders: `(M : Matrix (Fin k) (Fin k) α) (u w : Fin k → α)`; this works because
`u` is a local variable.

| Before | After |
|---|---|
| `hu : M *ᵥ u = w ⊢ u ≠ 0` | `hu : M *ᵥ 0 = w ⊢ False` |

**R5 · `exact hne e`** **closes** `False`: `hne : a ≠ b` is a function from proofs of `a = b` to `False`, so
apply it. Placeholders: `{β : Type} (a b : β) (hne : a ≠ b) (e : a = b)`. Write `exact hne (by …)` to prove
`a = b` in place: the `by` block starts with goal `⊢ a = b`.

| Before | After |
|---|---|
| `hne : a ≠ b, e : a = b ⊢ False` | no goals |

**R6 · `rw [Matrix.mulVec_zero]`** changes the **goal**. The lemma is `Matrix.mulVec_zero : M *ᵥ 0 = 0`.
Placeholders: `(M : Matrix (Fin k) (Fin k) α)`.

| Before | After |
|---|---|
| `⊢ P (M *ᵥ 0)` | `⊢ P 0` |

### Norm facts

**R7 · `norm_pos_iff`** changes the **goal** when used with `rw`. The lemma is
`norm_pos_iff : 0 < ‖a‖ ↔ a ≠ 0` (for any normed group, vectors `Fin k → ℝ` included). As a term,
`norm_pos_iff.mpr ha : 0 < ‖a‖` from `ha : a ≠ 0` (`.mpr` is the `←` direction of an `↔`). You need
`0 < ‖x‖` for R10 and `0 < ‖b‖` for R12. Placeholders: `(v : Fin k → ℝ)`.

| Before | After |
|---|---|
| `hv : v ≠ 0 ⊢ 0 < ‖v‖` | `hv : v ≠ 0 ⊢ v ≠ 0` |

**R8 · `Matrix.linfty_opNorm_mulVec`** changes the **context** with `have`. The lemma is
`Matrix.linfty_opNorm_mulVec M v : ‖M *ᵥ v‖ ≤ ‖M‖ * ‖v‖`, the defining property of an operator norm. It
needs `open scoped Matrix.Norms.Operator`. Placeholders: `(M : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ)`.
You need it twice: once with `B` and `b' - b`, once with `A` and `x`.

| Before | After |
|---|---|
| `⊢ G` | `hb : ‖M *ᵥ v‖ ≤ ‖M‖ * ‖v‖ ⊢ G` |

**R9 · `h ▸ e`** is a **term**: with `h : a = b` and `e : P a`, `h ▸ e : P b`. Lean tries both directions
of `h`, so it also turns `e : P b` into `P a`. Use it to rewrite R8's bound with a milestone equation, e.g.
`(h : w = M *ᵥ v) ▸ (bound on ‖M *ᵥ v‖)` gives a bound on `‖w‖`. The tactic version is `rw [h] at e`,
which changes the **context**. Placeholders: `{β : Type} (a b : β) (P : β → Prop)`.

| Before `rw [h] at e` | After |
|---|---|
| `e : P a ⊢ P b` | `e : P b ⊢ P b` |

### Clearing the denominator and the `calc` chain

**R10 · `rw [div_le_iff₀ hc]`** changes the **goal**. The lemma is
`div_le_iff₀ : 0 < c → (b / c ≤ a ↔ b ≤ a * c)`; pass the positivity proof (R7). Placeholders:
`(a b c : ℝ) (hc : 0 < c)`. Only the **left** side's denominator is cleared; the quotient on the right
stays.

| Before | After |
|---|---|
| `⊢ b / c ≤ a` | `⊢ b ≤ a * c` |

**R11 · `calc`** changes the **goal list**: it proves `a ≤ d` through a chain
`calc a ≤ b := p₁` / `_ = c := p₂` / `_ ≤ d := p₃`, each step with its own proof (`by …` allowed). `≤` and
`=` compose to `≤`. Indent the `_` lines further than `calc`. The first term and the last must be the
goal's two sides (up to unfolding). Placeholders: `(a b c d : ℝ)`.

| Before | After |
|---|---|
| `h1 : a ≤ b, h2 : b = c, h3 : c ≤ d ⊢ a ≤ d` | no goals |

**R12 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero, using
hypotheses `hc : c ≠ 0` or `hc : 0 < c`, and normalises. It may reorder factors (`b * c` becomes `c * b`),
and it closes the goal when the cleared sides agree. Use it for the `calc` step that writes `q` as
`q / c * c`. Placeholders: `(a b c d : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ a / c + b = d` | `⊢ a + c * b = c * d` |

**R13 · `gcongr`** changes the **goal**: for `L ≤ R` where `L` and `R` have the same shape and differ in one
place, it reduces to the inequality between the differing parts. Side goals such as `0 ≤ c` for the fixed
factor are closed automatically (by `positivity`, which knows norms and quotients of norms are `≥ 0`). If
the remaining goal is a hypothesis, `gcongr` closes it too. Placeholders:
`(u : Fin k → ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ ‖u‖ * a ≤ ‖u‖ * b` | `⊢ a ≤ b` |

The last `calc` step (move `‖A‖` to the front, regroup) is plain `ring`: it treats each `‖·‖` as an
unknown, so `ring` proves any rearrangement of a product of norms.

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a left inverse inside a difference.** With `hCD : C * D = 1`, prove
`C *ᵥ (D *ᵥ u - D *ᵥ v) = u - v` by R1, R2, `rw [hCD]`, R3:

```lean-goal
⊢ C *ᵥ (D *ᵥ u - D *ᵥ v) = u - v
⊢ C *ᵥ D *ᵥ (u - v) = u - v
⊢ (C * D) *ᵥ (u - v) = u - v
⊢ 1 *ᵥ (u - v) = u - v
```

**W2: a ratio bound.** R10 then R8:

```lean-goal
⊢ ‖M *ᵥ v‖ / ‖v‖ ≤ ‖M‖
⊢ ‖M *ᵥ v‖ ≤ ‖M‖ * ‖v‖
```

**W3: `calc` with `field_simp` and `gcongr`.** From `hv : 0 < ‖v‖` and `hw : ‖v‖ ≤ ‖w‖`, prove
`‖u‖ ≤ ‖u‖ / ‖v‖ * ‖w‖` as `calc ‖u‖ = ‖u‖ / ‖v‖ * ‖v‖ := by field_simp` then
`_ ≤ ‖u‖ / ‖v‖ * ‖w‖ := by gcongr` (R11, R12, R13; `gcongr` finds `hw` itself).

```lean-goal
⊢ ‖u‖ ≤ ‖u‖ / ‖v‖ * ‖w‖
```

---

## Traps

- `*ᵥ` groups to the right: the infoview's `B *ᵥ A *ᵥ v` is `B *ᵥ (A *ᵥ v)`, exactly the form R2 wants.
- `rw [← hx]` replaces **every** `b` in the goal by `A *ᵥ x`. Rewrite before you introduce other terms that
  contain `b`.
- `rintro rfl` needs one side of the equation to be a local variable (`x`, not `A *ᵥ x`).
- `div_le_iff₀` needs `0 < c`, not `c ≠ 0`; prove positivity first with R7.
- `field_simp` needs the nonzero facts in the context **before** it runs (`have hbpos : 0 < ‖b‖ := …`).
- `gcongr` needs both sides to have the same shape; write the intermediate `calc` term so that only one
  factor differs.
- Without `open scoped Matrix.Norms.Operator`, `‖A‖` for a matrix has no meaning (no instance is found).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| replace `b` by `A *ᵥ x` | `rw [← hx]` | generic |
| `M *ᵥ u - M *ᵥ v → M *ᵥ (u - v)` | `rw [← Matrix.mulVec_sub]` | R1 |
| `M *ᵥ N *ᵥ v → (M * N) *ᵥ v` | `rw [Matrix.mulVec_mulVec]` | R2 |
| `1 *ᵥ v → v` | `rw [Matrix.one_mulVec]` | R3 |
| prove `u ≠ 0` | `rintro rfl` | R4 |
| use `hne : a ≠ b` | `exact hne (by …)` | R5 |
| `M *ᵥ 0 → 0` | `rw [Matrix.mulVec_zero]` | R6 |
| `0 < ‖v‖` from `v ≠ 0` | `norm_pos_iff.mpr hv` | R7 |
| `‖M *ᵥ v‖ ≤ ‖M‖ * ‖v‖` | `Matrix.linfty_opNorm_mulVec M v` | R8 |
| rewrite a term's type | `h ▸ e` / `rw [h] at e` | R9 |
| `b / c ≤ a → b ≤ a * c` | `rw [div_le_iff₀ hc]` | R10 |
| chain of `≤` and `=` | `calc` | R11 |
| clear denominators | `field_simp` | R12 |
| enlarge one factor | `gcongr` | R13 |
| rearrange a product | `ring` | generic |
| see the state | infoview | |
