# E070 · Products and Fin sums: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033) and E042 (sums `∑ i ∈ range n, f i`, `Finset.sum_range_succ`).
**New here:** Mathlib's finite products `∏`, the constant-product and cardinality lemmas, sums over a whole
`Fin n` (`∑ i, g i`), and the cast `↑i : ℕ` of an index `i : Fin n`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{M : Type}` is any type. A bracket such as `[CommMonoid M]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `range n` | `Finset.range n`, the finite set `{0, 1, …, n - 1}` of naturals (printed without `Finset.` because of `open Finset`) |
| `∏ i ∈ range n, f i` | the product `f 0 * f 1 * … * f (n - 1)`; empty product `= 1`. Typed `\prod` |
| `∏ _i ∈ s, b` | a product whose factor `b` does not depend on the index (`_i` marks it unused) |
| `#s` | `Finset.card s`, the number of elements of the finset `s` (notation from `open Finset`) |
| `Fin n` | the type of naturals `< n`; its elements are `0, 1, …, n - 1` |
| `ℝ` | Mathlib's real numbers (`Real`); `g : Fin 3 → ℝ` gives a real number for each index |
| `∑ i, g i` | for `g : Fin n → M`: the sum over **every** `i : Fin n` (over the finset `Finset.univ`) |
| `∑ i : Fin n, g i` | the same, with the index type written out |
| `↑i`, `(i : ℕ)` | `Fin.val i`, the value of `i : Fin n` as a natural number (a cast, or *coercion*) |
| `i.succ` | `Fin.succ i : Fin (n + 1)`, the index one higher than `i : Fin n` |
| `↑0` | the cast of `0 : Fin (n + 1)`; it equals `0 : ℕ` (R9) but is not written as `0` until rewritten |

---

## Part 1 · `prod_four`

Statement: `∏ i ∈ range 4, (i + 1) = 24`, i.e. `1 · 2 · 3 · 4 = 24` in `ℕ`.

**R1 · `decide`** **closes** a statement Lean can evaluate: a product over `range k` with a numeral `k` and
natural-number factors is computed, then the two numerals are compared.

| Before | After |
|---|---|
| `⊢ ∏ i ∈ range 3, (2 * i + 1) = 15` | no goals |

---

## Part 2 · `prod_peel`

Statement: for every `n : ℕ`, `∏ i ∈ range (n + 1), (i + 1) = (n + 1) * ∏ i ∈ range n, (i + 1)`: peel the last
factor and put it in front.

**R2 · `rw [Finset.prod_range_succ]`** changes the **goal**. The lemma is
`Finset.prod_range_succ (f : ℕ → M) (n : ℕ) : ∏ x ∈ range (n + 1), f x = (∏ x ∈ range n, f x) * f n`, the
product version of E042's `sum_range_succ`: the last factor `f n` comes off **on the right**.
Placeholders: `{M : Type} [CommMonoid M]` (`M` has an associative, commutative `*` with `1`; `ℕ`, `ℤ`, `ℝ`
qualify), `(f : ℕ → M) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (∏ x ∈ range (n + 1), f x)` | `⊢ P ((∏ x ∈ range n, f x) * f n)` |

**R3 · `rw [mul_comm]`** changes the **goal**. The lemma is `mul_comm (a b : M) : a * b = b * a`. Without
arguments, `rw` uses the first product it finds (in the left-hand side, outermost first) as `a * b` and
rewrites every copy of it. After rewriting, `rw` tries `rfl`, so it closes the goal when both sides now match.
Placeholders: `{M : Type} [CommMonoid M] (a b : M)` (any commutative `*`).

| Before | After |
|---|---|
| `⊢ P (a * b)` | `⊢ P (b * a)` |

**W1.** Peel and swap a different product. After R2 the factor sits on the wrong side; R3 swaps it and closes
the goal:

```lean-goal
⊢ ∏ i ∈ range (n + 1), (2 * i + 1) = (2 * n + 1) * ∏ i ∈ range n, (2 * i + 1)
⊢ (∏ x ∈ range n, (2 * x + 1)) * (2 * n + 1) = (2 * n + 1) * ∏ i ∈ range n, (2 * i + 1)
```

---

## Part 3 · `prod_const_two`

Statement: `∏ _i ∈ range n, (2 : ℕ) = 2 ^ n`: `n` factors of `2`.

**R4 · `rw [Finset.prod_const]`** changes the **goal**. The lemma is
`Finset.prod_const (b : M) : ∏ _x ∈ s, b = b ^ #s`: a product of a constant over `s` is `b` to the power of the
number of elements of `s`. Placeholders: `{ι M : Type} [CommMonoid M] (s : Finset ι) (b : M)`.

| Before | After |
|---|---|
| `⊢ P (∏ _x ∈ s, b)` | `⊢ P (b ^ #s)` |

**R5 · `rw [Finset.card_range]`** changes the **goal**. The lemma is `Finset.card_range (n : ℕ) : #(range n) = n`.
Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P #(range n)` | `⊢ P n` |

**W2.** `(∏ _i ∈ range n, (3 : ℤ)) * 3 = 3 ^ (n + 1)`: R4, R5, then `rw [pow_succ]`
(`a ^ (n + 1) = a ^ n * a`) makes both sides equal and `rw` closes the goal:

```lean-goal
⊢ (∏ _i ∈ range n, 3) * 3 = 3 ^ (n + 1)
⊢ 3 ^ #(range n) * 3 = 3 ^ (n + 1)
⊢ 3 ^ n * 3 = 3 ^ (n + 1)
```

---

## Part 4 · `sum_fin_three`

Statement: for `g : Fin 3 → ℝ`, `∑ i, g i = g 0 + g 1 + g 2`: a sum over all of `Fin 3`, written out.

**R6 · `Fin.sum_univ_three`** changes the **goal**. The lemma is
`Fin.sum_univ_three (f : Fin 3 → M) : ∑ i, f i = f 0 + f 1 + f 2`. Use it with `rw`, or as a proof term: a
lemma applied to its arguments *is* a proof of its statement (E004), so `exact Fin.sum_univ_three f` closes a
goal that is exactly that statement. Placeholders: `{M : Type} [AddCommMonoid M]` (`M` has an associative,
commutative `+` with `0`; `ℕ`, `ℤ`, `ℝ` qualify), `(f : Fin 3 → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1 + f 2)` |

There are also `Fin.sum_univ_two`, `Fin.sum_univ_four`, … with the same shape.

**W3.** `∑ i : Fin 3, ((i : ℕ) + 1) = 6`: R6, then `decide` (R1) evaluates the numerals in `ℕ`:

```lean-goal
⊢ ∑ i, (↑i + 1) = 6
⊢ ↑0 + 1 + (↑1 + 1) + (↑2 + 1) = 6
```

---

## Part 5 · `sum_fin_succ`

Statement: for `g : ℕ → ℝ`, `∑ i : Fin (n + 1), g i = g 0 + ∑ i : Fin n, g ((i : ℕ) + 1)`. On the left, `g i`
means `g ↑i`: `g` takes a natural number, so the index is cast. Peel the `0` term; then the two sides differ
only in how the index is written (`↑0` vs `0`, `↑i.succ` vs `↑i + 1`).

**R7 · `rw [Fin.sum_univ_succ]`** changes the **goal**. The lemma is
`Fin.sum_univ_succ (f : Fin (n + 1) → M) : ∑ i, f i = f 0 + ∑ i : Fin n, f i.succ`: the first term comes off,
and the rest is a sum over the smaller type `Fin n` with every index shifted up by `Fin.succ`.
Placeholders: `{M : Type} [AddCommMonoid M] (n : ℕ) (f : Fin (n + 1) → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + ∑ i, f i.succ)` |

**R8 · `Fin.val_succ`** changes the **goal**. The lemma is `Fin.val_succ (j : Fin n) : ↑j.succ = ↑j + 1`: the
value of the next index is the value plus one, computed in `ℕ`. `simp` uses it by itself.
Placeholders: `(n : ℕ) (j : Fin n)`.

| Before | After |
|---|---|
| `⊢ P ↑j.succ` | `⊢ P (↑j + 1)` |

**R9 · `Fin.val_zero`** changes the **goal**. The lemma is `Fin.val_zero : ↑(0 : Fin (n + 1)) = 0`. `simp`
reaches the same result by its own lemmas (`Fin.coe_ofNat_eq_mod`, `Nat.zero_mod`: `↑0 = 0 % (n + 1) = 0`).
Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑0` | `⊢ P 0` |

**W4.** `∑ i : Fin (n + 1), (i : ℕ) = ∑ i : Fin n, ((i : ℕ) + 1)`: R7 peels the `0` term; then `simp` applies
R9 and R8 under the `∑` (and `0 + x = x`) and closes the goal:

```lean-goal
⊢ ∑ i, ↑i = ∑ i, (↑i + 1)
⊢ ↑0 + ∑ i, ↑i.succ = ∑ i, (↑i + 1)
```

`rw [Fin.val_succ]` alone would fail here: the `↑i.succ` sits under the binder `∑ i, …`, and `rw` cannot
rewrite a term that mentions a bound variable. `simp` can.

In `sum_fin_succ` the same goes for the explicit form: `simp only [Fin.val_zero, Fin.val_succ]` (R9, R8) also
closes the goal left by R7. `rw [Fin.val_zero]` alone does work there, because `g ↑0` is outside the `∑`.

---

## Traps

- In `sum_fin_succ`, `g ((i : ℕ) + 1)` adds **in `ℕ` after the cast**. It is not `g ↑(i + 1)` with `Fin`
  addition, which wraps around (in `Fin 3`, `2 + 1 = 0`). `Fin.val_succ` is what connects `↑i.succ` to
  `↑i + 1`.
- `rw` cannot rewrite under a binder (`∑ i, …`, `∏ i ∈ s, …`, `fun i => …`) when the term mentions the bound
  `i`; use `simp` or `simp only [lemma]` there (W4).
- `prod_range_succ` puts the last factor on the **right**; the statement of `prod_peel` has it on the left, hence
  R3.
- `decide` only works when Lean can compute everything: numerals in `ℕ`, a numeral range. It fails on `ℝ`
  (Part 4, Part 5) and on a variable `n` (Parts 2, 3).
- `#s` is notation from `open Finset`; without it Lean prints `s.card`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| closed product in `ℕ` | `decide` | R1 |
| `∏ x ∈ range (n + 1), f x` → `(∏ x ∈ range n, f x) * f n` | `rw [Finset.prod_range_succ]` | R2 |
| `a * b` → `b * a` | `rw [mul_comm]` | R3 |
| `∏ _x ∈ s, b` → `b ^ #s` | `rw [Finset.prod_const]` | R4 |
| `#(range n)` → `n` | `rw [Finset.card_range]` | R5 |
| `∑ i : Fin 3, f i` → `f 0 + f 1 + f 2` | `rw [Fin.sum_univ_three]` or `exact Fin.sum_univ_three f` | R6 |
| `∑ i : Fin (n + 1), f i` → `f 0 + ∑ i : Fin n, f i.succ` | `rw [Fin.sum_univ_succ]` | R7 |
| `↑j.succ` → `↑j + 1`, `↑0` → `0` (also under `∑`) | `simp`, or `simp only [Fin.val_zero, Fin.val_succ]` | R8, R9 |
| see the state | infoview | |
