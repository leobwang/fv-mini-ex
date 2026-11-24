# M102 · Horner's method: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`rw [h]`, `simp only`, `ring`, `exact`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `List`, pattern-matching definitions, `rw`, `simp`,
`exact`. **New here:** Mathlib's finite sums `∑ i ∈ Finset.range n, f i`, safe list indexing
`List.getD`, `l[i]?` and `l[i]`, real polynomials `ℝ[X]` with `coeff`, `natDegree` and `eval`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : β → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid β]`
  is a requirement on `β` (a *type class*). Each entry says which familiar types meet it; `ℕ`, `ℤ`, `ℝ`, `ℂ`
  meet all the brackets used here.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `c :: cs` | the list with head `c` and tail `cs` |
| `[].length`, `cs.length` | `List.length`: the number of entries (`[].length` is `0`) |
| `Finset.range n` | the finite set `{0, 1, …, n - 1}` (a `Finset ℕ`; `Finset.range 0 = ∅`) |
| `∑ i ∈ Finset.range n, f i` | the finite sum $f(0) + \dots + f(n-1)$; `i` is a bound variable |
| `x_1`, `k` as the bound variable | the same sum: after a rewrite Lean may rename the bound variable (`x_1` because `x` is taken) |
| `cs.getD i 0` | `List.getD`: entry `i` of `cs`, counted from 0, or the default `0` if `i ≥ cs.length` |
| `l[i]?` | entry `i` as an `Option`: `some (entry)` if `i < l.length`, else `none` |
| `l[i]` | entry `i`, with a hidden proof that `i < l.length` (it is not shown in the infoview); `l[i]'h` in source passes the proof `h` explicitly (guide R21, R22) |
| `o.getD d` | `Option.getD`: the value inside `o = some a`, or `d` if `o = none` |
| `List.map f l` | `l` with `f` applied to every entry |
| `List.range n` | the list `[0, 1, …, n - 1]` (a `List ℕ`) |
| `↑k` (W3) | the natural number `k` cast into `ℝ` (`(k : ℝ)` in source) |
| `Option.map f o` | `some (f a)` if `o = some a`, else `none`; appears if `simp` meets `(List.map f l)[i]?` (Traps) |
| `ℝ[X]` | polynomials with real coefficients (notation from `open Polynomial`) |
| `p.coeff i` | the coefficient of $X^i$ in `p` (`0` for `i` above the degree) |
| `p.natDegree` | the degree of `p` as a natural number (`0` for `p = 0`) |
| `eval x p` | `p.eval x`, the value $p(x)$; Lean prints `p.eval x` this way |
| `x✝ : i ∈ …` | an unnamed hypothesis (from `fun i _ => …`); `✝` marks a name you cannot type |
| `case cons`, `case nil`, `case e_a` | the goal's tag: which induction case, or which part after `congr 1` |

---

## Part 1 · `horner_eq_sum`

Statement: for every list `cs = [c₀, …, cₙ₋₁]`, `horner x cs` equals $\sum_{i<n} c_i x^i$, where
`n = cs.length` and $c_i$ is written `cs.getD i 0`. Induction on `cs`. In the `cons` case the left side is
`c + x * (sum for cs)` and the right side is the sum for `c :: cs`; split the `i = 0` term off the right side
(R5), push the `x` into the left sum (R6), and make the two sums agree term by term.

### Induction and unfolding

**R1 · `induction xs with | nil => … | cons c cs ih => …`** changes the **goal list and the context**: one
goal per way a list is built. In `cons`, `xs` is `c :: cs` and `ih` is the statement for `cs`.
Placeholders: `(P : List ℝ → Prop) (xs : List ℝ)`.

| Before | After |
|---|---|
| `xs : List ℝ ⊢ P xs` | `⊢ P []`, `c : ℝ, cs : List ℝ, ih : P cs ⊢ P (c :: cs)` |

**R2 · `simp [D]`** **closes** the `nil` case: it unfolds `D []` with D's first equation, and rewrites
`[].length` to `0`, `Finset.range 0` to `∅` and the empty sum to `0`. Placeholders: `total` (the guide's list
sum, defined like `horner` by `| [] => 0 | c :: cs => …`), `(f : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ total [] = ∑ i ∈ Finset.range [].length, f i` | closed |

**R3 · `rw [D]`** changes the **goal**: on an argument of the form `c :: cs` it replaces the call by the
right-hand side of D's `cons` equation. It needs the argument to be literally `[]` or `_ :: _`.
Placeholders: `(c : ℝ) (cs : List ℝ)`.

| Before | After |
|---|---|
| `⊢ P (total (c :: cs))` | `⊢ P (c + total cs)` |

Then `rw [ih]` replaces the recursive call by the sum for `cs` (TACTIC_STATES, `rw [h]`).

**R4 · `List.length_cons`** changes the **goal**: `(a :: as).length = as.length + 1`. This puts the range in
the form `range (n + 1)` that R5 needs. Placeholders: `{α : Type} (a : α) (as : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: as).length` | `⊢ P (as.length + 1)` |

### Sums over `Finset.range`

**R5 · `Finset.sum_range_succ'`** changes the **goal**:
`∑ k ∈ range (n + 1), f k = ∑ k ∈ range n, f (k + 1) + f 0`. It splits off the **first** term and shifts the
index of the rest by one. (`Finset.sum_range_succ`, unprimed, splits off the last term.) Placeholders:
`{β : Type} [AddCommMonoid β] (f : ℕ → β) (n : ℕ)` (β has `+` and `0`, commutative).

| Before | After |
|---|---|
| `⊢ P (∑ k ∈ Finset.range (n + 1), f k)` | `⊢ P (∑ k ∈ Finset.range n, f (k + 1) + f 0)` |

**R6 · `Finset.mul_sum`** changes the **goal**: `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i` (distributivity over a
finite sum). Placeholders: `{ι β : Type} [NonUnitalNonAssocSemiring β] (s : Finset ι) (f : ι → β) (a : β)`
(β has `+`, `*` and distributivity).

| Before | After |
|---|---|
| `⊢ P (a * ∑ i ∈ s, f i)` | `⊢ P (∑ i ∈ s, a * f i)` |

### Reading list entries

**R7 · `List.getD_cons_succ`** changes the **goal**: `(c :: cs).getD (n + 1) d = cs.getD n d`. This is how
the shifted index `k + 1` from R5 lands back on `cs`. Placeholders: `{α : Type} (c d : α) (cs : List α) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((c :: cs).getD (n + 1) d)` | `⊢ P (cs.getD n d)` |

**R8 · `List.getD_cons_zero`** changes the **goal**: `(c :: cs).getD 0 d = c`. Placeholders as in R7.

| Before | After |
|---|---|
| `⊢ P ((c :: cs).getD 0 d)` | `⊢ P c` |

### Powers

**R9 · `pow_zero`, then `mul_one`** change the **goal**: `a ^ 0 = 1` and `b * 1 = b`. Together they clean up
the `i = 0` term `c * x ^ 0`. Placeholders: `{M : Type} [Monoid M] (a b : M)` (M has an associative `*` with
`1`).

| Before | After `rw [pow_zero]` | After `rw [mul_one]` |
|---|---|---|
| `⊢ P (b * a ^ 0)` | `⊢ P (b * 1)` | `⊢ P b` |

**R10 · `pow_succ`** changes the **goal**: `a ^ (n + 1) = a ^ n * a`. The new factor goes on the **right**, so
the right sum's terms become `cᵢ * (x ^ i * x)` while the left sum's are `x * (cᵢ * x ^ i)`; they agree only
up to `ring`. Placeholders: `{M : Type} [Monoid M] (a : M) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

R7–R10 can go in one `simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]`:
`simp only` rewrites under the `∑` binder, which `rw` cannot (TACTIC_STATES, Rewriting).

### Matching the two sides

**R11 · `rw [add_comm]`** changes the **goal**: `a + b = b + a`, applied to the **first** `_ + _` Lean finds
reading the goal left to right, i.e. the left side's top-level sum. Use `add_comm a b` to choose another one.
Placeholders: `{β : Type} [AddCommMagma β] (a b c : β)` (β has a commutative `+`).

| Before | After |
|---|---|
| `⊢ a + b = c` | `⊢ b + a = c` |

**R12 · `congr 1`** changes the **goal list**: `f a b = f a' b'` becomes `a = a'` and `b = b'` (here `f` is
`+`). Parts that are equal on both sides close by `rfl` (or by a hypothesis stating them), so
`S + c = S' + c` leaves only `S = S'`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a + c = b + c` | `⊢ a = b` |

**R13 · `refine Finset.sum_congr rfl fun i hi => ?_`** changes the **goal and the context**: an equation of
two sums over the same set becomes one equation of terms, for an arbitrary `i` with `hi : i ∈ s`. The lemma is
`Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`; `rfl` proves `s₁ = s₂`. In term
form it is `Finset.sum_congr rfl fun i _ => by ring`. Placeholders:
`{ι β : Type} [AddCommMonoid β] (s : Finset ι) (f g : ι → β)`.

| Before | After |
|---|---|
| `⊢ ∑ i ∈ s, f i = ∑ i ∈ s, g i` | `i : ι, hi : i ∈ s ⊢ f i = g i` |

The term goal is then a commutative-ring identity: `ring` (TACTIC_STATES, Closing).

### Worked combinations (W1, W2, on objects that are not the exercise's)

**W1.** `total cs = ∑ i ∈ Finset.range cs.length, cs.getD i 0`, the plain list sum: R1; `nil` by R2; `cons` by
`rw [total, ih, List.length_cons, Finset.sum_range_succ']` (R3, R4, R5), `simp only` with R7, R8, and R11
(which leaves both sides identical, so `rw` closes the goal by `rfl`).

```lean-goal
⊢ total cs = ∑ i ∈ Finset.range cs.length, cs.getD i 0
```

**W2.** `congr 1` then R13 then `ring`:

```lean-goal
⊢ ∑ i ∈ Finset.range n, 2 * (f i * 3) + 1 = ∑ i ∈ Finset.range n, 6 * f i + 1
⊢ ∑ i ∈ Finset.range n, 2 * (f i * 3) = ∑ i ∈ Finset.range n, 6 * f i
⊢ 2 * (f i * 3) = 6 * f i
```

---

## Part 2 · `horner_eval`

Statement: for `p : ℝ[X]` and the list of its coefficients `[p.coeff 0, …, p.coeff d]` with
`d = p.natDegree`, `horner x` of that list is `p.eval x`. Prove Part 1 first and use it as the first rewrite:
both sides become sums over `range (d + 1)` (Part 1, R14), the left range simplifies (R15, R16), and the terms
agree (R13, R17, then R18–R22 inside one `simp`).

**R14 · `Polynomial.eval_eq_sum_range`** changes the **goal**:
`eval x p = ∑ i ∈ range (p.natDegree + 1), p.coeff i * x ^ i`. With `open Polynomial` it can be written
`eval_eq_sum_range`. Placeholders: `(p : ℝ[X]) (x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (eval x p)` | `⊢ P (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i)` |

**R15 · `List.length_map`** changes the **goal**: `(List.map f l).length = l.length`. Placeholders:
`{α β : Type} (f : α → β) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P (List.map f l).length` | `⊢ P l.length` |

**R16 · `List.length_range`** changes the **goal**: `(List.range n).length = n`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (List.range n).length` | `⊢ P n` |

R15 and R16 sit inside a `Finset.range …` under the sum; `rw` reaches them (they are not under the binder),
`simp only [List.length_map, List.length_range]` works too.

**R17 · `rw [Finset.mem_range] at hi`** changes the **context**: `Finset.mem_range : m ∈ range n ↔ m < n`.
`simp` can use `hi : i < n` to decide `i < length`, not `i ∈ range n`. Placeholders: `(i n : ℕ)`.

| Before | After |
|---|---|
| `hi : i ∈ Finset.range n ⊢ G` | `hi : i < n ⊢ G` |

### One entry of a mapped list

`simp [List.getD_eq_getElem?_getD, hi]` does R18–R22 in a row. Only R18 has to be named: `simp` applies R19–R22
by itself, and uses `hi` (after R15, R16 on the length) for R19's side condition.

**R18 · `List.getD_eq_getElem?_getD`** changes the **goal**: `l.getD i d = l[i]?.getD d`. Placeholders:
`{α : Type} (l : List α) (i : ℕ) (d : α)`.

| Before | After |
|---|---|
| `⊢ P (l.getD i d)` | `⊢ P (l[i]?.getD d)` |

**R19 · `getElem?_pos`** changes the **goal**: `l[i]? = some l[i]` given `hl : i < l.length`. Placeholders:
`{α : Type} (l : List α) (i : ℕ) (hl : i < l.length)`.

| Before | After |
|---|---|
| `⊢ P l[i]?` | `⊢ P (some l[i])` |

**R20 · `Option.getD_some`** changes the **goal**: `(some a).getD d = a`. Placeholders: `{α : Type} (a d : α)`.

| Before | After |
|---|---|
| `⊢ P ((some a).getD d)` | `⊢ P a` |

**R21 · `List.getElem_map`** changes the **goal**: `(List.map f l)[i] = f l[i]`. Placeholders:
`{α β : Type} (f : α → β) (l : List α) (i : ℕ)`, with `hl : i < (List.map f l).length`.

| Before | After |
|---|---|
| `⊢ P (List.map f l)[i]` | `⊢ P (f l[i])` |

**R22 · `List.getElem_range`** changes the **goal**: `(List.range n)[j] = j`. Placeholders: `(n j : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (List.range n)[j]` | `⊢ P j` |

**W3.** Entry `i` of the list of squares `[0, 1, 4, 9, 16]`, given `hi : i < 5`: one
`simp [List.getD_eq_getElem?_getD, hi]` (R18–R22) closes

```lean-goal
⊢ (List.map (fun k => ↑k ^ 2) (List.range 5)).getD i 0 = ↑i ^ 2
```

---

## Traps

- `Finset.sum_range_succ'` (primed) splits off `f 0`; `Finset.sum_range_succ` splits off `f n`. Horner needs the
  first one, because `horner` consumes the list from the front.
- `rw` cannot rewrite under the `∑ i ∈ s, …` binder when the pattern mentions the bound variable (`cs.getD (i+1) 0`,
  `x ^ (i + 1)`): use `simp only [...]`.
- `pow_succ` gives `x ^ i * x`, not `x * x ^ i`. After R6 the two sums differ by the order of the factors, so do
  not expect `rfl`: finish termwise with R13 and `ring`.
- `rw [add_comm]` swaps the first `+` it finds, which may not be the one you mean; check the infoview.
- After a rewrite the bound variable may be renamed (`x_1`, `k`): the sum is the same.
- In `horner_eval`, rewrite with `horner_eq_sum` before anything else; it needs Part 1 to be proved (or at
  least stated) above.
- `simp` needs `hi : i < p.natDegree + 1`, not `hi : i ∈ Finset.range …`: do R17 first.
- If you forget `hi` in the last `simp`, it cannot read the entry: it turns `getD` into
  `(Option.map p.coeff (List.range …)[i]?).getD 0` and, because both sides end in `* x ^ i`, cancels that factor
  into a disjunction `… = p.coeff i ∨ x = 0 ∧ ¬i = 0`. Add `hi` (in the `<` form); the goal then closes.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on a list | `induction cs with \| nil => … \| cons c cs ih => …` | R1 |
| close the `nil` case | `simp [horner]` | R2 |
| unfold `f (c :: cs)` | `rw [f]` | R3 |
| `(a :: as).length` | `List.length_cons` | R4 |
| split off the `i = 0` term | `Finset.sum_range_succ'` | R5 |
| `a * ∑ = ∑ a *` | `Finset.mul_sum` | R6 |
| `getD` of a cons at `n + 1` / at `0` | `List.getD_cons_succ` / `List.getD_cons_zero` | R7, R8 |
| `a ^ 0`, `* 1`, `a ^ (n + 1)` | `pow_zero`, `mul_one`, `pow_succ` | R9, R10 |
| rewrite under `∑` | `simp only [lemmas]` | R7–R10 |
| swap `a + b` | `rw [add_comm]` | R11 |
| `S + c = S' + c` → `S = S'` | `congr 1` | R12 |
| sums equal termwise | `refine Finset.sum_congr rfl fun i hi => ?_` | R13 |
| commutative-ring identity | `ring` | |
| `p.eval x` as a sum | `eval_eq_sum_range` | R14 |
| length of `map` / `range` | `List.length_map`, `List.length_range` | R15, R16 |
| `i ∈ range n` → `i < n` | `rw [Finset.mem_range] at hi` | R17 |
| one entry of `(List.range n).map f` | `simp [List.getD_eq_getElem?_getD, hi]` | R18–R22 |
| see the state | infoview | |
