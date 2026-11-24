# E064 · simp_rw: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `rw [h]` and `rw [← h]`, `fun x => e`, `∀`, `↔`, `exact`.
**New here:** the tactic `simp_rw`, which rewrites *under binders*; Mathlib's algebra lemmas `two_mul`,
`mul_add`, `mul_one`, `zero_add` and the type classes they are stated for; Mathlib's finite sums
`∑ i ∈ s, f i` over a `Finset`.

## How to read an entry

Each entry is one tactic or one lemma used with `simp_rw`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the goal; no entry changes the
  hypotheses.
- `P` (or `Q`) is "the rest of your goal". The step changes only the part inside `P (…)`, wherever it sits in
  a larger goal.
- Placeholders are written as Lean binders. `{ι α β : Type}` are any types; `ι` is the type of the bound
  variable, `α`/`β` the type of the values. A bracket such as `[NonAssocSemiring α]` is a requirement on `α`
  (a *type class*); each entry says which familiar types meet it. `ℕ`, `ℤ`, `ℚ`, `ℝ` meet all of them.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

**What a binder is.** In `fun x => e`, `∀ x, e`, `∃ x, e` and `∑ i ∈ s, e`, the variable is *bound*: it
exists only inside `e`. `rw [h]` with `h : ∀ x, g x = k x` first turns `h` into the pattern `g ?x` and looks
for one instance of it in the goal. An instance inside `e` would have to fill `?x` with the bound variable,
which `rw` never does, so it fails with "did not find an occurrence of the pattern". `simp_rw [h]` enters
the binder, fixes a fresh `x`, rewrites there and closes the binder again.

`simp_rw [r₁, r₂, …]` applies the rules one at a time, left to right: each rule rewrites *every* match,
everywhere in the goal (under binders too), until none is left. `← r` uses `r` right to left.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ` | `Nat`, the natural numbers `0, 1, 2, …`; numerals such as `2 * n` are in `ℕ` |
| `fun x => e` | the function `x ↦ e`; `λ x => e` is the same term (the guide writes `λ`: `fun` is banned here) |
| `P fun x => e` | `P (fun x => e)`: Lean drops the parentheses around a trailing `fun` |
| `∀ (x : ι), p x` | `∀ x, p x` with the binder's type printed |
| `Finset ι` | a finite set of elements of `ι` (Mathlib) |
| `Finset.range n` | the finite set `{0, 1, …, n - 1}` of naturals |
| `∑ i ∈ s, f i` | the sum of `f i` over `i ∈ s`; it is `Finset.sum s (fun i => f i)`, so the summand is a `fun` |
| `∑ x ∈ s, …` after a step | the same sum: `simp_rw` renamed the bound variable `i` to `x` |
| `inst✝ : Add β` | an unnamed type-class hypothesis, from a bracket `[Add β]` |
| `A ↔ B` | `A` if and only if `B` |

---

## Part 1 · `fun_rw`

Statement: given `f : ℕ → ℕ` with `f n = n + 1` for every `n`, the two functions `n ↦ f n + f n` and
`n ↦ 2 * n + 2` are equal. Both sides are `fun`s, so every rewrite happens under the binder.

**R1 · `simp_rw [h]`** with `h : ∀ x, g x = k x` changes the **goal**: every `g x` under the binder becomes
`k x`. Placeholders: `{ι β : Type} [Add β] (g k : ι → β) (c : β)`, `(P : (ι → β) → Prop)`.

| Before | After |
|---|---|
| `⊢ P fun x => g x + c` | `⊢ P fun x => k x + c` |

**R2 · `simp_rw [← two_mul]`** changes the **goal**. The lemma is `two_mul : 2 * a = a + a`, and `←` uses it
right to left, so a sum of two equal terms becomes a doubling. The two terms must be syntactically the same
(`n + 1 + (n + 1)` qualifies: both halves are `n + 1`). Placeholders: `{ι α : Type} [NonAssocSemiring α]`
(α has `+`, `*`, `0`, `1` and the distributive laws; ℕ qualifies), `(g : ι → α)`.

| Before | After |
|---|---|
| `⊢ P fun x => g x + g x` | `⊢ P fun x => 2 * g x` |

**R3 · `simp_rw [mul_add]`** changes the **goal**. The lemma is `mul_add : a * (b + c) = a * b + a * c`
(distribute a factor on the left). Placeholders: `{ι α : Type} [Mul α] [Add α] [LeftDistribClass α]`
(α has `*`, `+`, and left distributivity; ℕ qualifies), `(a : α) (g k : ι → α)`.

| Before | After |
|---|---|
| `⊢ P fun x => a * (g x + k x)` | `⊢ P fun x => a * g x + a * k x` |

**R4 · `simp_rw [mul_one]`** changes the **goal**. The lemma is `mul_one : a * 1 = a`. Placeholders:
`{ι α : Type} [MulOneClass α]` (α has `*` with unit `1`; ℕ qualifies), `[Add α] (g k : ι → α)`.

| Before | After |
|---|---|
| `⊢ P fun x => g x * 1 + k x` | `⊢ P fun x => g x + k x` |

**R5 · `simp_rw` closes the goal** (goal list: one goal → none) when, after a rule, the goal is `e = e` or
`A ↔ A` with the two sides the same text. So after the last rule of the chain there is nothing left to write.
It does not compute: `2 * n + 2 * 1 = 2 * n + 2` stays open until a rule (R4) rewrites `2 * 1`. Placeholders:
`{ι α : Type} (p : α → Prop) (g k : ι → α)`, `h : ∀ x, g x = k x`.

| Before | After `simp_rw [h]` |
|---|---|
| `⊢ (∀ (x : ι), p (g x)) ↔ ∀ (x : ι), p (k x)` | no goals |

### Worked combination (W1, on an object that is not the exercise's)

**W1: `rw` works under a binder when the pattern has no bound variable.** With `h : c = d`, the pattern `c`
does not mention `x`, so `rw [h]` finds it inside the `fun`:

| Before | After `rw [h]` |
|---|---|
| `⊢ P fun x => g x + c` | `⊢ P fun x => g x + d` |

---

## Part 2 · `forall_rw`

Statement: for a predicate `p` on ℕ, "`p (0 + n)` for every `n`" is equivalent to "`p n` for every `n`". The
`0 + n` sits under the binder `∀ n`.

**R6 · `simp_rw [zero_add]`** changes the **goal**. The lemma is `zero_add : 0 + a = a`. Placeholders:
`{α : Type} [AddZeroClass α]` (α has `+` with unit `0`; ℕ qualifies), `(p : α → Prop) (Q : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ Q (∀ (x : α), p (0 + x))` | `⊢ Q (∀ (x : α), p x)` |

When the whole goal is an `↔` whose two sides become the same, R5 closes it.

**W2: nested binders `∃ x, ∀ y`.** `simp_rw [mul_one]` then `simp_rw [zero_add]` (R4, R6); the second step
leaves `A ↔ A` and closes it (R5):

```lean-goal
⊢ (∃ x, ∀ (y : α), p (x * 1) (0 + y)) ↔ ∃ x, ∀ (y : α), p x y
⊢ (∃ x, ∀ (y : α), p x (0 + y)) ↔ ∃ x, ∀ (y : α), p x y
```

---

## Part 3 · `sum_two`

Statement: `∑_{i<n} 2i = ∑_{i<n} (i + i)`, as sums over `Finset.range n = {0, …, n - 1}`. The summand is a
`fun i => …`, so `2 * i` is under a binder.

**R7 · `simp_rw [two_mul]`** under `∑` changes the **goal**: every summand `2 * g i` becomes `g i + g i`
(R2's lemma, now left to right). Placeholders: `{ι : Type} (s : Finset ι) (g : ι → ℕ) (P : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, 2 * g i)` | `⊢ P (∑ x ∈ s, (g x + g x))` |

**W3: a chain under `∑`.** `simp_rw [mul_one]` (R4) on
`∑ i ∈ s, (g i * 1 + g i * 1) = ∑ i ∈ s, 2 * g i`, then `simp_rw [← two_mul]` (R2), which leaves both sides
equal and closes the goal (R5):

```lean-goal
⊢ ∑ i ∈ s, (g i * 1 + g i * 1) = ∑ i ∈ s, 2 * g i
⊢ ∑ x ∈ s, (g x + g x) = ∑ i ∈ s, 2 * g i
```

---

## Traps

- `rw [h]` on a term under a binder fails with this error; it is the cue to use `simp_rw`:
  ```
  Tactic `rewrite` failed: Did not find an occurrence of the pattern
    f ?n
  ```
  The same happens to `rw [zero_add]` on `∀ n, p (0 + n)` (pattern `0 + ?a`).
- This exercise bans `fun`, `intro`, `funext`, `ext`, `constructor`, `congr`, `conv`: you may not open the
  binder and rewrite inside; `simp_rw` must reach in. `simp`, `ring`, `abel`, `norm_num`, `push_cast` are
  banned too: they also work under binders and would skip the lesson.
- Each `simp_rw` rule rewrites **every** match, as often as it can. `simp_rw [two_mul]` and
  `simp_rw [← two_mul]` undo each other; never put both in one call.
- `← two_mul` needs two syntactically equal summands: `a + a`, not `a + b` with `a = b` only provable.
- After `mul_add` the goal holds `2 * 1`, not `2`: `simp_rw` rewrites only with the rules you give, so add
  `mul_one` to turn `2 * 1` into `2`.
- Do not write a rule after the goal is closed: `simp_rw` fails on a rule with nothing to rewrite, and fails
  when there is no goal.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| rewrite with `h : ∀ x, g x = k x` under `fun` / `∀` / `∑` | `simp_rw [h]` | R1 |
| several rules in order | `simp_rw [r₁, ← r₂, r₃]` | R1–R4 |
| `a + a → 2 * a` | `simp_rw [← two_mul]` | R2 |
| `2 * a → a + a` | `simp_rw [two_mul]` | R7 |
| `a * (b + c) → a * b + a * c` | `simp_rw [mul_add]` | R3 |
| `a * 1 → a` | `simp_rw [mul_one]` | R4 |
| `0 + a → a` | `simp_rw [zero_add]` | R6 |
| finish `e = e` / `A ↔ A` | nothing: `simp_rw` closes it | R5 |
| rewrite a term with no bound variable | `rw [h]` still works | W1 |
| see the state | infoview | |
