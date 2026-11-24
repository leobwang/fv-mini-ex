# H069 · Floating-point summation error: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `inductive`, structural recursion, `theorem … := by`.
**New here:** Mathlib's real numbers `ℝ` and absolute value `|·|`, induction on your own inductive type
and on lists, `obtain`, `set`, `calc`, and the inequality tactics `gcongr`, `linarith`, `nlinarith`.

**The model.** A rounding function `fl : ℝ → ℝ` satisfies `RelErr u fl` when every real `x` is rounded to
`x * (1 + δ)` for some `δ` with `|δ| ≤ u` (`u` is the unit roundoff, e.g. `2⁻⁵³` for binary64). The
`δ` depends on `x`, and `RelErr u fl` is **all** you know about `fl`. A `STree` fixes the order of the
additions; `t.flSum fl` rounds after every addition. The claim: the error is at most
`((1 + u) ^ depth - 1) · ∑ |xᵢ|`, which is `≈ depth · u · ∑ |xᵢ|` for small `u`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`, `refine`, `exact` or as a term. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Preorder α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- A state containing `|·|` cannot sit in a Markdown table (`|` splits cells). Such states are given as a
  `lean-goal` block instead: the first line is the goal before the step, the next lines the goals after.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (exact, not floats); `ℕ` is the naturals |
| `\|a\|` | `abs a`, the absolute value |
| `STree.leaf x`, `l.node r` | the constructors `STree.leaf x` and `STree.node l r`; after `induction` the node goal is stated for `l.node r` until you unfold (R2) |
| `STree.flSum fl l` | `l.flSum fl`; Lean prints the dot form only when the tree is the first explicit argument |
| `l.exact`, `l.absSum`, `l.depth` | `STree.exact l` etc.: the exact sum, `∑ \|xᵢ\|`, and the depth of `l` |
| `(1 + u) ^ d` | a real number to a natural power `d : ℕ` (no cast involved) |
| `max m n` | the larger of two naturals |
| `[]`, `x :: xs` | the empty list, and the list with head `x` and tail `xs`; the `nil` goal shows `fsum fl []`, `[].sum`, `[].length` |
| `∀ x ∈ l, 0 ≤ x` | `∀ x, x ∈ l → 0 ≤ x`: every element of the list `l` is nonnegative (R23) |
| `List.map abs xs` | `xs.map abs`, the list of absolute values; `(List.map abs xs).sum` is `∑ \|xᵢ\|` |
| `xs.sum`, `xs.length` | `List.sum xs`, `List.length xs` |
| `d : ℕ := max l.depth r.depth` | a local definition made by `set` (R12); later printed `d : ℕ := ⋯` |
| `n✝`, `a_ih✝`, `head✝` | inaccessible names: Lean made them up; name them with `with` (R1, R6) |
| `case node`, `case cons` | the goal of that constructor after `induction` (R1, R6) |
| `case ha`, `case hmn`, `case h₁`, `case h₂`, `case b0` | labels of the goals `gcongr` leaves (R15, R21); `b0` labels a `0 ≤ …` side goal |
| `RelErr u fl` | a `def` of the problem; `obtain` sees through it to the `∃` inside (R11) |

---

## Part 1 · `abs_exact_le` (milestone)

Statement: `|t.exact| ≤ t.absSum`, the triangle inequality over a whole tree. Prove it first: Part 4
uses it for `0 ≤ l.absSum` (R13) and for `|l.exact + r.exact| ≤ l.absSum + r.absSum`.

**R1 · `induction t with | tip n => _ | fork a b iha ihb => _`** changes the **goal list and the context**:
one goal per constructor, and each recursive argument (`a`, `b`) comes with its induction hypothesis
(`iha : P a`). The names after each constructor are yours to choose, in the order of the constructor's
arguments, then the hypotheses. Placeholders: `(P : Bin → Prop) (t : Bin)`, where `Bin` is the guide's tree
type with constructors `tip (n : ℕ)` and `fork (a b : Bin)`. For `STree`: `| leaf x => _ | node l r ihl ihr => _`.

| Before | After |
|---|---|
| `t : Bin ⊢ P t` | `n : ℕ ⊢ P (Bin.tip n)`, `a b : Bin, iha : P a, ihb : P b ⊢ P (a.fork b)` |

**R2 · `simp only [Bin.size]`** changes the **goal**: a function defined by pattern matching, applied to a
constructor, becomes that clause's right side. Placeholders: `(a b : Bin)`. For this problem:
`simp only [STree.exact, STree.absSum]` (Parts 1, 4), and with `STree.flSum, STree.depth` too (Part 4).

| Before | After |
|---|---|
| `⊢ P (a.fork b).size` | `⊢ P (a.size + b.size)` |

**R3 · `h₁.trans h₂`** (lemma `le_trans : a ≤ b → b ≤ c → a ≤ c`) changes the **goal** when written as
`refine h₁.trans ?_`: what is left is the second link. Placeholders: `{α : Type} [Preorder α] (a b c : α)`
(`[Preorder α]`: `α` has a reflexive, transitive `≤`; `ℝ` and `ℕ` qualify).

| Before | After |
|---|---|
| `hab : a ≤ b ⊢ a ≤ c` | `⊢ b ≤ c` |

**R4 · `abs_add_le`** changes the **goal** (used with R3): `abs_add_le a b : |a + b| ≤ |a| + |b|`.
Placeholders: `(a b c : ℝ)`. Step: `refine (abs_add_le a b).trans ?_`.

```lean-goal
⊢ |a + b| ≤ c
⊢ |a| + |b| ≤ c
```

**R5 · `add_le_add`** changes the **goal list**: `add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d`, so
`refine add_le_add ?_ ?_` leaves one goal per summand. Placeholders: `(a b c d : ℝ)`. As a term:
`(abs_add_le _ _).trans (add_le_add ihl ihr)` is R4, R3, R5 in one line.

| Before | After |
|---|---|
| `⊢ a + c ≤ b + d` | `⊢ a ≤ b`, `⊢ c ≤ d` |

---

## Part 2 · `abs_list_sum_le` (milestone)

Statement: `|xs.sum| ≤ (xs.map abs).sum`, the same inequality for lists. Part 5 uses it.

**R6 · `induction xs with | nil => _ | cons x xs ih => _`** changes the **goal list and the context**, as R1
for the list type: `[]` and `x :: xs`, the latter with `ih` for `xs`. Placeholders: `{α : Type}
(P : List α → Prop) (xs : List α)`.

| Before | After |
|---|---|
| `xs : List α ⊢ P xs` | `⊢ P []`, `x : α, xs : List α, ih : P xs ⊢ P (x :: xs)` |

**R7 · `List.sum_cons`, `List.map_cons`, `List.length_cons`** change the **goal**: each list function at
`x :: xs` becomes one step of its recursion. Statements: `(x :: xs).sum = x + xs.sum`,
`(x :: xs).map f = f x :: xs.map f`, `(x :: xs).length = xs.length + 1`. Placeholders:
`{α β : Type} [AddMonoid α] (x : α) (xs : List α) (f : α → β)` (`[AddMonoid α]`: `α` has `+` and `0`; `ℝ`
qualifies). Use them together: `simp only [List.sum_cons, List.map_cons]`.

| Before | After |
|---|---|
| `⊢ P (x :: xs).sum` | `⊢ P (x + xs.sum)` |
| `⊢ P (List.map f (x :: xs))` | `⊢ P (f x :: List.map f xs)` |
| `⊢ P (x :: xs).length` | `⊢ P (xs.length + 1)` |

**R8 · `linarith`** **closes** a goal `t ≤ t'`, `t < t'` or `t = t'` that follows from the hypotheses by
adding them up with nonnegative rational coefficients. It treats every nonlinear piece (`|a|`, `a * b`,
`a ^ n`) as an unknown. `linarith [p, q]` also uses the proof terms `p, q`, e.g.
`linarith [abs_nonneg a, abs_list_sum_le xs]`.

---

## Part 3 · `one_add_delta` (milestone)

Statement: from `|δ| ≤ u`, `|1 + δ| ≤ 1 + u`. Parts 4 and 5 use it for the factor `|1 + δ|`.

**R9 · `rw [abs_le] at h ⊢`** changes the **goal and the context**: `abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b`
turns an absolute-value bound into two linear ones, in `h` and in the goal at once (`at h ⊢`). Then
`constructor` (TACTIC_STATES) and `linarith` (R8) on each half. Placeholders: `(a b c : ℝ)`. The hypothesis
`h : |a| ≤ b` becomes `h : -b ≤ a ∧ a ≤ b`; the goal:

```lean-goal
⊢ |a| ≤ c
⊢ -c ≤ a ∧ a ≤ c
```

---

## Part 4 · `tree_sum_error`

Statement: `|t.flSum fl - t.exact| ≤ ((1 + u) ^ t.depth - 1) * t.absSum`. Induction on `t` (R1). The node
case is the whole problem: with `s = l.flSum fl + r.flSum fl` and `eₗ = l.flSum fl - l.exact` (same for `r`),

  `fl s - (l.exact + r.exact) = (eₗ + eᵣ) * (1 + δ) + (l.exact + r.exact) * δ`:

the children's errors are scaled by `1 + δ`, and the new rounding adds `δ` times the exact sum.

### The leaf

**R10 · `simp`** on the leaf goal `|x - x| ≤ ((1 + u) ^ 0 - 1) * |x|` (after R2) **closes** it, with
`sub_self : a - a = 0`, `abs_zero : |0| = 0`, `pow_zero : a ^ 0 = 1`, `zero_mul : 0 * a = 0`.
Placeholders: `(x a : ℝ)`.

```lean-goal
⊢ P (|x - x| + (a ^ 0 - 1) * |x|)
⊢ P 0
```

### Unpacking the rounding, naming the depth

**R11 · `obtain ⟨d, hA, hB⟩ := h`** changes the **context**: `h : ∃ d, A d ∧ B d` is replaced by a witness and
the two facts. Placeholders: `{α : Type} (A B : α → Prop) (G : Prop)`. Here: `hfl` is a `∀`, so apply it to
the sum you round first: `obtain ⟨δ, hδ, hs⟩ := hfl (l.flSum fl + r.flSum fl)`; then
`hs : fl (…) = (…) * (1 + δ)` is what `rw [hs]` uses after R2.

| Before | After |
|---|---|
| `h : ∃ d, A d ∧ B d` and `⊢ G` | `d : α, hA : A d, hB : B d ⊢ G` |

**R12 · `set d := e`** changes the **goal and the context**: it adds the local definition `d := e` and
replaces every `e` in the goal by `d`. Placeholders: `(m n : ℕ)`. Here: `set d := max l.depth r.depth`.

| Before | After |
|---|---|
| `⊢ P (max m n + 1)` | `d : ℕ := max m n ⊢ P (d + 1)` |

**R13 · `abs_nonneg`** changes the **context** (as a `have`): `abs_nonneg a : 0 ≤ |a|`. With R3:
`(abs_nonneg _).trans (abs_exact_le l) : 0 ≤ l.absSum`. Placeholders: `(e A : ℝ)`. After
`have h0 : 0 ≤ |e| := abs_nonneg e` the context has `h0`; the goal stays

```lean-goal
⊢ 0 ≤ A
```

### Lifting both children to the common depth

**R14 · `gcongr`** changes the **goal**: for a goal `lhs ≤ rhs` where both sides have the same shape, it
reduces to inequalities between the parts that differ, using monotonicity lemmas. Side conditions
(`0 ≤ c` to multiply by `c`) are closed from the context or by `positivity`. Placeholders: `(a b c x : ℝ)`.

| Before | After |
|---|---|
| `hc : 0 ≤ c ⊢ a * c ≤ b * c` | `⊢ a ≤ b` |

**R15 · `gcongr` on a power** changes the **goal list**: it uses `pow_le_pow_right₀ : 1 ≤ a → m ≤ n →
a ^ m ≤ a ^ n` and leaves `1 ≤ a` and `m ≤ n`. `exacts [p, q]` closes the goals in order with `p`, `q`.
Placeholders: `(u A : ℝ) (m n : ℕ)`, with `hu : 0 ≤ u`. Here: `ihl.trans (by gcongr; exacts [by linarith, le_max_left _ _])`
lifts `ihl` from depth `l.depth` to `d` (R3, R15, R8, R16).

| Before | After |
|---|---|
| `hA : 0 ≤ A ⊢ ((1 + u) ^ m - 1) * A ≤ ((1 + u) ^ max m n - 1) * A` | `⊢ 1 ≤ 1 + u`, `⊢ m ≤ max m n` |

**R16 · `le_max_left m n : m ≤ max m n`**, **`le_max_right m n : n ≤ max m n`**: terms, no state change.
Placeholders: `(m n : ℕ)`.

### Splitting the error, the `calc` chain

**R17 · `rw [show A = B by ring]`** changes the **goal**: `show A = B by ring` is a proof of the identity,
built on the spot, and `rw` uses it. `A` must appear literally in the goal: copy it from the infoview.
Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((a + b) * c)` | `⊢ P (a * c + b * c)` |

**R18 · `calc`** **closes** a goal `a ≤ d` by a chain of links `_ ≤ b := p₁`, `_ ≤ c := p₂`, `_ = d := p₃`,
each with its own proof (a term, or `by …` indented further). `_` at the start of a line is the right side
of the previous line; in the first line it is the goal's left side. Mixed `≤`, `<`, `=` links combine.
Placeholders: `(a b c d : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ d` | closed |

**R19 · `rw [abs_mul]`** changes the **goal**: `abs_mul a b : |a * b| = |a| * |b|`. Write `rw [abs_mul, abs_mul]`
for two products. Placeholders: `(a b : ℝ)`.

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R20 · `one_le_pow₀`** changes the **context** (as a `have`): `one_le_pow₀ : 1 ≤ a → 1 ≤ a ^ n`.
Placeholders: `(a : ℝ) (n : ℕ)`. Here: `have hd1 : (1 : ℝ) ≤ (1 + u) ^ d := one_le_pow₀ (by linarith)`.
It is needed **before** R21: it lets `positivity` prove `0 ≤ (1 + u) ^ d - 1`.

| Before | After |
|---|---|
| `ha : 1 ≤ a ⊢ 0 ≤ a ^ n - 1` | `h : 1 ≤ a ^ n ⊢ 0 ≤ a ^ n - 1` |

**R21 · `gcongr` on a sum of products** changes the **goal list**: one goal per factor that differs between
the two sides. A goal equal to a hypothesis (`hδ : |δ| ≤ u`) is closed for you. Side goals `0 ≤ …` go to
`positivity`, which reads hypotheses such as `hw : 1 ≤ w`, `hA : 0 ≤ A`. Placeholders: `(e s δ u w A C : ℝ)`
with `hw : 1 ≤ w`, `hA : 0 ≤ A`, `hC : 0 ≤ C`, `hδ : |δ| ≤ u`.

```lean-goal
⊢ |e| * |1 + δ| + |s| * |δ| ≤ (w - 1) * A * (1 + u) + C * u
⊢ |e| ≤ (w - 1) * A
⊢ |1 + δ| ≤ 1 + u
⊢ |s| ≤ C
```

Without a bound that `positivity` can use (second example: only `hw : 2 ≤ w + 1`), the side goal stays and
comes **first**:

| Before | After (first goal) |
|---|---|
| `hA : 0 ≤ A` and the goal above | `⊢ 0 ≤ (w - 1) * A` |

**R22 · `ring`** **closes** the last link. It knows `a ^ (n + 1) = a ^ n * a` for a symbolic `n`. The key
identity is `((1 + u) ^ d - 1) * (1 + u) + u = (1 + u) ^ (d + 1) - 1`. Placeholders: `(a x : ℝ) (n : ℕ)`.

### Worked combinations

**W1.** `1 ≤ t.size` for every `Bin`: R1, then R2 and R8 in the `fork` case.

```lean-goal
⊢ 1 ≤ t.size
```

**W2: one rounding of an exact sum.** `|(a + b)(1 + δ) - (a + b)| ≤ (|a| + |b|) u`, by R17, R19, R14, R4:

```lean-goal
⊢ |(a + b) * (1 + δ) - (a + b)| ≤ (|a| + |b|) * u
⊢ |(a + b) * δ| ≤ (|a| + |b|) * u
⊢ |a + b| * |δ| ≤ (|a| + |b|) * u
⊢ |a + b| ≤ |a| + |b|
```

---

## Part 5 · `fsum_error`

Statement: `|fsum fl xs - xs.sum| ≤ ((1 + u) ^ xs.length - 1) * (xs.map abs).sum`. Recursive summation is
the tree whose depth is the length, but `fsum` is a list function, so redo Part 4 by list induction (R6).
New: the error of the tail is already at depth `n = xs.length`, so no lifting (R15) is needed, but the head
`x` only gets the factor `u`, and the last link is an inequality, not an identity.

**R23 · `List.sum_nonneg`** changes the **goal**: `List.sum_nonneg : (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum`.
Placeholders: `(l : List ℝ)`. Here: `List.sum_nonneg (by simp)` proves `0 ≤ (xs.map abs).sum`; `simp`
proves `∀ x ∈ List.map abs xs, 0 ≤ x` with `List.mem_map` and `abs_nonneg`.

| Before | After |
|---|---|
| `⊢ 0 ≤ l.sum` | `⊢ ∀ x ∈ l, 0 ≤ x` |

**R24 · `rw [pow_succ]`** changes the **goal**: `pow_succ a n : a ^ (n + 1) = a ^ n * a`. Placeholders:
`{α : Type} [Monoid α] (a : α) (n : ℕ)` (`[Monoid α]`: `α` has an associative `*` with `1`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

**R25 · `mul_nonneg ha hb : 0 ≤ a * b`** from `ha : 0 ≤ a`, `hb : 0 ≤ b`: a term. Placeholders: `(a b : ℝ)`.

**R26 · `sub_nonneg.mpr h : 0 ≤ a - b`** from `h : b ≤ a`: `sub_nonneg : 0 ≤ a - b ↔ b ≤ a`, and `.mpr` uses
the `↔` right to left. Placeholders: `(a b : ℝ)`.

**R27 · `nlinarith [t]`** **closes** a goal that `linarith` (R8) could close if the product facts `t` were
hypotheses; it also multiplies pairs of hypotheses itself, but a hint makes it reliable. Placeholders:
`(a b c : ℝ)` with `ha : 0 ≤ a`, `hb : 1 ≤ b`, `hc : 0 ≤ c`; hint `mul_nonneg (mul_nonneg ha hc) (sub_nonneg.mpr hb)`,
which is `0 ≤ a * c * (b - 1)` (R25, R26).

| Before | After |
|---|---|
| `⊢ a * c ≤ a * b * c` | closed |

A factor proof can be written inline with its statement spelled out, `(by linarith : (0 : ℝ) ≤ 1 + u)`
(a type ascription `(e : T)`), or first as `have h1u : (0 : ℝ) ≤ 1 + u := by linarith`.

Here the last link, after `rw [pow_succ]`, is `RHS - LHS = |x| · (1 + u) · ((1 + u) ^ n - 1) ≥ 0`
(with `n = xs.length`), so the hint is that product's nonnegativity, from `abs_nonneg x`, `0 ≤ 1 + u` and
`hn1 : 1 ≤ (1 + u) ^ xs.length` (R20).

**W3: list induction.** A sum of squares is nonnegative: R6, R7, then R27 with `sq_nonneg x : 0 ≤ x ^ 2`.

```lean-goal
⊢ 0 ≤ (List.map (fun x => x ^ 2) xs).sum
```

---

## Traps

- `RelErr u fl` is all you know about `fl`: there is no formula to unfold. Each use is `hfl s` for one
  specific `s`, and it gives a fresh `δ` for that `s`.
- Take `δ` (R11) for the sum that is actually rounded, `l.flSum fl + r.flSum fl` (list: `x + fsum fl xs`),
  so that `rw [hs]` finds it in the goal.
- The children have different depths. Lift both IHs to `d = max l.depth r.depth` (R15) **before** the
  `calc`; `gcongr` then needs `0 ≤ l.absSum` in the context (from R13 and `abs_exact_le`).
- `gcongr` leaves side goals `0 ≤ …` it cannot prove, and they come first in the goal list. Put
  `hd1 : 1 ≤ (1 + u) ^ d` (R20) and `0 ≤ absSum` facts in the context before calling it.
- `rw [show A = B by ring]` needs `A` to match the goal up to notation: copy it from the infoview.
  `l.flSum fl` and `STree.flSum fl l` are the same term, but the order of `+` and the parentheses must match.
- `set d := …` shows `d : ℕ := ⋯` later; `d` unfolds to `max …` when a tactic needs it (`le_max_left _ _`
  proves `l.depth ≤ d`).
- The list version's last link is not an identity: the head `x` contributes `|x| · u`, at most
  `|x| · ((1 + u) ^ (n + 1) - 1)`. `ring` fails there; use R24, then R27 with a product hint.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on a tree | `induction t with \| leaf x => _ \| node l r ihl ihr => _` | R1 |
| unfold a definition at a constructor | `simp only [STree.exact, STree.absSum]` | R2 |
| chain `a ≤ b`, `b ≤ c` | `h₁.trans h₂`, `refine h₁.trans ?_` | R3 |
| triangle inequality | `abs_add_le a b : \|a + b\| ≤ \|a\| + \|b\|` | R4 |
| add two bounds | `add_le_add h₁ h₂` | R5 |
| induction on a list | `induction xs with \| nil => _ \| cons x xs ih => _` | R6 |
| list functions at `x :: xs` | `simp only [List.sum_cons, List.map_cons, List.length_cons]` | R7 |
| linear goal from hypotheses | `linarith [extra facts]` | R8 |
| `\|a\| ≤ b` as two inequalities | `rw [abs_le] at h`, and in the goal at the same time (R9) | R9 |
| leaf case | `simp [STree.flSum, STree.exact, STree.depth]` | R10 |
| take the rounding error | `obtain ⟨δ, hδ, hs⟩ := hfl s` | R11 |
| name a subterm | `set d := max l.depth r.depth` | R12 |
| `0 ≤ \|a\|` | `abs_nonneg a` | R13 |
| monotonicity | `gcongr` | R14, R15, R21 |
| `m ≤ max m n` | `le_max_left`, `le_max_right` | R16 |
| rewrite by an identity | `rw [show A = B by ring]` | R17 |
| chain of (in)equalities | `calc _ ≤ b := p₁` / `_ = d := p₂` | R18 |
| `\|a * b\|` | `rw [abs_mul]` | R19 |
| `1 ≤ a ^ n` | `one_le_pow₀ h` | R20 |
| the identity with `^ (d + 1)` | `ring` | R22 |
| `0 ≤ list sum` | `List.sum_nonneg (by simp)` | R23 |
| `a ^ (n + 1)` → `a ^ n * a` | `rw [pow_succ]` | R24 |
| products of nonnegatives | `mul_nonneg`, `sub_nonneg.mpr` | R25, R26 |
| nonlinear last step | `nlinarith [product hint]` | R27 |
| key identity | `((1 + u) ^ d - 1) * (1 + u) + u = (1 + u) ^ (d + 1) - 1` | R22 |
