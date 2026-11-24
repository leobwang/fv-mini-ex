# M075 · Monotone convergence: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, absolute value
`|x|`, sets and `Set.range`, the supremum `sSup` of a set of reals and its two lemmas (`le_csSup`,
`exists_lt_of_lt_csSup`), `BddAbove`, `Monotone`, the `obtain … rfl` pattern, and `linarith`. Mathlib's own
limits (`Tendsto`, filters) are banned: you build `N` by hand.

## How to read an entry

Each entry is one tactic or one lemma used with `have`/`rw`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal". A bare `P : Prop` is "whatever the goal is" in entries that only add a fact
  to the context.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Preorder α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it; `ℝ` meets all of them.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ → ℝ` | a real sequence `a₀, a₁, …`; `a n` is the term `aₙ` |
| `ℝ` | Mathlib's real numbers (a complete ordered field; not floating point) |
| `\|x\|` | `abs x`, the absolute value |
| `Set α` | a set of elements of `α` (a predicate `α → Prop`); `x ∈ s` is membership |
| `Set.range a` | `{x \| ∃ n, a n = x}`, the set of values of `a`; `x ∈ Set.range a` unfolds to `∃ y, a y = x` |
| `sSup s` | the supremum (least upper bound) of `s`. On `ℝ` it is only meaningful for `s` nonempty and bounded above; otherwise Lean defines it as `0` |
| `BddAbove s` | `s` has an upper bound: some `M` with `x ≤ M` for every `x ∈ s` |
| `s.Nonempty` | `Set.Nonempty s`: `∃ x, x ∈ s` |
| `Monotone a` | `∀ ⦃m n⦄, m ≤ n → a m ≤ a n` (non-decreasing). `⦃ ⦄` (strict implicit) means `m`, `n` are not written: they are read off the proof of `m ≤ n` you pass, so `hm h : a m ≤ a n` |
| `ConvergesTo a L` | the exercise's definition: `∀ ε > 0, ∃ N, ∀ n ≥ N, \|a n - L\| < ε` |
| `∀ ε > 0, Q ε` | `∀ ε, ε > 0 → Q ε`: `intro` takes two names (R1) |
| `∀ n ≥ N, Q n` | `∀ n, n ≥ N → Q n` (R6) |
| `∃ x ∈ s, Q x` | `∃ x, x ∈ s ∧ Q x` (R4, R5) |
| `n ≥ N` | `N ≤ n` (`≥` is `≤` with the sides swapped; the same term) |
| `cs` in a lemma name | "conditionally complete": the lemma needs `Nonempty`/`BddAbove` hypotheses because `sSup` is only well behaved on such sets |
| `case left`, `case right` | the two goals `constructor` makes from `A ∧ B`: `left` is `A`, `right` is `B` |
| `inst✝ : …` | an unnamed type-class assumption from a bracket `[…]` |

---

## Part 1 · `monotone_converges`

Statement: if `a : ℕ → ℝ` is monotone and its set of values is bounded above, then `a` converges, in the
explicit ε-N sense, to `L = sSup (Set.range a)`. The math: given `ε > 0`, `L - ε < L`, so `L - ε` is not an
upper bound and some term satisfies `L - ε < a N`. For `n ≥ N`, monotonicity and `L` being an upper bound give
`L - ε < a N ≤ a n ≤ L`, hence `|a n - L| < ε`.

### Opening the ε-N statement

**R1 · `intro ε hε`** changes the **goal and the context**. `intro` unfolds a definition by itself when its body
starts with `∀`, so `ConvergesTo a L` needs no `unfold` first. `∀ ε > 0, Q ε` is two binders: `ε : ℝ` and
`hε : ε > 0`. Placeholders: `(Q : ℝ → Prop)`, and `AllPos Q := ∀ ε > 0, Q ε` as the named definition.

| Before | After |
|---|---|
| `⊢ AllPos Q` | `ε : ℝ, hε : ε > 0 ⊢ Q ε` |

### Finding a term above `sSup s - ε`

**R2 · `sub_lt_self`** changes the **context** (via `have`). Statement: `sub_lt_self (a : α) : 0 < b → a - b < a`.
`a` is explicit, `b` is read off the proof of `0 < b`; write `sub_lt_self _ hε` and Lean fills `a` from the
expected type. `hε : ε > 0` is accepted as `0 < ε` (same term). Placeholders:
`{α : Type} [AddGroup α] [LT α] [AddLeftStrictMono α] (a b : α)` (an additive group where adding on the left
preserves `<`; `ℝ`, `ℤ`, `ℚ` qualify).

| Before | After |
|---|---|
| `hb : 0 < b ⊢ P` | `hb : 0 < b, hlt : a - b < a ⊢ P` |

**R3 · `Set.range_nonempty`** changes the **context** (via `have`), or is passed directly as an argument.
Statement: `Set.range_nonempty (f : ι → α) : (Set.range f).Nonempty`, for a nonempty domain `ι` (Lean finds
`Nonempty ℕ` by itself). Placeholders: `{α : Type} (f : ℕ → α)`.

| Before | After |
|---|---|
| `⊢ P` | `hne : (Set.range f).Nonempty ⊢ P` |

**R4 · `exists_lt_of_lt_csSup`** changes the **context** (via `have`), or feeds `obtain` directly (R5).
Statement: `exists_lt_of_lt_csSup : s.Nonempty → b < sSup s → ∃ x ∈ s, b < x`: anything strictly below the
supremum is beaten by an element of the set. Placeholders:
`{α : Type} [ConditionallyCompleteLinearOrder α] (s : Set α) (b : α)` (a total order in which every nonempty
bounded set has a `sSup`; `ℝ` qualifies, `ℚ` does not).

| Before | After |
|---|---|
| `hs : s.Nonempty, hb : b < sSup s ⊢ P` | `hs : s.Nonempty, hb : b < sSup s ⊢ P`, plus `hex` |

where the new hypothesis is `hex : ∃ x ∈ s, b < x` (it contains `, `, so it is written here rather than
in the table; `guide_sync.py` splits a cell's hypotheses on `, `).

**R5 · `obtain ⟨_, ⟨N, rfl⟩, hN⟩ := hex`** changes the **context**. With `s = Set.range f`, `hex` is
`∃ x, (∃ y, f y = x) ∧ b < x`. The pattern takes it apart: `_` is `x`, `⟨N, rfl⟩` is the membership
`∃ y, f y = x` with `y` named `N`, and `rfl` substitutes `x := f N` everywhere, so `x` disappears. What is left
is an index `N` and `hN : b < f N`. Placeholders: `{α : Type} [LT α] (f : ℕ → α) (b : α)`.

Before: the context holds `hex : ∃ x ∈ Set.range f, b < x`, goal `⊢ P`.

| Before | After |
|---|---|
| `⊢ P` | `N : ℕ, hN : b < f N ⊢ P` |

and `hex` is gone.

### Choosing `N`

**R6 · `refine ⟨N, fun n hn => ?_⟩`** changes the **goal and the context**: the witness `N` is chosen, and the
remaining goal is the conclusion for an arbitrary `n` with `hn : n ≥ N`. `∀ n ≥ N, Q n` is
`∀ n, n ≥ N → Q n`, so the function takes two arguments. Placeholders: `(Q : ℕ → Prop) (N : ℕ)`.

| Before | After |
|---|---|
| `⊢ ∃ M, ∀ n ≥ M, Q n` | `n : ℕ, hn : n ≥ N ⊢ Q n` |

### Facts about one term `f n`

**R7 · `⟨n, rfl⟩`** proves `f n ∈ Set.range f`; with `have` it changes the **context**. Membership in
`Set.range f` is `∃ y, f y = f n`; the anonymous constructor gives the witness `n` and `rfl : f n = f n`.
`Set.mem_range_self n` is the same proof by name. Placeholders: `{α : Type} (f : ℕ → α) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P` | `hmem : f n ∈ Set.range f ⊢ P` |

**R8 · `le_csSup`** changes the **context** (via `have`). Statement:
`le_csSup : BddAbove s → x ∈ s → x ≤ sSup s`: the supremum is an upper bound. Typical use:
`le_csSup hb ⟨n, rfl⟩` (R7 as the second argument). Placeholders:
`{α : Type} [ConditionallyCompleteLattice α] (s : Set α) (x : α)` (`ℝ` qualifies).

| Before | After |
|---|---|
| `hbdd : BddAbove s, hx : x ∈ s ⊢ P` | `hbdd : BddAbove s, hx : x ∈ s, hle : x ≤ sSup s ⊢ P` |

**R9 · `hm hab`** with `hm : Monotone f` changes the **context** (via `have`). `Monotone f` *is* the statement
`∀ ⦃a b⦄, a ≤ b → f a ≤ f b`, so `hm` is applied to a proof `hab : a ≤ b` like a function. Since `n ≥ N` is
literally `N ≤ n`, `hm hn` gives `f N ≤ f n` (W3). Placeholders:
`{α β : Type} [Preorder α] [Preorder β] (f : α → β) (a b : α)` (types with `≤`; `ℕ`, `ℝ` qualify).

| Before | After |
|---|---|
| `hab : a ≤ b ⊢ P` | `hab : a ≤ b, hfab : f a ≤ f b ⊢ P` |

### Closing `|x - L| < ε`

**R10 · `rw [abs_sub_lt_iff]`** changes the **goal**: one absolute-value inequality becomes a conjunction of two
plain ones. Statement: `abs_sub_lt_iff : |a - b| < c ↔ a - b < c ∧ b - a < c`. `rw` with an `↔` replaces the
left side by the right. Then `constructor` splits the `∧` (TACTIC_STATES, "Structure"). Placeholders:
`{G : Type} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] (a b c : G)` (an additive group with a
compatible total order; `ℝ`, `ℤ`, `ℚ` qualify).

Before, then after (a goal block: a table cell cannot hold the `|` of `|x|` in code):

```lean-goal
⊢ |a - b| < c
⊢ a - b < c ∧ b - a < c
```

**R11 · `linarith`** **closes** a goal `t < s`, `t ≤ s`, `t = s` (or `False`) that follows from the hypotheses by
adding up linear inequalities. Nonlinear pieces such as `sSup (Set.range a)`, `a N`, `a n` are treated as
unknown atoms, which is all this exercise needs. It does not unfold definitions: the facts it uses
(R2, R5, R8, R9) must already be hypotheses. Placeholders: `(u v w e : ℝ)`.

| Before | After |
|---|---|
| `h1 : u - e < v, h2 : v ≤ w ⊢ u - w < e` | closed |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a value of `g : ℤ → ℝ` between `b` and the supremum.** From `hb : b < sSup (Set.range g)`,
`obtain ⟨_, ⟨k, rfl⟩, hk⟩ := exists_lt_of_lt_csSup (Set.range_nonempty g) hb` (R3, R4, R5) gives:

```lean-goal
⊢ ∃ k, b < g k ∧ g k ≤ sSup (Set.range g)
```

with `k : ℤ` and `hk : b < g k` in the context; `exact ⟨k, hk, le_csSup hg ⟨k, rfl⟩⟩` (R7, R8) closes it.

**W2: two one-sided bounds → one absolute value.** With `h1 : L - e < x`, `h2 : x ≤ y`, `h3 : y ≤ L`:
R10, then `constructor`, then R11 on each half:

```lean-goal
⊢ |L - y| < e
⊢ L - y < e ∧ y - L < e
⊢ L - y < e
⊢ y - L < e
```

**W3.** `example (f : ℕ → ℝ) (hm : Monotone f) (N n : ℕ) (hn : n ≥ N) : f N ≤ f n := hm hn` (R9).

---

## Traps

- The bans block Mathlib's limit library (`Tendsto`, `atTop`, filters, `tendsto_atTop_ciSup`, …): the `N`
  must be built by hand from the ε-N definition.
- `intro ε` alone leaves `ε > 0 → …` in the goal; `∀ ε > 0` needs two names, `intro ε hε`.
- `sSup` on `ℝ` is a total function: for an empty or unbounded set it is `0`. That is why `le_csSup` needs
  `BddAbove s` and `exists_lt_of_lt_csSup` needs `s.Nonempty`; supply them (`hb`, R3).
- `exists_lt_of_lt_csSup` gives an element `x ∈ Set.range a`, not an index. Use the `⟨N, rfl⟩` pattern
  (R5) to turn it into `a N`; a plain `⟨x, hx, hN⟩` leaves `hx : x ∈ Set.range a` and `hN : … < x`.
- `linarith` only sees hypotheses: state `a n ≤ sSup (Set.range a)` (R8) and `a N ≤ a n` (R9) with `have`
  before calling it.
- `linarith` cannot see inside `|·|`: rewrite with `abs_sub_lt_iff` (R10) first, then `constructor`.
- After `constructor`, `t ; linarith` runs `linarith` on the first goal only; use `<;>` or two bullets.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| open `∀ ε > 0, …` (even under a definition) | `intro ε hε` | R1 |
| `a - ε < a` from `0 < ε` | `sub_lt_self _ hε` | R2 |
| the range of a sequence is nonempty | `Set.range_nonempty a` | R3 |
| `b < sSup s` ⟹ some `x ∈ s` with `b < x` | `exists_lt_of_lt_csSup hs hb` | R4 |
| element of `Set.range a` → index `N` | `obtain ⟨_, ⟨N, rfl⟩, hN⟩ := …` | R5 |
| choose `N`, get `n`, `hn : n ≥ N` | `refine ⟨N, fun n hn => ?_⟩` | R6 |
| `a n ∈ Set.range a` | `⟨n, rfl⟩` | R7 |
| `x ≤ sSup s` | `le_csSup hb hx` | R8 |
| `a N ≤ a n` from `Monotone a`, `n ≥ N` | `hm hn` | R9 |
| `\|x - L\| < ε` → two inequalities | `rw [abs_sub_lt_iff]; constructor` | R10 |
| linear inequality from hypotheses | `linarith` | R11 |
| see the state | infoview | |
