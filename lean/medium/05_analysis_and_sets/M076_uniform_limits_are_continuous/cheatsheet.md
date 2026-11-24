# M076 · Uniform limits are continuous: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ` and absolute
value `|x|`, binder notation `∀ ε > 0`, `∃ δ > 0`, `∀ n ≥ N`, the triangle inequality `abs_add_three`, and
the tactics `obtain`, `calc`, `positivity`, `ring_nf`, `gcongr`.

## How to read an entry

Each entry is one tactic or one lemma used with `have`/`exact`/`rw`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`.
- `G : Prop` is an arbitrary goal. Some lemmas here are *forward* facts: `have h := lemma args` adds `h`
  to the context; in the guide a hypothesis `k : … → G` then consumes it.
- `Q`, `R`, `A`, `B` are arbitrary predicates (`Q : ℝ → Prop`, `R : ℝ → ℝ → Prop`, …): "some property".
- Placeholders are written as Lean binders. The lemmas here are stated in Mathlib for general ordered
  types (type-class brackets such as `[AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]`: "`+`, `-`,
  `0`, a total order, and `+` respects the order"); `ℝ` meets every one of them, so the entries use `ℝ`
  directly.
- A goal or hypothesis containing `|` (absolute value) cannot sit in a table cell; it is shown in a
  `lean-goal` block (one goal per line: before, then after) or in the text.
- Every `⊢` cell and every `lean-goal` line is a state Lean reaches in the companion file;
  `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | the real numbers (Mathlib's `Real`) |
| `f : ℝ → ℝ`, `f y` | a real function and its value at `y` |
| `F : ℕ → ℝ → ℝ`, `F n x` | a sequence of functions: `F n` is the `n`-th function, `F n x` its value at `x` |
| `\|x\|` | absolute value of `x` (Mathlib's `abs x`) |
| `ε > 0` | notation for `0 < ε` (`>` is `<` flipped) |
| `n ≥ N` | notation for `N ≤ n` |
| `ε / 3` | real division; `ε / 3 + ε / 3 + ε / 3 = ε` is a ring identity (R13) |
| `∀ ε > 0, Q ε` | `∀ ε, ε > 0 → Q ε`: `intro ε hε` takes both (R1) |
| `∃ δ > 0, Q δ` | `∃ δ, δ > 0 ∧ Q δ`: take apart with `obtain ⟨δ, hδ, hc⟩` (R4), build with `⟨δ, hδ, proof⟩` (R5) |
| `∀ n ≥ N, ∀ (x : ℝ), Q n x` | apply it as `hN n hn x`, with `hn : n ≥ N` (R7) |
| `ContAt f x` | the exercise's ε-δ continuity of `f` at `x`; it unfolds by itself under `intro` and when applied |
| `UnifConv F f` | the exercise's uniform convergence: one `N` per `ε`, valid for every `x` |
| `ForallPos Q`, `SomeIndex Q` | toy definitions in the guide, shaped like `ContAt` and `UnifConv` |

---

## Part 1 · `uniform_limit_contAt`

Statement: if every `F n` is continuous at every point (`hF`) and `F n → f` uniformly (`hu`), then `f` is
continuous at `x`: for every `ε > 0` there is `δ > 0` with `|y - x| < δ → |f y - f x| < ε`.

The plan (the ε/3 argument). Given `ε > 0`, pick one index `N` with `|F N z - f z| < ε / 3` for **every**
`z` (uniform convergence), then a `δ > 0` from the continuity of that single function `F N` at `x`, with
tolerance `ε / 3`. For `|y - x| < δ`:

$$|f y - f x| \le |f y - F_N y| + |F_N y - F_N x| + |F_N x - f x| < \tfrac{ε}{3} + \tfrac{ε}{3} + \tfrac{ε}{3} = ε.$$

The first and third terms use the same `N` at two different points `y` and `x`; that is exactly what
*uniform* buys you.

### Taking the hypotheses apart, building the `∃ δ`

**R1 · `intro ε hε`** changes the **goal and the context**. A goal whose definition unfolds to
`∀ ε > 0, Q ε` (here `ContAt f x`) is introduced directly: `intro` unfolds the definition by itself.
Placeholders: `(Q : ℝ → Prop)`, `def ForallPos (Q) : Prop := ∀ ε > 0, Q ε`.

| Before | After |
|---|---|
| `⊢ ForallPos Q` | `ε : ℝ, hε : ε > 0 ⊢ Q ε` |

**R2 · `obtain ⟨N, hN⟩ := h (e / 3) (by positivity)`** changes the **context**. Applying `h` to `e / 3`
unfolds its definition (here `SomeIndex Q`, in the exercise `UnifConv F f`) to `e / 3 > 0 → ∃ N, …`; the
second argument `(by positivity)` (R3) proves `e / 3 > 0`, and `obtain ⟨N, hN⟩` splits the `∃` into the
witness `N` and its property `hN`. Placeholders: `(Q : ℝ → ℕ → Prop)`,
`def SomeIndex (Q) : Prop := ∀ ε > 0, ∃ N : ℕ, Q ε N`, `(e : ℝ) (he : e > 0)`.

| Before | After |
|---|---|
| `h : SomeIndex Q, he : e > 0 ⊢ G` | `N : ℕ, hN : Q (e / 3) N ⊢ G` |

**R3 · `positivity`** **closes** a goal `0 < t` or `t > 0` when `t` is built from pieces it knows are
positive (numerals, hypotheses `he : e > 0` in the context) by `+`, `*`, `/`, … It needs `hε` in the
context, so do R1 first. Placeholders: `(e : ℝ)`.

| Before | After |
|---|---|
| `he : e > 0 ⊢ e / 3 > 0` | no goals |

**R4 · `obtain ⟨δ, hδ, hc⟩ := h`** changes the **context**. `∃ δ > 0, Q δ` is `∃ δ, δ > 0 ∧ Q δ`, so the
pattern has three parts: the witness, the proof of `δ > 0`, the property. In the exercise `h` is
`hF N x (ε / 3) (by positivity)`: `hF N x : ContAt (F N) x` unfolds when applied, as in R2.
Placeholders: `(Q : ℝ → Prop)`.

| Before | After |
|---|---|
| context has `h : ∃ δ > 0, Q δ`; `⊢ G` | `h` is gone; `δ : ℝ, hδ : δ > 0, hc : Q δ ⊢ G` |

**R5 · `refine ⟨δ, hδ, fun y hy => ?_⟩`** changes the **goal and the context**: it gives the witness `δ`
and its proof `hδ` for `∃ d > 0`, and introduces the `y` and the hypothesis `hy` of the `∀ y, R y d → …`
that follows; `?_` is the remaining goal. In the exercise `R y d` is `|y - x| < d` and `P y` is
`|f y - f x| < ε`. Placeholders: `(R : ℝ → ℝ → Prop) (P : ℝ → Prop) (δ : ℝ) (hδ : δ > 0)`.

| Before | After |
|---|---|
| `⊢ ∃ d > 0, ∀ (y : ℝ), R y d → P y` | `y : ℝ, hy : R y δ ⊢ P y` |

**R6 · `have h2 := hc y hy`** changes the **context**: it instantiates `hc : ∀ y, A y → B y` at `y`, with
`hy` as the proof of the premise. In the exercise this gives `|F N y - F N x| < ε / 3`.
Placeholders: `(A B : ℝ → Prop) (y : ℝ)`.

| Before | After |
|---|---|
| `hy : A y ⊢ B y` | `h2 : B y ⊢ B y` |

**R7 · `le_rfl`** proves `a ≤ a`. Since `N ≥ N` is `N ≤ N`, it is the side condition when you instantiate
`hN : ∀ n ≥ N, ∀ x, Q n x` at `n := N` itself: `hN N le_rfl z`. Do it twice, at `z := y` and at `z := x`:
the same `N` serves both points. Changes the **context**. Placeholders: `(Q : ℕ → ℝ → Prop) (N : ℕ) (z : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `h1 : Q N z ⊢ G` |

### The ε/3 chain

**R8 · `calc`** **closes** the goal `a < e` with a chain of steps, each with its own proof (a term, or
`by tac`). The relations compose: `=` then `≤` then `<` then `=` gives `<`. Write the first term after
`calc`, each later line as `_ rel next := proof`, indented under the first. Placeholders: `(a b c d e : ℝ)`.

| Before | After |
|---|---|
| `h1 : a = b, h2 : b ≤ c, h3 : c < d, h4 : d = e ⊢ a < e` | no goals |

**R9 · `ring_nf`** **closes** an equation whose two sides agree after normalising every ring expression,
also inside a function application such as `|·|`. Use it for the first `calc` step
`|f y - f x| = |(f y - F N y) + (F N y - F N x) + (F N x - f x)|`; `ring` fails there (it does not look
inside `|·|`). Lean prints `(a - b) + (b - c)` without the first parentheses, since `+` groups to the left.
Placeholders: `(g : ℝ → ℝ) (a b c d : ℝ)`.

| Before | After |
|---|---|
| `⊢ g (a - d) = g (a - b + (b - c) + (c - d))` | no goals |

**R10 · `abs_add_three`** changes the **context**. The lemma is
`abs_add_three a b c : |a + b + c| ≤ |a| + |b| + |c|`, the triangle inequality for three terms. As a `calc`
step write `abs_add_three _ _ _` (Lean fills `a b c` from the step). Placeholders: `(a b c : ℝ)`.

| Before | After `have h := abs_add_three a b c` |
|---|---|
| `⊢ G` | context gains `h : \|a + b + c\| ≤ \|a\| + \|b\| + \|c\|`; goal `G` unchanged |

**R11 · `rw [abs_sub_comm a]`** changes the **goal**. The lemma is `abs_sub_comm a b : |a - b| = |b - a|`.
Giving the first argument `a` makes `rw` flip only `|a - _|`. In the exercise the split gives
`|f y - F N y|` while the hypothesis is `|F N y - f y| < ε / 3`: `rw [abs_sub_comm (f y)]`.
Placeholders: `(a b : ℝ)`.

```lean-goal
⊢ P |a - b|
⊢ P |b - a|
```

**R12 · `gcongr`** changes the **goal list**: on `a + b + c < d + e + f` it reduces the goal to the pieces
`a < d`, `b < e`, `c < f` ("generalized congruence": `+` is monotone in each argument). It closes each piece
at once when some hypothesis states it **exactly**; any other piece is handed back as a new goal (W2).
Placeholders: `(a b c d e f : ℝ)`.

| Before | After |
|---|---|
| `h1 : a < d, h2 : b < e, h3 : c < f ⊢ a + b + c < d + e + f` | no goals |

**R13 · `ring`** **closes** an identity of commutative rings; division by a numeral is fine in `ℝ`. Use it
for the last `calc` step `ε / 3 + ε / 3 + ε / 3 = ε`. Placeholders: `(e : ℝ)`.

| Before | After |
|---|---|
| `⊢ e / 4 + e / 4 + e / 2 = e` | no goals |

### Worked combinations (W1–W2, on numbers, not functions)

**W1: the ε/3 split on four reals** `u v w z` with `|u - v|`, `|w - v|`, `|w - z|` all `< e / 3`. One `calc`
chains R9, R10, R11 + R12, R13 and closes

```lean-goal
⊢ |u - z| < e
```

**W2: what `gcongr` hands back when a hypothesis is flipped.** With `h2 : |w - v| < e / 3` but the summand
`|v - w|`, `gcongr` closes the first and third pieces and leaves the middle one; R11 then matches it to `h2`:

```lean-goal
⊢ |u - v| + |v - w| + |w - z| < e / 3 + e / 3 + e / 3
⊢ |v - w| < e / 3
⊢ |w - v| < e / 3
```

---

## Traps

- **Uniform, not pointwise.** In `UnifConv` one `N` works for every `x` at once. Choose `N` first (R2),
  then `δ` from `F N` (R4), then `y` (R5): `δ` depends on `N`, and `y` on `δ`. If `N` could depend on the
  point, you would need it at `y`, which is only chosen after `δ`; the argument would be circular.
- Instantiate `hN` at the same index you took `δ` from: `hN N le_rfl y` and `hN N le_rfl x` (R7), not at
  some other `n ≥ N`.
- `hu (ε / 3)` alone is a function still waiting for a proof of `ε / 3 > 0`: write
  `hu (ε / 3) (by positivity)` (R2, R3), after `intro ε hε` (R1).
- `ring` does not look inside `|·|`: the first `calc` step needs `ring_nf` (R9).
- `gcongr` closes a piece only from a hypothesis with exactly that statement. `|f y - F N y|` and
  `|F N y - f y|` are different text: flip with `rw [abs_sub_comm (f y)]` first (R11, W2).
- The `have`s `h1 h2 h3` must be in the context **before** the `calc` step that calls `gcongr`; it looks
  only at hypotheses present at that point.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| open `∀ ε > 0, …` (also behind `ContAt`) | `intro ε hε` | R1 |
| use `∀ ε > 0, ∃ N, …` at `ε / 3` | `obtain ⟨N, hN⟩ := hu (ε / 3) (by positivity)` | R2, R3 |
| `0 < ε / 3` | `positivity` | R3 |
| take apart `∃ δ > 0, …` | `obtain ⟨δ, hδ, hc⟩ := …` | R4 |
| prove `∃ δ > 0, ∀ y, … → …` | `refine ⟨δ, hδ, fun y hy => ?_⟩` | R5 |
| instantiate `∀ y, A y → B y` | `have h2 := hc y hy` | R6 |
| instantiate `∀ n ≥ N, ∀ x, …` at `n := N` | `have h1 := hN N le_rfl y` | R7 |
| chain `=`, `≤`, `<` | `calc a = b := … _ ≤ c := … _ < d := …` | R8 |
| regroup inside `\|·\|` | `by ring_nf` | R9 |
| triangle inequality, 3 terms | `abs_add_three _ _ _` | R10 |
| flip `\|a - b\|` to `\|b - a\|` | `rw [abs_sub_comm a]` | R11 |
| sum `<` sum from termwise hypotheses | `gcongr` | R12 |
| `ε / 3 + ε / 3 + ε / 3 = ε` | `by ring` | R13 |
| see the state | infoview | |
