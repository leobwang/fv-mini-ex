# M068 · Limit of a sum: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `obtain` (E005, E007) and `calc` (E020).
**New here:** Mathlib's real numbers `ℝ`, absolute value `|x|`, `max` on `ℕ`, the lemmas `abs_add_le`
(triangle inequality), `le_of_max_le_left/right`, `add_lt_add`, `calc` mixing `=`, `≤`, `<` on `ℝ` from a
beta-reduced first term, and the tactics `positivity`, `ring_nf`, `ring`. Convergence is the exercise's own
ε-N definition `ConvergesTo`, not Mathlib's filters (`Filter.Tendsto`, which is banned here).

## How to read an entry

Each entry is one tactic or one lemma used with `exact`/`obtain`/`calc`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). A bare `G : Prop` is "whatever the goal is" in entries that
  only change the context; `S : ℕ → Prop` is "the inequality for one index `n`".
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[LinearOrder α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it; `ℝ` meets all of them.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. States that
  contain `|·|` are shown in `lean-goal` blocks, because `|` would break a table.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (a complete ordered field; not floating point) |
| `ℕ → ℝ` | a real sequence `a₀, a₁, …`; `a n` is the term `aₙ` |
| `ConvergesTo a L` | the exercise's definition: for every `ε > 0` there is `N : ℕ` with `\|a n - L\| < ε` for all `n ≥ N` |
| `∀ ε > 0, Q ε` | `∀ ε, ε > 0 → Q ε`: `intro` takes two names (R1) |
| `∃ N, ∀ n ≥ N, S n` | some `N` works for all `n ≥ N`, i.e. `∀ n, n ≥ N → S n` (R4) |
| `ε > 0`, `n ≥ N` | `0 < ε`, `N ≤ n` (`>`, `≥` are `<`, `≤` with the sides swapped) |
| `\|x\|` | `abs x`, the absolute value `max x (-x)` |
| `max N1 N2` | the larger of `N1` and `N2` (here on `ℕ`) |
| `ε / 2` | real division; `ε / 2 + ε / 2 = ε` by `ring` (R12) |
| `(fun n => a n + b n) n` | the sum sequence applied to `n`, not yet beta-reduced to `a n + b n`; `calc` may start from the reduced form (R8) |

---

## Part 1 · `converges_add`

Statement: if `a n → La` and `b n → Lb` (both in the sense of `ConvergesTo`), then `a n + b n → La + Lb`.
The math: given `ε > 0`, ask `a` for precision `ε / 2` (get `N1`) and `b` for `ε / 2` (get `N2`). For
`n ≥ max N1 N2` both bounds hold, and

  `|a n + b n - (La + Lb)| = |(a n - La) + (b n - Lb)| ≤ |a n - La| + |b n - Lb| < ε/2 + ε/2 = ε`.

After R1 (`intro ε hε`) the goal is `∃ N, ∀ n ≥ N, |(fun n => a n + b n) n - (La + Lb)| < ε`.

### Opening the ε-N statement

**R1 · `intro ε hε`** changes the **goal and the context**. `intro` unfolds a definition by itself when its body
starts with `∀`, so `ConvergesTo … …` needs no `unfold` first. `∀ ε > 0, Q ε` is two binders: `ε : ℝ` and
`hε : ε > 0`. Placeholders: `(Q : ℝ → Prop)`, and `AllPos Q := ∀ ε > 0, Q ε` as the named definition.

| Before | After |
|---|---|
| `⊢ AllPos Q` | `ε : ℝ, hε : ε > 0 ⊢ Q ε` |

### Asking a hypothesis for precision `ε / 2`

**R2 · `positivity`** **closes** `0 < e / 2`. It proves `0 < t`, `0 ≤ t` or `t ≠ 0` for `t` built from positive
pieces (numerals, `+`, `*`, `/`); for a variable such as `e` it uses a hypothesis `he : e > 0` from the context.
`e / 2 > 0` is the same statement as `0 < e / 2`. Placeholders: `(e : ℝ) (he : e > 0)`.

| Before | After |
|---|---|
| `he : e > 0 ⊢ 0 < e / 2` | closed |

**R3 · `obtain ⟨K, hK⟩ := h (e / 2) (by positivity)`** changes the **context**. A hypothesis
`h : ∀ e > 0, ∃ N, …` is a function of two arguments: the number `e / 2` and a proof of `e / 2 > 0` (R2). The
result `∃ N, …` is taken apart by `obtain` into a witness `K` and its property `hK`. Here `ha : ConvergesTo a La`
is such a hypothesis (Lean unfolds the definition when you apply it). Placeholders:
`(S : ℝ → ℕ → Prop) (h : ∀ e > 0, ∃ N : ℕ, ∀ n ≥ N, S e n) (e : ℝ) (he : e > 0)`.

| Before | After |
|---|---|
| `⊢ G` | `K : ℕ ⊢ G`, plus `hK : ∀ n ≥ K, S (e / 2) n` |

Do it twice, once with `ha` (giving `N1`, `h1`) and once with `hb` (`N2`, `h2`). Then
`h1 : ∀ n ≥ N1, |a n - La| < ε / 2`.

### One `N` for both sequences: `max`

**R4 · `refine ⟨max K M, fun k hk => ?_⟩`** changes the **goal and the context**: the witness `max K M` is
chosen, and the `∀ n ≥ N` part is proved by a function whose body `?_` is left as the goal. Placeholders:
`(S : ℕ → Prop) (K M : ℕ)`.

| Before | After |
|---|---|
| `⊢ ∃ N, ∀ n ≥ N, S n` | `k : ℕ, hk : k ≥ max K M ⊢ S k` |

**R5 · `have e := h k hk`** changes the **context**: applying `h : ∀ n ≥ K, S n` to `k` and a proof of `k ≥ K`
gives `S k`. Without a type after `have`, Lean takes the type of the term. Placeholders:
`(S : ℕ → Prop) (K k : ℕ) (h : ∀ n ≥ K, S n) (hk : k ≥ K)`.

| Before | After |
|---|---|
| `⊢ G` | `e : S k ⊢ G` |

The proof of `n ≥ N1` comes from `hn : n ≥ max N1 N2` by R6 (and `n ≥ N2` by R7), so write
`have e1 := h1 n (le_of_max_le_left hn)`.

**R6 · `le_of_max_le_left`** **closes** `K ≤ k`. The lemma is `le_of_max_le_left : max a b ≤ c → a ≤ c`.
`k ≥ max K M` is notation for `max K M ≤ k`, so `hk` fits as it is, and `K ≤ k` is the same as `k ≥ K`.
Placeholders: `(K M k : ℕ) (hk : k ≥ max K M)`; in general `{α : Type} [LinearOrder α] {a b c : α}`, which `ℕ`,
`ℤ`, `ℚ`, `ℝ` meet.

| Before | After |
|---|---|
| `hk : k ≥ max K M ⊢ K ≤ k` | closed |

**R7 · `le_of_max_le_right`** **closes** `M ≤ k`. The lemma is `le_of_max_le_right : max a b ≤ c → b ≤ c`.
Placeholders as in R6.

| Before | After |
|---|---|
| `hk : k ≥ max K M ⊢ M ≤ k` | closed |

### The estimate: a `calc` chain

**R8 · `calc`** **closes** the goal by a chain of steps, each with its own proof:

```
calc f k + 1 = b := proof of f k + 1 = b
  _ ≤ c := proof of b ≤ c
  _ < d := proof of c < d
```

`_` stands for the previous right-hand side. Lean composes the relations (`=` then `≤` then `<` gives `<`),
and the result must match the goal. The first term may be the goal's left side **beta-reduced** (the
`fun` applied to its argument, written out): the example's goal says `(fun n => f n + 1) k` and the chain
starts from `f k + 1`; in the exercise write `|a n + b n - (La + Lb)|` for the goal's
`|(fun n => a n + b n) n - (La + Lb)|`. Indent the `_` lines further than `calc`. Placeholders:
`(f : ℕ → ℝ) (k : ℕ) (b c d : ℝ) (h1 : f k + 1 = b) (h2 : b ≤ c) (h3 : c < d)`.

| Before | After |
|---|---|
| `h1 : f k + 1 = b, h2 : b ≤ c, h3 : c < d ⊢ (fun n => f n + 1) k < d` | closed |

**R9 · `ring_nf`** **closes** the regrouping step. It puts every ring expression in normal form, inside `|·|`
too, so both sides become the same term. Placeholders: `(x y u v : ℝ)`.

```lean-goal
⊢ |x + y - (u + v)| = |x - u + (y - v)|
```

Lean prints `(x - u) + (y - v)` as `x - u + (y - v)`: `+` groups to the left, so the first brackets are not
needed.

**R10 · `abs_add_le`** **closes** the triangle inequality. The lemma is `abs_add_le (a b : α) : |a + b| ≤ |a| + |b|`.
Placeholders: `(a b : ℝ)`; in general `{α : Type} [Lattice α] [AddCommGroup α] [AddLeftMono α]`, which `ℤ`, `ℚ`,
`ℝ` meet. As a `calc` step proof write `abs_add_le _ _`: Lean reads `a`, `b` off the step.

```lean-goal
⊢ |a + b| ≤ |a| + |b|
```

**R11 · `add_lt_add`** **closes** a sum of two strict inequalities. The lemma is
`add_lt_add : a < b → c < d → a + c < b + d`. Placeholders: `(a b c d : ℝ) (h1 : a < b) (h2 : c < d)`; in general
`{α : Type} [Add α] [Preorder α] [AddLeftStrictMono α] [AddRightStrictMono α]`, which `ℕ`, `ℤ`, `ℚ`, `ℝ` meet.

| Before | After |
|---|---|
| `h1 : a < b, h2 : c < d ⊢ a + c < b + d` | closed |

**R12 · `ring`** **closes** `e / 2 + e / 2 = e`. In a field such as `ℝ` it treats `e / 2` as `e * 2⁻¹` and
handles the numeral. `add_halves : a / 2 + a / 2 = a` is the lemma form. Placeholders: `(e : ℝ)`.

| Before | After |
|---|---|
| `⊢ e / 2 + e / 2 = e` | closed |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: two "eventually" properties hold together.** From `hS : ∃ K, ∀ k ≥ K, S k` and
`hT : ∃ M, ∀ k ≥ M, T k`: `obtain` both (R3 without the `e / 2`), `refine ⟨max K M, fun k hk => ?_⟩` (R4), then
`have e1 := hK k (le_of_max_le_left hk)` and `have e2 := hM k (le_of_max_le_right hk)` (R5 with R6, R7), and
`exact ⟨e1, e2⟩`.

| Before | After R4 |
|---|---|
| `⊢ ∃ N, ∀ n ≥ N, S n ∧ T n` | `hk : k ≥ max K M ⊢ S k ∧ T k` |

**W2: triangle inequality through a middle point `y`,** from `h1 : |x - y| < e / 3` and
`h2 : |y - z| < 2 * e / 3`. One `calc` (R8): regroup with `ring_nf` (R9), `abs_add_le _ _` (R10),
`add_lt_add h1 h2` (R11), then `ring` for `e / 3 + 2 * e / 3 = e` (R12).

```lean-goal
⊢ |x - z| < e
```

---

## Traps

- Asking both hypotheses for `ε` itself gives `< ε + ε`, which is too weak. Ask for `ε / 2` (R3).
- One `N` must serve both sequences: `N1` alone or `N2` alone is not enough. Take `max N1 N2` (R4) and get
  each bound back with R6, R7.
- `obtain ⟨N1, h1⟩ := ha (ε / 2) (by positivity)` needs `hε` in the context, which `positivity` uses (R2). Do
  R1 first.
- `ring` on the regrouping step `|…| = |…|` does not close it as `ring`: it falls back to `ring_nf` and prints
  `Try this: ring_nf`. Write `ring_nf` (R9).
- The goal shows `(fun n => a n + b n) n`. Start the `calc` from `|a n + b n - (La + Lb)|`; Lean accepts it
  because the two are equal by beta reduction (R8).
- `Filter.Tendsto.add` and `tendsto_add` are banned: the point is the ε-N argument.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| open `∀ ε > 0, …` | `intro ε hε` | R1 |
| `0 < ε / 2` from `hε` | `positivity` | R2 |
| use a convergence hypothesis at `ε / 2` | `obtain ⟨N1, h1⟩ := ha (ε / 2) (by positivity)` | R3 |
| one `N` for two sequences | `refine ⟨max N1 N2, fun n hn => ?_⟩` | R4 |
| instance of `∀ n ≥ N, S n` | `have e := h n proof` | R5 |
| `N1 ≤ n` / `N2 ≤ n` from `n ≥ max N1 N2` | `le_of_max_le_left hn` / `le_of_max_le_right hn` | R6, R7 |
| chain `=`, `≤`, `<` | `calc … = … := … _ ≤ … := … _ < … := …` | R8 |
| regroup inside `\|·\|` | `by ring_nf` | R9 |
| `\|a + b\| ≤ \|a\| + \|b\|` | `abs_add_le _ _` | R10 |
| add two strict inequalities | `add_lt_add h1 h2` | R11 |
| `ε / 2 + ε / 2 = ε` | `by ring` | R12 |
| see the state | infoview | |
