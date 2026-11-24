# M067 · 1/(n+1) tends to 0: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, the cast `ℕ → ℝ`,
absolute value `|x|`, the Archimedean property `exists_nat_gt`, the division lemma `div_lt_iff₀`, and the
tactics `simpa`, `obtain`, `exact_mod_cast`, `positivity`, `nlinarith`. Convergence is the exercise's own
ε-N definition `ConvergesTo`, not Mathlib's filters.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`obtain`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. A bare `G : Prop` is "whatever the goal is" in entries that only change the context.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Lattice α]` is a
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
| `∀ n ≥ N, S n` | `∀ n, n ≥ N → S n`: a `fun` takes two names (R2) |
| `ε > 0`, `n ≥ N` | `0 < ε`, `N ≤ n` (`>`, `≥` are `<`, `≤` with the sides swapped) |
| `↑n` | the natural number `n` cast to `ℝ` (`Nat.cast`); `(n : ℝ)` in source code |
| `\|x\|` | `abs x`, the absolute value `max x (-x)` |
| `(fun n => 1 / (↑n + 1)) n` | the sequence applied to `n`, not yet beta-reduced to `1 / (↑n + 1)`; `rw` and `positivity` see through it |
| `(fun x => c) n` | the constant sequence `c` applied to `n`; Lean prints `fun _ => c` as `fun x => c` |
| `x✝ : n ≥ 0` | an unnamed hypothesis (you wrote `_`); it cannot be referred to by name |

---

## Part 1 · `const_converges`

Statement: for every real `c`, the constant sequence `n ↦ c` converges to `c`: for every `ε > 0` there is an
`N` with `|c - c| < ε` for all `n ≥ N`. Any `N` works (take `0`), because `|c - c| = 0 < ε`.

**R1 · `intro ε hε`** changes the **goal and the context**. `intro` unfolds a definition by itself when its body
starts with `∀`, so `ConvergesTo a L` needs no `unfold` first. `∀ ε > 0, Q ε` is two binders: `ε : ℝ` and
`hε : ε > 0`. Placeholders: `(Q : ℝ → Prop)`, and `AllPos Q := ∀ ε > 0, Q ε` as the named definition.

| Before | After |
|---|---|
| `⊢ AllPos Q` | `ε : ℝ, hε : ε > 0 ⊢ Q ε` |

**R2 · `refine ⟨K, fun k hk => ?_⟩`** changes the **goal and the context**: the witness `K` is chosen, and the
`∀ n ≥ N` part is proved by a function whose body `?_` is left as the goal. Placeholders: `(S : ℕ → Prop)`
(the inequality for one `n`) and `(K : ℕ)`. Write `fun k _ => ?_` when the bound `k ≥ K` is not needed (Part 1).

| Before | After |
|---|---|
| `⊢ ∃ N, ∀ n ≥ N, S n` | `k : ℕ, hk : k ≥ K ⊢ S k` |

**R3 · `simp`** changes the **goal**. It beta-reduces `(fun _ => a) k` to `a`, then uses
`sub_self : a - a = 0` and `abs_zero : |0| = 0`. Placeholders: `(a e : ℝ) (k : ℕ)`.

```lean-goal
⊢ |(fun x => a) k - a| < e
⊢ 0 < e
```

**R4 · `simpa using h`** **closes** the goal. It runs `simp` on the goal and on `h`, then finishes with
`exact h`. `simp` also rewrites `e > 0` as `0 < e`, so `h : e > 0` matches the simplified goal of R3.
Placeholders: `(a e : ℝ) (k : ℕ) (h : e > 0)`.

```lean-goal
⊢ |(fun x => a) k - a| < e
```

---

## Part 2 · `inv_succ_converges`

Statement: `1 / (n + 1) → 0`: for every `ε > 0` there is an `N` with `|1 / (n + 1) - 0| < ε` for all `n ≥ N`.
The math: choose `N > 1 / ε` (Archimedean property). Then `N ε > 1`, and for `n ≥ N`,
`ε (n + 1) > ε N > 1`, so `1 / (n + 1) < ε`. The term is positive, so `|1 / (n + 1) - 0| = 1 / (n + 1)`.

R1 opens the definition as in Part 1. Get `N` **before** R2, so you can name it in the witness.

### Choosing `N`: the Archimedean property

**R5 · `obtain ⟨x, hx⟩ := e`** changes the **context**: from `e : ∃ x, Q x` it adds a witness `x` and its
property `hx : Q x` (and removes `e`). Placeholders: `{α : Type} (Q : α → Prop) (e : ∃ x, Q x)`.

| Before | After |
|---|---|
| `⊢ G` (with `e` in the context) | `x : α, hx : Q x ⊢ G` (`e` is gone) |

**R6 · `exists_nat_gt`** changes the **context** when used with R5. The lemma is
`exists_nat_gt (x : R) : ∃ n : ℕ, x < ↑n`: every element is below some natural number (the Archimedean
property). Placeholders: `(x : ℝ)`; in general `{R : Type} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
[Archimedean R]`, which `ℝ` and `ℚ` meet. Apply it to `1 / ε`.

| Before | After `obtain ⟨K, hK⟩ := exists_nat_gt x` |
|---|---|
| `⊢ G` | `K : ℕ, hK : x < ↑K ⊢ G` |

Then R2 with witness `N`: the context gains `n : ℕ` and `hn : n ≥ N`.

**R7 · `have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab`** changes the **context**: it turns the `ℕ` fact
`hab : b ≥ a` into the same fact about the casts `↑a ≤ ↑b` in `ℝ` (lemma `Nat.cast_le`, applied for you).
`nlinarith` works in `ℝ` and cannot use the `ℕ` fact. Placeholders: `(a b : ℕ) (hab : b ≥ a)`.

| Before | After |
|---|---|
| `hab : b ≥ a ⊢ G` | `hab' : ↑a ≤ ↑b ⊢ G` |

### Simplifying `|x - 0| < ε`

**R8 · `rw [sub_zero]`** changes the **goal**. The lemma is `sub_zero : a - 0 = a`. Placeholders: `(a : ℝ)`; in
general `{G : Type} [SubNegZeroMonoid G]`, which `ℤ`, `ℚ`, `ℝ`, `ℂ` meet.

| Before | After |
|---|---|
| `⊢ P (a - 0)` | `⊢ P a` |

**R9 · `rw [abs_of_pos]`** changes the **goal list**. The lemma is `abs_of_pos : 0 < a → |a| = a`, so the goal is
rewritten and a side goal `0 < a` is added. Write `rw [abs_of_pos (by positivity)]` to close it on the spot
(R10). Placeholders: `(a : ℝ)`; in general `{α : Type} [Lattice α] [AddGroup α] [AddLeftMono α]`, which `ℤ`,
`ℚ`, `ℝ` meet.

```lean-goal
⊢ P |a|
⊢ P a
⊢ 0 < a
```

The first line is before; the last two are the two goals after.

**R10 · `positivity`** **closes** `0 < e`, `0 ≤ e` or `e ≠ 0` when `e` is built from positive pieces: numerals,
casts `↑k` of naturals, `+`, `*`, `/`. It sees through `(fun n => …) n`, which is the form of the side goal
of R9 and R11 here. Example with `(k : ℕ)`:

| Before | After |
|---|---|
| `k : ℕ ⊢ 0 < (fun k => 2 / (↑k + 3)) k` | closed |

### Clearing the denominator

**R11 · `rw [div_lt_iff₀ hc]`** changes the **goal**. The lemma is
`div_lt_iff₀ : 0 < c → (b / c < a ↔ b < a * c)`. Note the order of the product: `a * c`, the right-hand side
first. Placeholders: `(a b c : ℝ) (hc : 0 < c)`; in general `{G₀ : Type} [GroupWithZero G₀] [PartialOrder G₀]
[MulPosReflectLT G₀]`, which `ℚ` and `ℝ` meet. In the goal the denominator is `↑n + 1`: prove
`0 < ↑n + 1` with `(by positivity)`.

| Before | After |
|---|---|
| `⊢ b / c < a` | `⊢ b < a * c` |

**R12 · `rw [div_lt_iff₀ hc] at hb`** changes the **context**: `at hb` rewrites the hypothesis `hb` instead of the
goal. Use it on `hN : 1 / ε < ↑N` with `hε`. Placeholders as in R11, with `(hb : b / c < a)`.

| Before | After |
|---|---|
| `hb : b / c < a ⊢ G` | `hb : b < a * c ⊢ G` |

### Finishing

**R13 · `nlinarith`** **closes** an inequality that follows from the hypotheses after multiplying pairs of them.
`linarith` adds hypotheses only with constant coefficients, so from `x ≤ y` and `0 < e` it cannot get
`e * x ≤ e * y`; `nlinarith` multiplies `y - x ≥ 0` by `e > 0` and finds it. Placeholders:
`(x y e : ℝ) (he : 0 < e) (hxy : x ≤ y) (h1 : 1 < x * e)`.

| Before | After |
|---|---|
| `he : 0 < e, hxy : x ≤ y, h1 : 1 < x * e ⊢ 1 < e * (y + 2)` | closed |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: eventually `5 < k`.** `obtain ⟨K, hK⟩ := exists_nat_gt (5 : ℝ)` (R5, R6), `refine ⟨K, fun k hk => ?_⟩`
(R2), cast `hk` (R7), then `linarith` (linear: no product needed):

```lean-goal
⊢ ∃ K, ∀ k ≥ K, 5 < ↑k
⊢ 5 < ↑k
```

**W2: one bound for `2 / (k + 3)`,** given `hK : 2 / e < ↑K` and `hk : ↑K ≤ ↑k`. R8, R9 with R10, R11 with R10,
R12, R13:

```lean-goal
⊢ |2 / (↑k + 3) - 0| < e
⊢ |2 / (↑k + 3)| < e
⊢ 2 / (↑k + 3) < e
⊢ 2 < e * (↑k + 3)
```

After R12, `hK : 2 < ↑K * e`, and `nlinarith` closes `2 < e * (↑k + 3)`.

---

## Traps

- Get `N` (R5, R6) **before** `refine ⟨N, …⟩` (R2): the witness must already be in the context.
- `exists_nat_gt (1 / ε)` gives `1 / ε < ↑N` with a division. Clear it with R12 so `nlinarith` sees a product
  `↑N * ε`, not a quotient.
- `hn : n ≥ N` lives in `ℕ`; the goal lives in `ℝ`. Cast it first (R7), or `nlinarith` cannot use it.
- `div_lt_iff₀` needs `0 < c` for the denominator, so always pass a proof: `hε` or `(by positivity)`.
- The product in `div_lt_iff₀` is `a * c` (right-hand side times denominator): the goal becomes
  `1 < ε * (↑n + 1)` and `hN` becomes `1 < ↑N * ε`. `nlinarith` does not care about the order.
- `linarith` fails on the last step: `ε * ↑n` is a product of two unknowns (R13).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| open `∀ ε > 0, …` | `intro ε hε` | R1 |
| give `N`, open `∀ n ≥ N` | `refine ⟨N, fun n hn => ?_⟩` | R2 |
| `\|c - c\| < ε` from `hε` | `simpa using hε` | R3, R4 |
| use `∃` | `obtain ⟨x, hx⟩ := e` | R5 |
| `N > x` for real `x` | `obtain ⟨N, hN⟩ := exists_nat_gt x` | R6 |
| `ℕ` inequality → `ℝ` | `have h' : (N : ℝ) ≤ n := by exact_mod_cast h` | R7 |
| `x - 0 → x` | `rw [sub_zero]` | R8 |
| `\|x\| → x` for `x > 0` | `rw [abs_of_pos (by positivity)]` | R9, R10 |
| positivity side goal | `positivity` | R10 |
| `b / c < a → b < a * c` (goal / hypothesis) | `rw [div_lt_iff₀ hc]` / `rw [div_lt_iff₀ hc] at h` | R11, R12 |
| inequality needing a product of hypotheses | `nlinarith` | R13 |
| see the state | infoview | |
