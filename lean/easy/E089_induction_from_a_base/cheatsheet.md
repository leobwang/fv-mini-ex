# E089 · Induction from a base: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `induction` on `Nat` (E014), `omega` (E011)
and `calc` (E020). **New here:** Mathlib's induction principle `Nat.le_induction` (induction that starts at
`n₀` instead of `0`) used through `induction … using`, the power lemma `pow_succ`, and the Mathlib closers
`norm_num`, `nlinarith`, `ring`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{M : Type}` is any type. A bracket such as `[Monoid M]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ` | `Nat`, the natural numbers `0, 1, 2, …` (Mathlib's notation, typed `\N`) |
| `2 ^ n` | `2` to the power `n`; in `ℕ`, `n : ℕ` is the exponent (`HPow ℕ ℕ ℕ`) |
| `n₀ ≤ n`, `hn : 3 ≤ n` | the hypothesis that induction from a base consumes; `n ≥ 3` is the same proposition written the other way |
| `case base` | the goal for the starting value `n₀` (here `3` or `4`) |
| `case succ` | the step goal: from the claim for `k` (and `n₀ ≤ k`) to the claim for `k + 1` |
| `hk : n₀ ≤ k` | in the `succ` case: `k` is at least the base (the only place `k ≥ 3` / `k ≥ 4` comes from) |
| `ih : P k` | the induction hypothesis: the claim for `k` |
| `n k : ℕ` | the original `n` stays in the context after `induction … using Nat.le_induction`; it is unused, ignore it |
| `case calc_1`, `calc_2`, … | the goals for the links of a `calc` chain whose proofs are `?_` (R6) |
| `inst✝ : Monoid M` | an anonymous type-class hypothesis from a `[Monoid M]` binder |

---

## Part 1 · `lin_ge`

Statement: for every `n : ℕ` with `3 ≤ n`, `2 * n + 1 ≤ 2 ^ n`. Without `3 ≤ n` it is false at `n = 1`
(`3 ≤ 2`) and `n = 2` (`5 ≤ 4`), so an induction from `0` on the bare claim has a false step: `0 → 1` goes
from the true `1 ≤ 1` to the false `3 ≤ 2`. Inducting from the base `3` (R1) makes `3` the base case and
gives `hk : 3 ≤ k` in every step.

**R1 · `induction n, hn using Nat.le_induction with | base => ?_ | succ k hk ih => ?_`** changes the **goal
list and the context**. The principle is `Nat.le_induction`: to prove `P n` for every `n` with `n₀ ≤ n`, prove
`P n₀` (case `base`) and, for every `k` with `n₀ ≤ k`, `P k → P (k + 1)` (case `succ`). Name both the variable
and the hypothesis after `induction` (`n, hn`); `hn` leaves the context. With `with` you name the step's new
hypotheses `k hk ih`; you may write tactics after each `=>` instead of `?_`. Placeholders: `(n₀ : ℕ)`,
`(P : ℕ → Prop)`, `(n : ℕ) (hn : n₀ ≤ n)`.

| Before | After |
|---|---|
| `hn : n₀ ≤ n ⊢ P n` | `⊢ P n₀` (case `base`), `hk : n₀ ≤ k, ih : P k ⊢ P (k + 1)` (case `succ`) |

**R2 · `norm_num`** **closes** a goal made only of numerals, such as the base case once `n` is a literal: it
evaluates `+`, `*`, `^` on literals and decides `≤`, `=`, `<`. (`decide` also works on these small `ℕ`
goals.)

| Before | After |
|---|---|
| `⊢ 5 ^ 2 ≤ 3 ^ 3` | no goals |

**R3 · `rw [pow_succ]`** changes the **goal**. The lemma is `pow_succ (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a`:
it peels the last factor off a power, so the `2 ^ k` of `ih` appears in the goal. Placeholders:
`{M : Type} [Monoid M] (a : M) (n : ℕ)`; `Monoid M` means `M` has an associative `*` with a `1`, which `ℕ`,
`ℤ`, `ℝ`, `ℂ` and matrices meet.

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

**R4 · `omega`** **closes** a goal of linear arithmetic over `ℕ` or `ℤ` (`+`, `-`, `*` by a numeral, `≤`, `<`,
`=`), using the hypotheses in the context. A non-linear subterm such as `3 ^ k` or `k ^ 2` is treated as one
unknown number (an *atom*), so `ih : 3 * k ≤ 3 ^ k` and the goal `… ≤ 3 ^ k * 3` speak about the same unknown.
After R3, the step of `lin_ge` is linear in the atoms `k` and `2 ^ k`.

| Before | After |
|---|---|
| `hk : 1 ≤ k, ih : 3 * k ≤ 3 ^ k ⊢ 3 * k + 3 ≤ 3 ^ k * 3` | no goals |

### Worked combination W1 (on `n + 2 ≤ 2 ^ n` from `n₀ = 2`, not the exercise's inequality)

R1 splits the goal; the `base` goal is numerals only:

```lean-goal
⊢ 2 + 2 ≤ 2 ^ 2
⊢ k + 1 + 2 ≤ 2 ^ (k + 1)
```

R2 closes the first. In the `succ` goal, R3 exposes `2 ^ k` (the atom of `ih : k + 2 ≤ 2 ^ k`), then R4 closes:

```lean-goal
⊢ k + 1 + 2 ≤ 2 ^ k * 2
```

---

## Part 2 · `pow_ge_sq`

Statement: for every `n : ℕ` with `4 ≤ n`, `n ^ 2 ≤ 2 ^ n`. It is false at `n = 3` (`9 ≤ 8`), so the
induction starts at `4`. In the step, `(k + 1) ^ 2 = k ^ 2 + (2 * k + 1)`; `ih` bounds `k ^ 2 ≤ 2 ^ k`, and a
helper fact must bound the rest `2 * k + 1` by `2 ^ k` too. That helper is non-linear in `k`, so `omega`
cannot prove it: `nlinarith` can (it holds because `k ≥ 4`). R1 and R2 are used as in Part 1.

**R5 · `nlinarith`** **closes** a polynomial inequality over an ordered field or `ℕ`/`ℤ`. It first multiplies
pairs of hypotheses (and the negated goal) together, then does linear arithmetic over the products, so a
hypothesis like `hx : 3 ≤ x` yields `9 ≤ x * x`-type facts. Use it inside `have h : … := by nlinarith` to get
the helper. Placeholders: `(x : ℕ) (hx : 3 ≤ x)`.

| Before | After |
|---|---|
| `hx : 3 ≤ x ⊢ 3 * x ≤ x ^ 2` | no goals |

**R6 · `calc`** changes the **goal list**: a goal `a ≤ d` is proved by a chain `a = b`, `_ ≤ c`, `_ = d`; each
link is its own goal (proved after its `:=`, here left as `?_`). A chain of `=` and `≤` links proves `≤`. The
first term must be the goal's left side and the last term its right side (up to unfolding). `_` stands for
the previous right side. Placeholders: `{α : Type} [Preorder α] (a b c d : α)` (`Preorder α`: `α` has a
reflexive, transitive `≤`, as `ℕ`, `ℤ`, `ℝ` do).

| Before | After |
|---|---|
| `⊢ a ≤ d` | `⊢ a = b` (case `calc_1`), `⊢ b ≤ c` (case `calc_2`), `⊢ c = d` (case `calc_3`) |

**R7 · `ring`** **closes** an equation that holds in every commutative semiring (`ℕ` included: no
subtraction needed). It expands and normalises both sides; exponents `n + 1` with a variable `n` are
split as `a ^ n * a`. It does not use hypotheses and does not prove `≤`. Placeholders:
`{R : Type} [CommSemiring R] (a : R) (n : ℕ)` (`ℕ`, `ℤ`, `ℝ`, `ℂ` qualify).

| Before | After |
|---|---|
| `⊢ a ^ (n + 1) + a ^ n = a ^ n * (a + 1)` | no goals |

### Worked combination W2 (on `n ^ 2 ≤ 3 ^ n` from `n₀ = 2`, not the exercise's inequality)

After R1 and R2, the `succ` goal is:

```lean-goal
⊢ (k + 1) ^ 2 ≤ 3 ^ (k + 1)
```

`have h : 2 * k + 1 ≤ 2 * k ^ 2 := by nlinarith` (R5, using `hk : 2 ≤ k`) adds the helper; the goal is
unchanged. Then a `calc` (R6) with three links: `(k + 1) ^ 2 = k ^ 2 + (2 * k + 1)` by R7,
`_ ≤ 3 ^ k + 2 * 3 ^ k` by R4 (from `ih` and `h`, atoms `k ^ 2`, `3 ^ k`), `_ = 3 ^ (k + 1)` by R7.

---

## Traps

- Plain `induction n` starts at `0`. On the bare claim its step is false somewhere (`0 → 1` for `lin_ge`,
  `2 → 3` for `pow_ge_sq`); keeping `hn` makes the step provable only by a case split that re-proves the
  base. Use R1 and name both `n, hn`. Without `with … succ k hk ih`, the new hypotheses get inaccessible
  names (`k✝`, `a✝`).
- `omega` treats `k * k` and `k ^ 2` as **different** atoms. A helper stated as `2 * k ≤ k * k` does not help
  `omega` with a goal containing `k ^ 2`: write the helper with the same `^ 2` that the goal uses.
- `omega` cannot prove the helper `2 * k + 1 ≤ k ^ 2` itself (it is non-linear in `k`); `nlinarith` can,
  because `hk` is in the context.
- In a `calc`, the first term must match the goal's left side and the last its right side; a chain ending at
  `2 ^ k * 2` does not close a goal `… ≤ 2 ^ (k + 1)` unless that last link is proved (e.g. by `ring`).
- `ring` proves only equations. Use it for the `=` links of a `calc`, and `omega`/`nlinarith` for the `≤` link.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induct from `n₀`, given `hn : n₀ ≤ n` | `induction n, hn using Nat.le_induction with \| base => … \| succ k hk ih => …` | R1 |
| numeral-only goal (the base case) | `norm_num` | R2 |
| `a ^ (k + 1) → a ^ k * a` | `rw [pow_succ]` | R3 |
| linear goal over `ℕ`, powers as atoms | `omega` | R4 |
| polynomial inequality from hypotheses | `nlinarith` | R5 |
| add a helper fact | `have h : T := by nlinarith` | TACTIC_STATES |
| chain `=` / `≤` steps | `calc a = b := by …`, next lines `_ ≤ c := by …`, `_ = d := by …` | R6 |
| polynomial identity (a `calc` `=` link) | `ring` | R7 |
| see the state | infoview | |
