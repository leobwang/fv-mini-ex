# E048 · Recursive theorems: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `decide`, `rfl`, `have`, `exact`, `simp only`,
`omega` and definitions by pattern matching. **New here:** a theorem that calls itself (a proof by induction
written as a recursive function), splitting `n` with `match` into the cases a definition uses (`0 | 1 | n + 2`
or `0 | n + 1`), unfolding one equation of a recursive definition with `simp only [f]`, changing the goal to a
definitionally equal form with `show`, and `Nat.pow_succ`. No Mathlib.

The `induction` tactic and the recursors (`Nat.rec`, …) are banned: the recursion is the proof.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Why a recursive theorem is an induction proof

A theorem `thm (n : Nat) : P n` is a function from `n` to a proof of `P n`. Defining it by cases on `n`, and
calling `thm m` for some `m` structurally smaller than `n` (obtained by peeling `+ 1`s off the pattern), is
exactly induction: `thm m : P m` is the induction hypothesis. Lean checks that every recursive call is on a
smaller argument, so the recursion terminates and the proof is sound.

| Definition has cases | Split the theorem as | Recursive calls allowed in the last case | Proof principle |
|---|---|---|---|
| `0`, `n + 1` | `0`, `m + 1` | `thm m` | ordinary induction |
| `0`, `1`, `n + 2` | `0`, `1`, `m + 2` | `thm m`, `thm (m + 1)` | two-step induction: two IHs |

## Reading the goals

| You see | It means |
|---|---|
| `fib n < 2 ^ n` | `<` on `Nat`; `2 ^ n` is the natural-number power $2^n$ |
| `b ^ n * b * b` | `*` groups to the left: `(b ^ n * b) * b` |
| `evenB (2 * n) = true` | `evenB` returns a `Bool`; `true`/`false` are its two values, and `= true` turns it into a `Prop` |
| `n✝ n : Nat` | after a term-mode `match n with … \| n + 2 => by …`: `n✝` is the original `n` (unusable, the `✝` marks a shadowed name); the goal is about the new pattern variable `n` |
| `n m : Nat` | after `refine match n with … \| m + 2 => ?_`: `n` is still listed, but the goal is about `m` |
| `f (m + 2)` | `f` applied to the third pattern; `simp only [f]` unfolds it (R4) |
| `f (m + 1)` | not of the form `_ + 2`: `simp only [f]` leaves it alone |
| `2 * (m + 1)` | also not `_ + 2` as written, though it computes to `2 * m + 2` (R10) |
| `b ^ n * b` | `b ^ (n + 1)` after `Nat.pow_succ` (R6) |
| `case refine_1` | the label of the first `?_` goal after `refine` |

---

## Part 1 · `fib_lt_two_pow`

Statement: `fib n < 2 ^ n` for all `n`, where `fib 0 = 0`, `fib 1 = 1`, `fib (n + 2) = fib n + fib (n + 1)`.
Mirror `fib`'s three cases. In the case `m + 2` the step is
`fib m + fib (m + 1) < 2 ^ m + 2 ^ (m + 1) ≤ 2 ^ m * 2 * 2`, which needs the IH at both `m` and `m + 1`.

**R1 · `match n with | 0 => … | 1 => … | m + 2 => …`** changes the **goal list**: one goal becomes one goal per
pattern, with `n` replaced by the pattern. In the guide it is written `refine match n with … => ?_` so the
three cases appear as goals; after `:=` you can write the same `match` in term mode, with `by …` in each arm.
Placeholders: `(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ P n` | `⊢ P 0`, `⊢ P 1`, `n m : Nat ⊢ P (m + 2)` |

**R2 · `decide`** **closes** a base case. With a literal argument, `half 1 < 2 ^ 1` (and `fib 0 < 2 ^ 0`) is a
closed computation that `decide` evaluates.

| Before | After |
|---|---|
| `⊢ half 1 < 2 ^ 1` | no goals |

**R3 · `have ih := thm … m`** changes the **context**: the recursive call is a proof of the statement at `m`,
added as a hypothesis. From the case `m + 2` you may call the theorem at `m` and at `m + 1`. Pass every
explicit argument of the theorem (in the exercise that is only `n`). Placeholders:
`(P : Nat → Prop) (step : ∀ m, P m → P (m + 1) → P (m + 2))`, theorem `twoStep … (n : Nat) : P n`.

| Before | After `have ih1 := twoStep P h0 h1 step m` | After `have ih2 := twoStep P h0 h1 step (m + 1)` |
|---|---|---|
| `n m : Nat ⊢ P (m + 2)` | `ih1 : P m ⊢ P (m + 2)` | `ih1 : P m, ih2 : P (m + 1) ⊢ P (m + 2)` |

**R4 · `simp only [f]`** changes the **goal**: it rewrites with the equations of the recursive definition `f`
(here `half 0 = 0`, `half 1 = 0`, `half (n + 2) = half n + 1`), wherever the argument, as written, has the
shape of a pattern (a numeral offset counts: `n + 3` is read as `(n + 1) + 2`; `2 * (m + 1)` does not match).
Placeholders: `(n : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (half (n + 2))` | `⊢ P (half n + 1)` |

**R5 · `simp only [f] at *`** changes the **context and the goal**: the same rewriting in every hypothesis and
in the goal (`at h` for one hypothesis). Use it after R3, so the IHs are unfolded the same way as the goal.
Placeholders: `(n : Nat) (P Q : Nat → Prop) (h : P (half (n + 2)))`.

| Before | After |
|---|---|
| `h : P (half (n + 2)) ⊢ Q (half (n + 2))` | `h : P (half n + 1) ⊢ Q (half n + 1)` |

**R6 · `Nat.pow_succ`** changes the **goal**. The lemma is `Nat.pow_succ (n m : Nat) : n ^ m.succ = n ^ m * n`,
where `m.succ` (`Nat.succ m`) is `m + 1`: so `b ^ (n + 1) = b ^ n * b`.
`rw` uses it once; `simp only [Nat.pow_succ]` repeats it, so `b ^ (n + 2)` becomes `b ^ n * b * b` (W3).
Placeholders: `(b n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (b ^ (n + 1))` | `⊢ P (b ^ n * b)` |

**R7 · `omega`** **closes** a goal of linear arithmetic (`+`, `*` by a literal, `<`, `≤`, `=`) over `Nat` and
`Int`, using the hypotheses in the context. Any other term, such as `3 ^ k` or `fib m`, is one unknown number,
so `3 ^ k * 3` is linear in the unknown `3 ^ k`. Placeholders: `(x y k : Nat)`.

| Before | After |
|---|---|
| `hx : x < 3 ^ k, hy : y ≤ 3 ^ k * 3 ⊢ x + y < 3 ^ k * 4` | no goals |

**W1 (on `half`):** R1, R2, R3, R4, R7 in that order prove `half n ≤ n`. The third case starts at

```lean-goal
⊢ half (m + 2) ≤ m + 2
```

and after `have ih := half_le m` and `simp only [half]`, `omega` closes `half m + 1 ≤ m + 2` from
`ih : half m ≤ m`.

**W3 (powers of 3):** `simp only [Nat.pow_succ] at *` (R5 with R6) turns both `^ (k + 1)` and `^ (k + 2)` into
products of `3 ^ k`, then `omega` (R7) closes:

| Before | After `simp only [Nat.pow_succ] at *` |
|---|---|
| `h : x < 3 ^ (k + 1) ⊢ x + x < 3 ^ (k + 2)` | `h : x < 3 ^ k * 3 ⊢ x + x < 3 ^ k * 3 * 3` |

---

## Part 2 · `evenB_double`

Statement: `evenB (2 * n) = true`, where `evenB 0 = true`, `evenB 1 = false`, `evenB (n + 2) = evenB n`.
Split `n` into `0` and `m + 1`: then `2 * (m + 1)` is two more than `2 * m`, so one `evenB` step leads back to
the statement at `m`.

**R8 · `match n with | 0 => … | m + 1 => …`** changes the **goal list**: two goals. Placeholders:
`(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ P n` | `⊢ P 0`, `n m : Nat ⊢ P (m + 1)` |

**R9 · `rfl`** **closes** an equation whose two sides compute to the same value: `2 * 0` computes to `0`, then
`half 0` to `0` by the first equation. In term mode, `| 0 => rfl` is the whole arm.

| Before | After |
|---|---|
| `⊢ half (2 * 0) = 0` | no goals |

**R10 · `show G'`** changes the **goal** to `G'`, provided `G'` and the goal are equal by computation
(definitionally equal). `Nat.mul` recurses on its second argument, so `2 * (m + 1)` computes to `2 * m + 2`.
`show` is how you make the `_ + 2` pattern visible to `simp only [f]` (R4). For an odd argument, put `+ 2`
outermost: `2 * (m + 1) + 1` becomes `2 * m + 1 + 2`. Placeholders: `(P : Nat → Prop) (m : Nat)`.

| Before | After |
|---|---|
| `⊢ P (2 * (m + 1))` | `⊢ P (2 * m + 2)` |
| `⊢ P (2 * (m + 1) + 1)` | `⊢ P (2 * m + 1 + 2)` |

**R11 · `exact thm … m`** **closes** a goal that is the theorem's own statement at a smaller argument. It is
R3 used to finish instead of to add a hypothesis. Placeholders: `(P : Nat → Prop) (step : ∀ m, P m → P (m + 1))`,
theorem `oneStep … (n : Nat) : P n`.

| Before | After |
|---|---|
| `n m : Nat ⊢ P m` | no goals |

**W2 (on `half`):** `half (2 * n) = n` by R8, R9 for `0`, then R10, R4, and the recursive call:

| After `show half (2 * m + 2) = m + 1` | After `simp only [half]` |
|---|---|
| `⊢ half (2 * m + 2) = m + 1` | `⊢ half (2 * m) + 1 = m + 1` |

`rw [half_double m]` then turns the left side into `m + 1` and closes the goal.

---

## Part 3 · `evenB_double_add_one`

Statement: `evenB (2 * n + 1) = false`. Same structure as Part 2: R8, R9 for `0` (`evenB (2 * 0 + 1)` computes
to `evenB 1 = false`), then R10 with the odd form (second row of the R10 table), R4, R11.

---

## Traps

- `simp only [f]` on `f (2 * (m + 1))` fails with "simp made no progress": `2 * (m + 1)` is not literally
  `_ + 2`. Use `show` first (R10).
- `show G'` only accepts a `G'` that computes to the same thing as the goal; it is not a rewriting tool. If the
  two forms differ by more than computation (say `n * 2` vs `2 * n`), `show` fails.
- `omega` rewrites `b ^ (k + 1)` to `b ^ k * b` by itself, but treats `b ^ (k + 2)` as a new unknown unrelated
  to `b ^ k`. Rewrite with `Nat.pow_succ` (R6) first.
- The rewrite that matters is in the goal: `2 ^ (m + 2)` must become `2 ^ m * 2 * 2`. In `h2`, `omega`
  would handle `2 ^ (m + 1)` by itself; `at *` (R5) rewrites it anyway, so every hypothesis shows the
  same unknown `2 ^ m`, which makes the state easier to read.
- A recursive call on a non-smaller argument (`thm (m + 2)` inside the case `m + 2`) is rejected: Lean cannot
  show termination.
- `induction`, `fun_induction` and the recursors are banned: write the `match` and the recursive calls.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| cases `0`, `1`, `n + 2` | `match n with \| 0 => … \| 1 => … \| n + 2 => …` | R1 |
| base case at a literal | `decide` / `rfl` | R2, R9 |
| induction hypothesis | `have ih := thm m` (also `thm (m + 1)` from `m + 2`) | R3 |
| unfold `f (n + 2)` | `simp only [f]`, in hypotheses too: `at *` | R4, R5 |
| `b ^ (n + 1) → b ^ n * b` | `simp only [Nat.pow_succ]` | R6 |
| linear arithmetic, `2 ^ n` as an unknown | `omega` | R7 |
| cases `0`, `n + 1` | `match n with \| 0 => … \| n + 1 => …` | R8 |
| expose `_ + 2` in `2 * (n + 1)` | `show f (2 * n + 2) = _` | R10 |
| goal is the statement at `m` | `exact thm m` | R11 |
| see the state | infoview | |
