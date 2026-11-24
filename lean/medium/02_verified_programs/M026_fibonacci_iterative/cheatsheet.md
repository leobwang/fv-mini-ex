# M026 · Fibonacci, iterative: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`have`, `exact`, `rw`, `rfl`, `·`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def` by pattern matching, `induction … with`, `rfl`,
`have`, `exact`, `rw`, `simp only`, `omega`. **New here:** core Lean only (no Mathlib): strengthening the
statement so the induction goes through (an accumulator invariant over an arbitrary start index `k`),
`induction … generalizing k`, using the induction hypothesis at `k + 1`, proving an unfolding fact with
`have h : … := rfl`, `congr 1`, and the core lemma `Nat.zero_add`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
  "no goals" means the tactic closed the goal.
- `P` is "the rest of your goal" (`P : Nat → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- `f : Nat → Nat` stands for `fib`/`pell`, and `g : Nat → Nat → Nat → Nat` for `fibAux`/`pellAux`
  (the guide writes it `(g : (n a b : Nat) → Nat)`: the same type with its arguments named).
- The guide teaches on its own objects, **not** the exercise's: the Pell numbers
  `pell (n + 2) = 2 * pell (n + 1) + pell n`, their accumulator `pellAux n a b` (step
  `(a, b) ↦ (b, 2 * b + a)`) and `pellIter n = pellAux n 0 1`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Nat → Nat → Nat → Nat` | the type of `fibAux`: a function of three `Nat`s (curried: `→` groups to the right) |
| `\| n + 1, a, b => …` | a definition matching on all three arguments at once; `_` in a pattern ignores that argument |
| `ih : ∀ (k : Nat), …` | the induction hypothesis after `generalizing k`: usable at any index, e.g. `ih (k + 1)` |
| `k + 1 + n` | `(k + 1) + n`: `+` groups to the left |
| `k + 1 + 1` | `(k + 1) + 1`; it matches a definition's pattern `n + 2` (with `n := k`) by computation |
| `k + 0`, `0 + n` | `k + 0` computes to `k`; `0 + n` does NOT (for a variable `n`) and needs `Nat.zero_add` (R9) |
| `fibAux n b (a + b)` | the accumulator after one more step: the pair is now `(b, a + b)` |
| `case zero`, `case succ` | the two goals after `induction … with` |

---

## Part 1 · `fibIter_eq`

Statement: `fibIter n = fib n` for all `n`: the linear-time version agrees with the recursive one.

- **`fib : Nat → Nat`**: `fib 0 = 0`, `fib 1 = 1`, `fib (n + 2) = fib n + fib (n + 1)`. Exponential time.
- **`fibAux n a b`**: run the step `(a, b) ↦ (b, a + b)` `n` times and return the first component:
  `fibAux 0 a b = a`, `fibAux (n + 1) a b = fibAux n b (a + b)`.
- **`fibIter n = fibAux n 0 1`**: linear time, starting from `(fib 0, fib 1)`.
- **Why the statement is not inductive as it stands:** `fibIter (n + 1) = fibAux n 1 1`, and `(1, 1)` is not
  `(0, 1)`, so an induction hypothesis about `fibAux n 0 1` never applies. Generalise the start: from the
  pair `(fib k, fib (k + 1))`, `n` steps reach `(fib (k + n), fib (k + n + 1))`. That MILESTONE, a lemma of
  your own above the theorem, proved for every `k` by induction on `n`, gives the theorem at `k = 0`.

### The milestone: induction on `n`, generalising `k`

**R1 · `induction n generalizing k with | zero => ?_ | succ n ih => ?_`** changes the **goal list and the
context**. `generalizing k` takes `k` out of the context first, so what is proved by induction is
`∀ k, P n k`, and `ih` holds for every `k`. Without it, `ih` would only speak about the fixed `k`, and the
succ case needs it at `k + 1`. Placeholders: `(P : Nat → Nat → Prop) (n k : Nat)`.

| Before | After |
|---|---|
| `n k : Nat ⊢ P n k` | `k : Nat ⊢ P 0 k`, `n : Nat ⊢ P (n + 1) k` |

In the second goal the context also holds `ih : ∀ (k : Nat), P n k` (between `n` and `k`).

**R2 · `rfl`** **closes** the zero case. `pellAux 0 a b` computes to `a`, and `k + 0` computes to `k`
(`Nat.add` recurses on its second argument), so both sides become the same term. Placeholders:
`(f : Nat → Nat) (k : Nat)`.

| Before | After |
|---|---|
| `⊢ pellAux 0 (f k) (f (k + 1)) = f (k + 0)` | no goals |

**R3 · `have h : e₁ = e₂ := rfl`** changes the **context**: it adds an equation that holds by computation.
`pell (k + 1 + 1)` matches the third pattern `n + 2`, so `rfl` proves
`2 * pell (k + 1) + pell k = pell (k + 1 + 1)`. State it in this direction (sum on the left): `rw [h]` then
folds the sum that the accumulator step produced back into one `pell` application. For `fib` the fact is
`fib k + fib (k + 1) = fib (k + 1 + 1)`. Placeholders: `(k : Nat) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h : 2 * pell (k + 1) + pell k = pell (k + 1 + 1) ⊢ G` |

**R4 · `simp only [pellAux]`** changes the **goal**: it performs one accumulator step, using the equation
`pellAux (n + 1) a b = pellAux n b (2 * b + a)`. It fires only where the first argument is literally `0` or
`_ + 1`, so `pellAux n …` with a variable `n` is left alone. Placeholders: `(n a b : Nat)`.

| Before | After |
|---|---|
| `⊢ P (pellAux (n + 1) a b)` | `⊢ P (pellAux n b (2 * b + a))` |

Then `rw [h]` with the fact from R3 (TACTIC_STATES, "Rewriting").

**R5 · `rw [ih (k + 1)]`** changes the **goal**: the generalised hypothesis, used at the index `k + 1`.
`ih (k + 1) : g n (f (k + 1)) (f (k + 1 + 1)) = f (k + 1 + n)`; its left side must appear literally, which
is why R3 and `rw [h]` come first. Placeholders: `(g : Nat → Nat → Nat → Nat) (f : Nat → Nat) (n k : Nat)`,
`ih : ∀ (k : Nat), g n (f k) (f (k + 1)) = f (k + n)`.

| Before | After |
|---|---|
| `⊢ P (g n (f (k + 1)) (f (k + 1 + 1)))` | `⊢ P (f (k + 1 + n))` |

**R6 · `congr 1`** changes the **goal**: `f a = f b` becomes `a = b` (one application stripped from both
sides). It closes the new goal itself if it is `rfl` or a hypothesis. Use it when the two sides differ only
inside the argument. Placeholders: `(f : Nat → Nat) (k n : Nat)`.

| Before | After |
|---|---|
| `⊢ f (k + 1 + n) = f (k + (n + 1))` | `⊢ k + 1 + n = k + (n + 1)` |

**R7 · `omega`** **closes** a goal of linear arithmetic over `Nat`/`Int` (`+`, `*` by a literal, `=`, `<`,
`≤`). Placeholders: `(k n : Nat)`.

| Before | After |
|---|---|
| `⊢ k + 1 + n = k + (n + 1)` | no goals |

**W1 / W2 (on `pell`):** the succ case of the Pell milestone, one step per line (R3, R4, `rw [h]`, R5, R6;
R7 closes the last line):

```lean-goal
⊢ pellAux (n + 1) (pell k) (pell (k + 1)) = pell (k + (n + 1))
⊢ pellAux n (pell (k + 1)) (2 * pell (k + 1) + pell k) = pell (k + (n + 1))
⊢ pellAux n (pell (k + 1)) (pell (k + 1 + 1)) = pell (k + (n + 1))
⊢ pell (k + 1 + n) = pell (k + (n + 1))
⊢ k + 1 + n = k + (n + 1)
```

### From the milestone to the theorem

**R8 · `have h := thm n 0`** changes the **context**: a theorem with explicit arguments is a function, and
`thm n 0` is its statement at `k := 0`. Lean writes the instance as is: `0 + 1` and `0 + n` are not
simplified. Placeholders: theorem `shift … (n k : Nat) : g n (f k) (f (k + 1)) = f (k + n)`, `(n : Nat)`.

| Before | After |
|---|---|
| `⊢ G` | `h : g n (f 0) (f (0 + 1)) = f (0 + n) ⊢ G` |

**R9 · `simp only [Nat.zero_add] at h`** changes the **context**: `0 + x` becomes `x` inside `h`. The lemma
is `Nat.zero_add (n : Nat) : 0 + n = n`; it is not `rfl` for a variable, since `Nat.add` recurses on its
second argument. Placeholders: `(g : Nat → Nat → Nat → Nat) (f : Nat → Nat) (n : Nat)`.

| Before | After |
|---|---|
| `h : g n (f 0) (f (0 + 1)) = f n ⊢ G` | `h : g n (f 0) (f 1) = f n ⊢ G` |

**R10 · `exact h`** **closes** a goal that equals `h`'s type up to unfolding definitions (definitional
equality). `pellIter n` unfolds to `pellAux n 0 1`, and `pell 0`, `pell 1` compute to `0`, `1`, so no rewrite
is needed. The same holds for `fibIter`, `fib 0`, `fib 1`. Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `h : pellAux n (pell 0) (pell 1) = pell n ⊢ pellIter n = pell n` | no goals |

---

## Traps

- Inducting on `fibIter_eq` directly fails: `fibIter (n + 1)` starts from `(1, 1)`, not `(0, 1)`. Prove the
  milestone for an arbitrary start `k` first.
- Without `generalizing k`, `ih` is about the fixed `k` only and `ih (k + 1)` is a type error. Do not
  `intro k` before `induction` either: `generalizing` is exactly what undoes that.
- `rw [ih (k + 1)]` fails right after unfolding: the goal has `fib k + fib (k + 1)` where `ih (k + 1)` expects
  `fib (k + 1 + 1)`. Fold it with the `rfl` fact first (R3, `rw [h]`).
- The `rfl` fact must be stated as `… = fib (k + 1 + 1)`, not `fib (k + 2)`: `ih (k + 1)` produces
  `k + 1 + 1`, and `rw` matches text, not computation.
- After R5 the two sides are `fib (k + 1 + n)` and `fib (k + (n + 1))`: equal numbers, different terms.
  `rfl` and `omega` fail on the `fib` equation itself; strip `fib` with `congr 1` (R6), then `omega`.
- `0 + n` does not compute to `n` (R9); `k + 0` does (R2).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction with a re-quantified index | `induction n generalizing k with \| zero => … \| succ n ih => …` | R1 |
| zero case, both sides compute | `rfl` | R2 |
| an unfolding fact | `have h : fib k + fib (k + 1) = fib (k + 1 + 1) := rfl` | R3 |
| one accumulator step | `simp only [fibAux]` | R4 |
| fold the sum | `rw [h]` | R3 |
| IH at the next index | `rw [ih (k + 1)]` | R5 |
| `f a = f b` → `a = b` | `congr 1` | R6 |
| linear arithmetic | `omega` | R7 |
| milestone at `k = 0` | `have h := milestone n 0` | R8 |
| `0 + x → x` in `h` | `simp only [Nat.zero_add] at h` | R9 |
| goal equals `h` after unfolding | `exact h` | R10 |
| see the state | infoview | |
