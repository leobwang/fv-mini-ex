# M015 · Sum by accumulator: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular E014: `induction n with | zero => … | succ k ih => …`,
`simp only [f]`, `simp [f]`, the distributive laws `Nat.mul_add` / `Nat.add_mul`, and `omega` with `k * k` as an
atom. **New here:** core Lean only (no Mathlib): `induction … generalizing acc` for an argument that changes in
the recursive call (the *loop invariant* pattern), rewriting with a `∀`-hypothesis, and specialising your own
general lemma at `acc = 0`.

The problem in one paragraph. `sumAcc n acc` is a loop: while `n > 0`, add `n` to the accumulator `acc` and
decrement `n`; at `n = 0` return `acc`. So `sumAcc n acc = acc + n + (n-1) + … + 1`, and
`sumLoop n = sumAcc n 0 = 1 + 2 + … + n`. The goal is Gauss's formula `2 * sumLoop n = n * (n + 1)`.
Induction directly on `2 * sumAcc n 0 = n * (n + 1)` fails: the recursive call is `sumAcc n (0 + (n + 1))`,
whose accumulator is not `0`, so an IH about accumulator `0` says nothing about it. First state and prove a
MILESTONE for every accumulator (the loop invariant): `2 * sumAcc n acc = 2 * acc + n * (n + 1)`, by induction
generalizing `acc`. Then `sumLoop_spec` is its case `acc = 0`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`, or `P : Nat → Nat → Prop` in R1). The step changes only
  the part inside `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders: `(f : Nat → Nat → Nat)` is any two-argument function (it plays
  `sumAcc`), `(g : Nat → Nat)` any function, `(a b c k t n acc x : Nat)` numbers.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `def sumAcc : Nat → Nat → Nat` with `\| 0, acc => acc` and `\| n + 1, acc => sumAcc n (acc + (n + 1))` | a function of two `Nat`s defined by matching on the first: its first clause (`n = 0`, return `acc`) and second clause (one loop step) are what `simp [sumAcc]` / `simp only [sumAcc]` rewrite with (R2, R3) |
| `sumAcc n acc` | the loop run from counter `n` with accumulator `acc` |
| `sumLoop n` | the wrapper `sumAcc n 0`; it is not recursive, `simp only [sumLoop]` unfolds it (R8) |
| `case zero`, `case succ` | the goals for `0` and `k + 1` after `induction` |
| `ih : ∀ (acc : Nat), …` | the IH holds for every accumulator (after `generalizing acc`) |
| `acc + (n + 1)` | the new accumulator in the recursive call of `sumAcc (n + 1) acc` |
| `n + 1 + 1` | `(n + 1) + 1`: `+` groups to the left |
| `n * n`, `n * 1`, `1 * n`, `2 * 1`, `1 * 1` | left as they are by `simp only [Nat.mul_add, Nat.add_mul]`; `omega` reads `n * n` as one unknown, `n * 1` and `1 * n` as `n`, `2 * 1` as `2` |
| `2 * 0 + x` | the milestone at `acc = 0` before cleanup (R10) |

---

## Part 0 · MILESTONE `sumAcc_eq` (your own theorem, above `sumLoop_spec`)

Statement to write yourself, outside any spec region:
`theorem sumAcc_eq (n acc : Nat) : 2 * sumAcc n acc = 2 * acc + n * (n + 1)`.
In words: running the loop from counter `n` adds `1 + … + n = n(n+1)/2` to the accumulator. It is stated with
`2 *` on both sides so that no division appears.

**R1 · `induction n generalizing acc with | zero => … | succ k ih => …`** changes the **goal list and the
context**: one goal per constructor of `Nat`. Without `generalizing`, `acc` stays fixed and the IH is `P k acc`
for that one `acc`. With it, the `succ` goal gets `ih : ∀ (acc : Nat), P k acc`, usable at the new accumulator.
You may reuse the name `n` instead of `k`. Placeholders: `(P : Nat → Nat → Prop) (n acc : Nat)`.

| Before | After |
|---|---|
| `n acc : Nat ⊢ P n acc` | `acc : Nat ⊢ P 0 acc`, `k : Nat, acc : Nat ⊢ P (k + 1) acc` |

In the second goal the context also has `ih : ∀ (acc : Nat), P k acc`.

**R2 · `simp [f]`** **closes** the `zero` case. It unfolds `f 0 acc` to `acc` with `f`'s first clause, and its
default lemmas `Nat.zero_mul : 0 * n = 0`, `Nat.mul_zero : n * 0 = 0`, `Nat.add_zero : n + 0 = n` clean up
the right side; then both sides are equal. Placeholders: `(acc : Nat)`, the guide's `oddAcc`.

| Before | After |
|---|---|
| `acc : Nat ⊢ oddAcc 0 acc = acc + 0 * 0` | no goals |

**R3 · `simp only [f]`** changes the **goal**: `f (k + 1) acc` becomes the right side of `f`'s second clause,
a call `f k (new accumulator)`. For `sumAcc`, the new accumulator is `acc + (k + 1)`. A call `f k t` with an
unknown `k` is not unfolded. Placeholders: `(k acc : Nat)`, the guide's `oddAcc`.

| Before | After |
|---|---|
| `⊢ P (oddAcc (k + 1) acc)` | `⊢ P (oddAcc k (acc + (2 * k + 1)))` |

**R4 · `simp only [ih]`** with `ih : ∀ acc, c * f k acc = g acc` changes the **goal**: `simp` chooses the
instance of `∀ acc` itself (`acc := t`). The left side of `ih` must occur literally. In the milestone it does:
the goal starts with `2 * sumAcc k (acc + (k + 1))`, and `ih`'s left side is `2 * sumAcc k _`. This is why
R1 needs `generalizing`: an `ih` about the original `acc` only would not match `acc + (k + 1)`.
`rw [ih]` works the same way. Placeholders: `(f : Nat → Nat → Nat) (g : Nat → Nat) (c k t : Nat)`.

| Before | After |
|---|---|
| `⊢ P (c * f k t)` | `⊢ P (g t)` |

The context holds `ih : ∀ (acc : Nat), c * f k acc = g acc` throughout.

**R5 · `Nat.mul_add`** changes the **goal**. Statement: `Nat.mul_add (a b c : Nat) : a * (b + c) = a * b + a * c`.
Placeholders: `(a b c : Nat)`.

| Before | After |
|---|---|
| `⊢ P (a * (b + c))` | `⊢ P (a * b + a * c)` |

**R6 · `Nat.add_mul`** changes the **goal**. Statement: `Nat.add_mul (a b c : Nat) : (a + b) * c = a * c + b * c`.
Placeholders: `(a b c : Nat)`.

| Before | After |
|---|---|
| `⊢ P ((a + b) * c)` | `⊢ P (a * c + b * c)` |

Inside one `simp only [f, ih, Nat.mul_add, Nat.add_mul]`, R3, R4, R5, R6 fire repeatedly until no product has
a sum as a factor. In the milestone that expands `2 * (acc + (k + 1))`, `k * (k + 1)` (from `ih`) and
`(k + 1) * (k + 1 + 1)`.

**R7 · `omega`** **closes** a goal of linear arithmetic over `Nat` (`+`, `*` by a literal, `=`, `<`, `≤`). Any
other term counts as one unknown number: `k * k` is one atom, the same on both sides. It fails if a product
of two non-literals with a sum inside, such as `(k + 1) * (k + 1)`, is left unexpanded. Placeholders: `(a k : Nat)`.

| Before | After |
|---|---|
| `⊢ a + (2 * k + 1) + k * k = a + (k * k + 1 * k + (k * 1 + 1 * 1))` | no goals |

**W1 (on `oddAcc`, `oddAcc (n + 1) acc = oddAcc n (acc + (2 * n + 1))`):** the invariant
`oddAcc n acc = acc + n * n` by R1; R2 for `zero`; for `succ` one `simp only [oddAcc, ih, Nat.mul_add, Nat.add_mul]`
(R3, R4, R5, R6) and R7. Here `ih` has no factor in front (`c` is absent in R4's pattern).

| Before `simp only` | After `simp only` |
|---|---|
| `⊢ oddAcc (k + 1) acc = acc + (k + 1) * (k + 1)` | `⊢ acc + (2 * k + 1) + k * k = acc + (k * k + 1 * k + (k * 1 + 1 * 1))` |

The context holds `ih : ∀ (acc : Nat), oddAcc k acc = acc + k * k`.

---

## Part 1 · `sumLoop_spec`

Statement: `2 * sumLoop n = n * (n + 1)`. Unfold the wrapper `sumLoop` (R8), rewrite with your milestone at
`acc = 0` (R9), and clean up `2 * 0 + …` (R10). `simp` with the names `sumLoop` and `sumAcc_eq` does all three.

**R8 · `simp only [g]`** changes the **goal**: a non-recursive wrapper `def g n := f n 0` is replaced by its body.
Placeholders: `(n : Nat)`, the guide's `oddLoop n := oddAcc n 0`.

| Before | After |
|---|---|
| `⊢ P (oddLoop n)` | `⊢ P (oddAcc n 0)` |

**R9 · `rw [L]`** with `L : ∀ n acc, c * f n acc = c * acc + g n` changes the **goal**: `rw` instantiates both
`∀`s from the goal (`acc := 0`). Your milestone `sumAcc_eq` has exactly this shape with `c = 2`; a theorem
declared above is used like a hypothesis. Placeholders: `(f : Nat → Nat → Nat) (g : Nat → Nat) (c n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (c * f n 0)` | `⊢ P (c * 0 + g n)` |

**R10 · `Nat.mul_zero`, then `Nat.zero_add`** change the **goal**. Statements: `Nat.mul_zero (n : Nat) : n * 0 = 0`
and `Nat.zero_add (n : Nat) : 0 + n = n`. `simp` applies both by itself and then closes `x = x`.
Placeholders: `(c x : Nat)`.

| Before | After `rw [Nat.mul_zero]` | After `rw [Nat.zero_add]` |
|---|---|---|
| `⊢ P (c * 0 + x)` | `⊢ P (0 + x)` | `⊢ P x` |

**W2: the invariant at `acc = 0`.** With `L : ∀ n acc, 3 * oddAcc n acc = 3 * acc + 3 * (n * n)`, prove
`3 * oddLoop n = 3 * (n * n)` by `simp only [oddLoop]` (R8), `rw [L]` (R9), `simp` (R10):

```lean-goal
⊢ 3 * oddLoop n = 3 * (n * n)
⊢ 3 * oddAcc n 0 = 3 * (n * n)
⊢ 3 * 0 + 3 * (n * n) = 3 * (n * n)
```

---

## Traps

- `induction n` without `generalizing acc`: the `succ` goal is about `sumAcc n (acc + (n + 1))`, but the IH is
  about `sumAcc n acc` for the fixed `acc`, so `simp only [ih]` / `rw [ih]` finds nothing to rewrite.
- Do not induct on `2 * sumLoop n = n * (n + 1)` or on the `acc = 0` instance: it is not the statement the
  recursion preserves. State the milestone for every `acc` (Part 0).
- `omega` cannot multiply two unknowns: `(n + 1) * (n + 1 + 1)` and `n * n` are unrelated atoms to it. Expand
  every product with R5, R6 first (put them in the same `simp only` as `ih`, since `ih` itself brings in
  `n * (n + 1)`).
- If `simp only` already closes the goal, a following `omega` fails with "no goals".
- The milestone must be declared above `sumLoop_spec` in the file: Lean only sees theorems declared above.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction with a changing accumulator | `induction n generalizing acc with \| zero => … \| succ n ih => …` | R1 |
| `zero` case | `simp [sumAcc]` | R2 |
| unfold one loop step | `simp only [sumAcc]` | R3 |
| use the `∀`-IH at the new accumulator | `simp only [ih]` / `rw [ih]` | R4 |
| `a * (b + c) → a * b + a * c` | `Nat.mul_add` | R5 |
| `(a + b) * c → a * c + b * c` | `Nat.add_mul` | R6 |
| whole `succ` case | `simp only [sumAcc, ih, Nat.mul_add, Nat.add_mul]`, then `omega` | R3–R7 |
| linear arithmetic, `n * n` as an atom | `omega` | R7 |
| unfold the wrapper | `simp only [sumLoop]` | R8 |
| use the milestone at `acc = 0` | `rw [sumAcc_eq]` | R9 |
| `c * 0 + x → x` | `simp` (`Nat.mul_zero`, `Nat.zero_add`) | R10 |
| see the state | infoview | |
