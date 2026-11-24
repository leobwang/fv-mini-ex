# E079 · Recursion on two arguments: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `rfl`, `exact`, `rw`, `simp` (E010), `omega`
(E011) and `induction` on `Nat` (E014). **New here:** a function defined by pattern matching on two arguments at once, its
lexicographic termination measure, its equation lemmas `f.eq_1`, `f.eq_2`, `f.eq_3`, evaluating it with
`simp [f]` (not `rfl`), and `omega` for the linear arithmetic left at the end. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Two-argument recursion in one paragraph

`def ack : Nat → Nat → Nat | 0, n => … | m + 1, 0 => … | m + 1, n + 1 => …` matches both arguments at once;
each line is one case of the pair `(m, n)`. No single argument shrinks in every call: `ack (m + 1) n` keeps the
first argument, and `ack m (ack (m + 1) n)` may make the second one huge. Lean therefore cannot use structural
recursion. It proves termination by **well-founded recursion** on the pair `(m, n)` ordered
**lexicographically**: `(m', n') < (m, n)` when `m' < m`, or `m' = m` and `n' < n`. Every call lowers `m`, or
keeps `m` and lowers `n`. You may state this measure with `termination_by m n => (m, n)` (the guide's `g` does);
for `ack` Lean guessed it. Two consequences:

- Lean generates one **equation lemma** per pattern, `ack.eq_1 : ack 0 x = x + 1`,
  `ack.eq_2 : ack m.succ 0 = ack m 1`, `ack.eq_3 : ack m.succ n.succ = ack m (ack (m + 1) n)`. `rw [ack]` and
  `simp [ack]` use them; an equation applies only where the arguments literally have its pattern's shape.
- A function defined by well-founded recursion does not compute inside the kernel's definitional unfolding, so
  `rfl` and `decide` cannot evaluate `ack 2 3`. `simp [ack]` can: it rewrites with the equations.

## Reading the goals

| You see | It means |
|---|---|
| `ack m n`, `g m n` | the function applied to two `Nat`s; `ack 1 (k + 1)` is `ack` at `m = 1`, `n = k + 1` |
| `m.succ` | `Nat.succ m`, that is `m + 1` (equation lemmas print their patterns this way) |
| `g (0 + 1) k`, `ack (0 + 1) k`, `ack (1 + 1) k` | `g 1 k`, `ack 1 k`, `ack 2 k`: after `rw [f]` matched the literal against `m + 1`, Lean prints `1` as `0 + 1` and `2` as `1 + 1`. `rw [ih]` with `ih : ack 1 k = …` still finds it |
| `case zero`, `case succ` | the two goals after `induction n with` (R3) |
| `ih : ack 1 k = k + 2` | the induction hypothesis: the statement at the predecessor `k` |
| `2 * (k + 1) + 3` | the right side of the statement with `n` replaced by `k + 1`; `simp` and `omega` handle it |

---

## Part 1 · `ack_small`

Statement: `ack 2 3 = 9`. A closed computation: no variables, so the equations can be applied until only
numerals remain.

**R1 · `simp [f]`** **closes** an equation `f a b = v` between numerals. `simp` rewrites with every equation
lemma of `f`, repeatedly; a literal such as `2` matches the pattern `m + 1` with `m := 1`, and `0` matches the
pattern `0`. Placeholders: the guide's `g : Nat → Nat → Nat`.

| Before | After |
|---|---|
| `⊢ g 1 2 = 11` | no goals |

---

## Part 2 · `ack_one`

Statement: `ack 1 n = n + 2` for every `n`. A statement about every `n` needs induction on `n`. In the step,
`ack 1 (k + 1)` unfolds (equation 3) to `ack 0 (ack 1 k)`; the induction hypothesis turns `ack 1 k` into
`k + 2`; equation 1 turns `ack 0 (k + 2)` into `k + 2 + 1`, which `simp` identifies with `k + 1 + 2`.

**R2 · `rw [f]`** changes the **goal**: it uses one equation of `f`, once, at the first `f …` whose arguments
fit a pattern. Use it to see each unfolding step; `simp` (R4) does them all at once. Placeholders:
`(m n : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (g (m + 1) (n + 1))` | `⊢ P (g m (g (m + 1) n))` |

**R3 · `induction n with | zero => … | succ k ih => …`** changes the **goal list and the context**: two goals,
`n` replaced by `0` and by `k + 1`, with `ih : P k` in the second. In the exercise each arm holds its proof
(`| zero => …`). Placeholders: `(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ P n` | `⊢ P 0`, `k : Nat, ih : P k ⊢ P (k + 1)` |

**R4 · `simp only [f, ih]`** changes the **goal**: it unfolds `f`, rewrites with `ih`, and unfolds again, as
long as anything applies. `simp [f, ih]` (without `only`) also does the arithmetic clean-up and often closes the
goal. Placeholders: `(k c : Nat) (ih : g 1 k = c) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (g 1 (k + 1))` | `⊢ P (c + 3)` |

**W1 (on `g`, `g 1 n = 3 * n + 5`):** R3; the `zero` case is R1; the `succ` case by `rw [g]` (R2),
`rw [ih]`, `rw [g]` (R2), `omega` (R6) passes through

```lean-goal
⊢ g 1 (k + 1) = 3 * (k + 1) + 5
⊢ g 0 (g (0 + 1) k) = 3 * (k + 1) + 5
⊢ g 0 (3 * k + 5) = 3 * (k + 1) + 5
⊢ 3 * k + 5 + 3 = 3 * (k + 1) + 5
```

W2 does the step as `simp [g, ih]` (R4), which here stops at `3 * k + 3 = 3 * (k + 1)`, and `omega` ends it.

---

## Part 3 · `ack_two`

Statement: `ack 2 n = 2 * n + 3`. Induction again. In the step `ack 2 (k + 1)` unfolds to `ack 1 (ack 2 k)`;
`ih` gives `ack 1 (2 * k + 3)`. Unfolding cannot finish this: it needs the value of `ack 1` at an expression
containing the variable `k`, which is exactly what Part 2 proves. So use the theorem `ack_one` at `2 * k + 3`.
What is left is linear arithmetic.

**R5 · `simp only [thm]`**, with `thm : ∀ x, f x = e x`, changes the **goal**: every `f y` becomes `e y`; `simp`
chooses `x := y` itself. A theorem proved earlier in the file (here `ack_one`) is used by its name, exactly like
the hypothesis `hf` in the guide. Placeholders: `(hf : ∀ x, g 1 x = 3 * x + 5) (y : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (g 1 y)` | `⊢ P (3 * y + 5)` |

**R6 · `omega`** **closes** a linear equation or inequality over `Nat` or `Int`: built from variables,
numerals, `+`, `-`, and multiplication by a numeral. It does not unfold definitions, so a leftover `ack …` or
`g …` term is treated as an unknown number.

| Before | After |
|---|---|
| `⊢ 3 * k + 5 + 3 = 3 * (k + 1) + 5` | no goals |

**W3 (on `g 2 (n + 1) = 3 * (g 2 n + 1) + 2`):** `simp [g, g_one]` unfolds `g 2 (n + 1)` to `g 1 (g 2 n)`,
applies `g_one` at `x := g 2 n` (R5), and stops at

```lean-goal
⊢ 3 * g 2 n + 3 = 3 * (g 2 n + 1)
```

which `omega` closes, treating `g 2 n` as one unknown (R6).

---

## Traps

- `rfl` and `decide` fail on `ack 2 3 = 9`: well-founded definitions are not unfolded by definitional
  computation ("The left-hand side `ack 2 3` is not definitionally equal to the right-hand side `9`"). Use
  `simp [ack]`.
- `rw [ack]` or `simp only [ack]` on `ack 1 k` with a bare variable `k` makes no progress: no equation matches
  until `k` is `0` or `_ + 1`. Induct first.
- `ack_two` needs `ack_one` in the `simp` set: after `ih`, the goal contains `ack 1 (2 * k + 3)`, and only the
  closed form of `ack 1` removes it.
- `ack_one` must come before `ack_two` in the file to be usable there; it already does.
- After unfolding, a literal may print as `0 + 1` or `1 + 1` (it was matched against `m + 1`). It is the same
  number; `rw [ih]` and `simp` still see it.
- `simp [f, ih]` may stop at arithmetic such as `2 * k + 2 = 2 * (k + 1)`; finish with `omega`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| evaluate a closed `f a b = v` | `simp [f]` | R1 |
| unfold exactly one step | `rw [f]` | R2 |
| statement for every `n` | `induction n with \| zero => … \| succ k ih => …` | R3 |
| base case `f a 0 = …` | `simp [f]` | R1 |
| step case: unfold, use `ih` | `simp [f, ih]` | R4 |
| use a theorem proved earlier | `simp [f, ih, thm]` | R5 |
| linear arithmetic left over | `omega` | R6 |
| one equation by name | `rw [f.eq_3]` (`f.eq_1` … one per pattern) | R2 |
| see the state | infoview | |
