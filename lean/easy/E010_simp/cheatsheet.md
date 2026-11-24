# E010 · simp: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E009: `rfl` (E001), `def` (E002), `exact` (E003), and `rw [l]`,
`rw [l] at h` with the lemmas `Nat.add_zero`, `Nat.add_comm`, `List.length_append` (E009). **New here:**
the simplifier `simp`: its default lemma set, `simp only [...]`, `simp [f]` to unfold your own
definition, `simp [h]` to rewrite with a hypothesis, and `simp at h` to work on a hypothesis. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used by `simp`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop` or `P : List α → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- `{α : Type}` is any type of list elements (`Nat`, `Bool`, …).
- The lemma entries (R2, R3, R5, R7, R10) are shown with `simp only [lemma]`, which uses exactly the listed
  lemmas, so one rewrite happens. Plain `simp` uses all of them, and every other `@[simp]` lemma, at once.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## What `simp` does

`simp` rewrites the goal with a set of equations `l = r` (and iffs `p ↔ q`), always left to right, inside
every subterm, innermost first, and repeats until no equation applies. It then closes the goal if it became
`True` (`eq_self : (a = a) = True` turns `t = t` into `True`). If nothing changed it fails with
`simp made no progress`; if something changed but the goal is not closed, it leaves the simplified goal.

| Form | Equations used | Works on |
|---|---|---|
| `simp` | the default simp set: every lemma tagged `@[simp]` | the goal |
| `simp only [l₁, l₂]` | only `l₁`, `l₂` (plus closing `t = t`) | the goal |
| `simp [f]` | default set + the defining equation of your `def f` | the goal |
| `simp [h]` | default set + hypothesis `h : a = b` or `h : ∀ x, f x = g x` | the goal |
| `simp at h` | default set | hypothesis `h` |
| `simp_all` | default set + every hypothesis | all hypotheses and the goal |
| `simp?` | same as `simp` | also prints the `simp only [...]` call it used |

`simp at h₁ h₂` works on several hypotheses; add the symbol `⊢` to the list (`simp at h ⊢`) to include the goal.

## Reading the goals

| You see | It means |
|---|---|
| `List Nat`, `List α` | finite lists of naturals / of elements of type `α` |
| `[]` | the empty list |
| `xs ++ ys` | `xs` followed by `ys` (append); `xs ++ [] ++ ys` is `(xs ++ []) ++ ys` |
| `xs.length` | the number of elements of `xs` (`List.length xs`) |
| `P (xs ++ ys).length` | `P` applied to `(xs ++ ys).length`: Lean prints no extra parentheses |
| `∀ (x : Nat), f x = x + 1` | how Lean prints `∀ x, f x = x + 1` with the type filled in |
| `n + 3` | a numeral: `simp` can match it as `(n + 2) + 1` (R10) |

---

## Part 1 · `simp_default`

Statement: `(xs ++ [] ++ ys).length = xs.length + ys.length` for lists of naturals. Every lemma needed is in
the default simp set: drop `++ []` (R2), split the length of an append (R3); both sides are then equal (R11).

**R1 · `simp`** **closes** the goal here (or simplifies it). It uses the default simp set: every lemma tagged
`@[simp]`, among them `List.nil_append : [] ++ as = as`, `List.append_nil` (R2), `List.length_append` (R3),
`Nat.add_zero` (R5), `Nat.mul_one` (R7). Placeholders: `{α : Type} (xs : List α)`.

| Before | After |
|---|---|
| `xs : List α ⊢ ([] ++ xs).length = xs.length` | no goals |

**R2 · `List.append_nil`** changes the **goal**. The lemma is `List.append_nil : as ++ [] = as`. Placeholders:
`{α : Type} (xs : List α) (P : List α → Prop)`.

| Before | After |
|---|---|
| `⊢ P (xs ++ [])` | `⊢ P xs` |

**R3 · `List.length_append`** changes the **goal**. The lemma is
`List.length_append : (as ++ bs).length = as.length + bs.length` (as in E009, but `simp` finds it on its own).
Placeholders: `{α : Type} (xs ys : List α) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (xs ++ ys).length` | `⊢ P (xs.length + ys.length)` |

**W1: `simp` leaves what it cannot finish.** `simp` never reorders a sum, so on
`([] ++ xs ++ ys).length = (ys ++ xs).length` it stops at the commuted sum; `rw [Nat.add_comm]` (E009)
finishes.

| Before `simp` | After `simp` |
|---|---|
| `⊢ ([] ++ xs ++ ys).length = (ys ++ xs).length` | `⊢ xs.length + ys.length = ys.length + xs.length` |

---

## Part 2 · `simp_unfold`

Statement: `square (n + 0) = n * n`, where `square n = n * n` is defined in the file. Plain `simp` does not
look inside your own definitions (it only drops the `+ 0` and stops at `square n = n * n`): give it
the name (R4). The same call drops the `+ 0` (R5).

**R4 · `simp [f]`** changes the **goal**: every `f t` is replaced by `f`'s body with `t` substituted. Plain
`simp` on a goal whose only redex is `f t` fails with `simp made no progress`. Placeholders: the guide's
`def double (n : Nat) : Nat := n + n`, `(k : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (double k)` | `⊢ P (k + k)` |

**R5 · `Nat.add_zero`** changes the **goal**. The lemma is `Nat.add_zero : n + 0 = n` (in the default set).
Placeholders: `(n : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (n + 0)` | `⊢ P n` |

**W2.** `triple (n * 1) = n + n + n` with `triple n = n + n + n`: one `simp [triple]` unfolds (R4), turns
`n * 1` into `n` (R7) and closes the equal sides.

---

## Part 3 · `simp_hyp`

Statement: from `h : a * 1 + 0 = b + 0` prove `a = b`. The goal is already clean; the clutter is in `h`.
Simplify the hypothesis (R6, which uses R7 and R5), then the goal is exactly `h` (R8).

**R6 · `simp at h`** changes the **context**: `h` is rewritten with the default simp set; the goal is
unchanged. If `h` becomes `False`, the goal is closed; if nothing in `h` changes, it fails. Placeholders:
`(n : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `h : P (n * 1) ⊢ P n` | `h : P n ⊢ P n` |

**R7 · `Nat.mul_one`** changes the **goal**. The lemma is `Nat.mul_one : n * 1 = n` (in the default set).
Placeholders: `(n : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (n * 1)` | `⊢ P n` |

**R8 · `exact h`** **closes** a goal that is exactly the statement of `h` (E003). Placeholders: `(G : Prop)`.

| Before | After |
|---|---|
| `h : G ⊢ G` | no goals |

**W3.** From `h : 0 + a * 1 = b`, `simp at h` uses `Nat.zero_add : 0 + n = n` and R7:

| Before `simp at h` | After `simp at h` |
|---|---|
| `h : 0 + a * 1 = b ⊢ a = b` | `h : a = b ⊢ a = b` |

then `exact h` (R8). `simpa using h` does both steps in one: it simplifies `h` and the goal, then closes the
goal with `h`.

---

## Part 4 · `simp_with`

Statement: if `f x = x + 1` for every `x` (hypothesis `hf`), then `f (f a) = a + 2`. Hand `hf` to `simp` (R9):
it rewrites the inner `f a`, then the outer `f (…)`. The arithmetic equation that is left closes inside the same
call (R10, R11).

**R9 · `simp [hf]`** with `hf : ∀ x, f x = e x` changes the **goal**: every `f t` becomes `e t`, for any `t`,
inner occurrences first, so a nested `f (f a)` is rewritten twice by one call. `rw [hf]` would rewrite only the
instances of one pattern per call. Placeholders: `(f : Nat → Nat) (a : Nat) (P : Nat → Prop)`,
`hf : ∀ x, f x = 2 * x`.

| Before | After |
|---|---|
| `⊢ P (f (f a))` | `⊢ P (2 * (2 * a))` |

**R10 · `Nat.add_right_cancel_iff`** changes the **goal**. The lemma is
`Nat.add_right_cancel_iff : m + n = k + n ↔ m = k`; `simp` uses an `↔` lemma to replace the proposition on the
left by the one on the right. A numeral is split as needed: `b + 2` matches `(b + 1) + 1`. Placeholders:
`(a b : Nat)`.

| Before | After |
|---|---|
| `⊢ a + 1 = b + 2` | `⊢ a = b + 1` |

**R11 · `simp` closes an equation whose sides differ by numerals** **closes** the goal: R10 cancels `+ 1`
until `n + 1 = n + 1` is left, `Nat.add_left_cancel_iff : n + m = n + k ↔ m = k` turns it into `1 = 1`, and
`eq_self` turns that into `True`. Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `⊢ n + 1 + 1 + 1 = n + 3` | no goals |

**W4.** With `hg : ∀ x, g x = x + 3`, `simp [hg]` closes `g (g 1) = 7`: R9 twice gives `1 + 3 + 3 = 7`, and
`simp` evaluates numeral arithmetic. **W5.** Definitions and hypotheses mix in one list:
`simp [double, hf]` closes `double (f k) = k + k` when `hf : ∀ x, f x = x * 1`.

---

## Traps

- Plain `simp` does not unfold a `def` you wrote. If the goal has nothing else to simplify, you get
  `simp made no progress`: add the name, `simp [square]`.
- `simp` that changes nothing is an **error**, not a no-op. That includes `simp at h` when `h` is already clean.
- `simp` does not reorder sums (`a + b = b + a` stays, W1) and does not rewrite `a + 1 + 1` to `a + 2` inside
  `P (a + 1 + 1)`: it only cancels numerals in an equation (R10, R11). `omega` is banned in this exercise.
- `simp [h]` uses `h : a = b` left to right only. To rewrite `b` into `a`, write `simp [← h]`.
- `simp` simplifies the goal, not hypotheses: to clean `h`, write `simp at h` (R6).
- If `simp` already closed the goal, a following `exact h` fails with "no goals".

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| routine rewriting with library facts | `simp` | R1 |
| `xs ++ []` → `xs` | `simp` / `simp only [List.append_nil]` | R2 |
| `(xs ++ ys).length` → sum of lengths | `simp` / `simp only [List.length_append]` | R3 |
| unfold your own `def f` | `simp [f]` | R4 |
| `n + 0` → `n`, `n * 1` → `n` | `simp` (`Nat.add_zero`, `Nat.mul_one`) | R5, R7 |
| simplify a hypothesis | `simp at h` | R6 |
| goal is exactly `h` | `exact h` | R8 |
| rewrite with `hf : ∀ x, f x = …` | `simp [hf]` | R9 |
| `a + 1 = b + 2` → `a = b + 1` | `simp` (`Nat.add_right_cancel_iff`) | R10 |
| sides differ only by numerals | `simp` | R11 |
| simplify `h` and close with it | `simpa using h` | W3 |
| see which lemmas `simp` used | `simp?` | |
| see the state | infoview | |
