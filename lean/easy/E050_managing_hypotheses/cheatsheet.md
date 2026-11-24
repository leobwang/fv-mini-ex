# E050 · Managing hypotheses: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `exact`, `rfl`, `have`, `rw [h]` in the goal,
the anonymous constructor `⟨_, _⟩`, and applying a proof of `A → B` (or of `∀ x, P x`) like a function.
**New here:** tactics that change the **context** (the hypotheses above `⊢`) instead of the goal:
`specialize`, `replace`, `subst`, `rw … at h₁ h₂`, and the core lemma `Nat.zero_add`. No Mathlib.

The exercise is about these named tactics. `simp`, `omega`, `decide` and friends are banned, and although
plain `rw` in the goal could finish most parts, the point is to reshape the hypotheses (honor system).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P`, `Q` are "the rest of a statement" (`P : α → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits.
- `{α : Type}` is any type; the entries work for `Nat` or anything else.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `h : ∀ (n : Nat), f n = 2 * n` | `h` is a function: `h 3 : f 3 = 2 * 3`. Lean always prints the binder type `(n : Nat)` |
| `h : f 4 = 2 * 4` | after `specialize h 4`: `2 * 4` is not computed to `8` in the hypothesis, but `rfl` will compute it |
| a hypothesis moves to the bottom | `replace` and `rw … at` re-add the hypothesis, so it is listed last |
| a variable vanishes | `subst` removed it, together with its equation |
| `h : b = b` | what `rw [h] at *` makes of `h : a = b` itself (W4) |

---

## Part 1 · `specialize_ex`

Statement: from `h : ∀ n, f n = 2 * n`, prove `f 3 + f 4 = 14`. You need two instances of `h`: copy one
(R1), turn `h` itself into the other (R2), then rewrite the goal with both (R3).

**R1 · `have ha := h a`** changes the **context**: it adds the instance `ha : P a` and keeps `h`. `h a` is
`h` applied to `a`. Placeholders: `{α : Type} (P : α → Prop) (a : α) (h : ∀ x, P x)`.

| Before | After |
|---|---|
| `⊢ P a ∧ ∀ (x : α), P x` | `ha : P a ⊢ P a ∧ ∀ (x : α), P x` |

**R2 · `specialize h a`** changes the **context**: `h : ∀ x, P x` is **replaced** by `h : P a`; the general
statement is gone. Take every other instance first with R1. Placeholders: as in R1.

| Before | After |
|---|---|
| `h : ∀ (x : α), P x` and `⊢ P a` | `h : P a ⊢ P a` |

**R3 · `rw [h1, h2]`** changes the **goal**: it rewrites with `h1`, then with `h2` (`rw [h1, h2]` is
`rw [h1]; rw [h2]`), and finally tries `rfl`, which closes a goal like `2 + 4 = 6` by computation. So
nothing follows the last `rw`. Placeholders: `(f : Nat → Nat) (h1 : f 1 = 2) (h2 : f 2 = 4)`.

| Before | After `rw [h1]` | After `rw [h2]` |
|---|---|---|
| `⊢ f 1 + f 2 = 6` | `⊢ 2 + f 2 = 6` | no goals (`2 + 4 = 6` closed by `rfl`) |

**W1 (on `g n = n + 1`):** R1, R2, R3:

| Before | After `have h2 := h 2` | After `specialize h 5` |
|---|---|---|
| `⊢ g 2 * g 5 = 18` | `h2 : g 2 = 2 + 1 ⊢ g 2 * g 5 = 18` | `h : g 5 = 5 + 1, h2 : g 2 = 2 + 1 ⊢ g 2 * g 5 = 18` |

then `rw [h2, h]` leaves `(2 + 1) * (5 + 1) = 18`, which its final `rfl` closes.

---

## Part 2 · `replace_ex`

Statement: from `h : 0 + n = 5` and `g : n = 5 → n * 2 = 10`, prove `n * 2 = 10`. `g` wants exactly
`n = 5`, and `0 + n = 5` is **not** that by computation (Trap 1). Replace `h` by a clean `h : n = 5` (R4),
proving it with R5, then apply `g` to it.

**R4 · `replace h : T := proof`** changes the **context**: afterwards `h` has type `T`, and the old `h` is
gone. `proof` may still use the old `h` (in the exercise: `by rw [Nat.zero_add] at h; exact h`). Compare
`have h' : T := proof`, which keeps both. Placeholders:
`{α : Type} (P Q : α → Prop) (a : α) (h : P a) (f : P a → Q a)`.

| Before | After `replace h : Q a := f h` |
|---|---|
| `h : P a ⊢ Q a` | `h : Q a ⊢ Q a` |

**R5 · `rw [Nat.zero_add] at h`** changes the **context**: `h` is rewritten; the goal is unchanged. The lemma
is `Nat.zero_add (n : Nat) : 0 + n = n` (core Lean, no import). Placeholders: `(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `h : P (0 + n) ⊢ P n` | `h : P n ⊢ P n` |

**W3:** R4 with R5 inside, then a goal rewrite:

| Before | After `replace h : m = 3 := by rw [Nat.zero_add] at h; exact h` |
|---|---|
| `h : 0 + m = 3 ⊢ m + 1 = 4` | `h : m = 3 ⊢ m + 1 = 4` |

then `rw [h]` turns the goal into `3 + 1 = 4`, which its final `rfl` closes.

---

## Part 3 · `subst_ex`

Statement: from `h1 : a = b`, `h2 : b = c`, `h3 : c = 7`, prove `a + b = 14`. Eliminate the variables
from the end of the chain: `c` (with `h3`), then `b`, then `a`. What is left is `7 + 7 = 14`, closed by `rfl`.
`subst h3 h2 h1` does the three steps in that order.

**R6 · `subst h`** changes the **context** (and the goal): for `h : x = e` or `h : e = x`, where `x` is a
local variable that does not occur in `e`, it deletes `x` and `h` and replaces `x` by `e` everywhere.
When **both** sides are variables, `h : x = y`, it deletes the **right-hand** one, `y`, and writes `x` for it
(third row). Placeholders: `{α : Type} (P : α → Prop) (g : α → α) (x y : α)`.

| Before | After |
|---|---|
| `h : x = g y, hp : P (g y) ⊢ P x` | `hp : P (g y) ⊢ P (g y)` |
| `h : g y = x, hp : P (g y) ⊢ P x` | `hp : P (g y) ⊢ P (g y)` |
| `h : x = y, hp : P x ⊢ P y` | `hp : P x ⊢ P x` |

**W2 (a chain `x = y`, `y = z`, `z = 2`):** R6 three times, from the end:

| Before | After `subst e3` | After `subst e2` | After `subst e1` |
|---|---|---|---|
| `e3 : z = 2 ⊢ x * y = 4` | `e2 : y = 2 ⊢ x * y = 4` | `e1 : x = 2 ⊢ x * 2 = 4` | `⊢ 2 * 2 = 4` |

then `rfl`. Any order works here, but the states differ: `subst e1` first (with `e1 : x = y`, both sides
variables) deletes `y` and writes `x` for it, so `e2` becomes `x = z` and the goal `x * x = 4`. The other
hypotheses keep their names while their statements change.

---

## Part 4 · `rw_at_two`

Statement: from `h : a = b`, `h1 : a + 1 = 5`, `h2 : 2 * a = 8`, prove `b + 1 = 5 ∧ 2 * b = 8`. Rewrite both
hypotheses at once (R7); they are then exactly the two conjuncts (R8).

**R7 · `rw [h] at h1 h2`** changes the **context**: each listed hypothesis is rewritten with `h`; the goal is
unchanged. `at h1 ⊢` would also rewrite the goal; `at *` rewrites everything (W4). Placeholders:
`{α : Type} (P Q : α → Prop) (a b : α) (h : a = b)`.

| Before | After |
|---|---|
| `h1 : P a, h2 : Q a ⊢ P b ∧ Q b` | `h1 : P b, h2 : Q b ⊢ P b ∧ Q b` |

**R8 · `exact ⟨ha, hb⟩`** **closes** `A ∧ B` from `ha : A` and `hb : B`: `⟨_, _⟩` is the anonymous
constructor, here `And.intro`. Placeholders: `(A B : Prop) (ha : A) (hb : B)`.

| Before | After |
|---|---|
| `ha : A, hb : B ⊢ A ∧ B` | no goals |

**W4 · `rw [h] at *`** also rewrites `h` itself:

| Before | After `rw [h] at *` |
|---|---|
| `h : a = b, h1 : a + 1 = 3 ⊢ b + 1 = 3 ∧ a = b` | `h : b = b, h1 : b + 1 = 3 ⊢ b + 1 = 3 ∧ b = b` |

---

## Traps

1. `0 + n` does **not** compute to `n`; `n + 0` does. Addition on `Nat` recurses on its second argument, so
   `exact g h` with `h : 0 + n = 5` fails (type mismatch): rewrite `h` with `Nat.zero_add` first (R5).
2. `specialize h a` destroys the `∀`. If you need `h` at two points, `have` the first one (R1) before
   specializing to the second (R2).
3. `subst h` needs a **local variable** on one side that does not occur on the other. It fails on
   `h : f 3 = 2 * 3` (neither side is a variable; "invalid equality proof"): use `rw [h]` there. With two
   variables, `h : a = b` removes `b`, not `a` (R6, third row). To choose which variable goes, name it:
   `subst a` finds an equation for `a` itself and removes `a`.
4. `rw … at *` rewrites the equation itself into `b = b` (W4); harmless, but it no longer says anything.
5. `rw [h1, h2]` already tries `rfl` at the end; a following `rfl` then fails with "no goals".
6. `clear h` deletes a hypothesis you no longer need. It is never required here.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| an instance of `h : ∀ x, P x`, keep `h` | `have ha := h a` | R1 |
| turn `h : ∀ x, P x` into `h : P a` | `specialize h a` | R2 |
| rewrite the goal with several equations, close by computation | `rw [h1, h2]` | R3 |
| same name, new statement | `replace h : T := proof` | R4 |
| `0 + n → n` in a hypothesis | `rw [Nat.zero_add] at h` | R5 |
| eliminate `x` using `h : x = e` (or `e = x`) | `subst h` (several: `subst h3 h2 h1`) | R6 |
| rewrite in several hypotheses | `rw [h] at h1 h2` (everything: `at *`) | R7 |
| prove `A ∧ B` | `exact ⟨ha, hb⟩` | R8 |
| close `7 + 7 = 14` | `rfl` | |
| see the state | infoview | |
