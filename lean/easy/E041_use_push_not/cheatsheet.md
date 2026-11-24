# E041 · use and push Not: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `intro` (E003), `∃` and `⟨x, h⟩` (E007), `¬`
as `→ False` (E008), `rw` (E009) and `omega` (E011).
**New here:** Mathlib (`import Mathlib`) and two of its tactics.
- `push Not` moves a `¬` inward through `∀`, `∃` and order relations, using Mathlib's lemmas `not_forall`,
  `not_exists`, `not_lt`, `not_le` (and `not_not` for `¬¬p`). Several of them are classical: `¬ ∀ x, P x → ∃ x,
  ¬ P x` needs the law of excluded middle, so a proof using it depends on the axiom `Classical.choice`.
  `push_neg` is its older name: it still works but prints a deprecation warning.
- `use a` gives the witness of an `∃` goal and then tries to close what is left (R6–R9).

## How to read an entry

Each entry is one tactic call. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the hypotheses
  that change. "no goals" means the tactic closed the goal.
- `P` is "the rest of your goal" (`P : α → Prop`, a predicate on `α`). The step changes only the part inside
  `P (…)`.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[LinearOrder α]` is a
  requirement on `α` (a *type class*): `LinearOrder α` means `≤` and `<` on `α` form a total order, so any
  two elements compare. `ℕ`, `ℤ`, `ℚ`, `ℝ` qualify. `[Preorder α]` asks less (`≤` reflexive and transitive).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ`, `ℤ` | `Nat`, `Int` (type `\N`, `\Z`) |
| `¬P x` | `P x → False`; the infoview prints no space after `¬` |
| `¬∀ (x : α), P x` | "not every `x` satisfies `P`"; the binder type is shown for `∀` |
| `∃ x, ¬P x` | "some `x` fails `P`"; the binder type is hidden for `∃` (hover to see it) |
| `∃ x y, P x y` | `∃ x, ∃ y, P x y` |
| `a ≠ b` | `¬ (a = b)`; `push Not` writes it this way |
| `b ≤ a` after `push Not` on `¬a < b` | the order flipped: `push Not` never leaves `¬` in front of `<` or `≤` |
| `case h` | the goal tag `use` gives the goal it leaves; ignore it |

---

## Part 1 · `not_all_small`

Statement: `¬ ∀ n : ℕ, n < 5`, "not every natural number is below 5". Push the negation in (R1, R2): the goal
becomes an `∃` with a `≤` inside. Then name a witness (R6); `use` closes the rest by itself (R7).

**R1 · `push Not` on `¬ ∀`** changes the **goal**. Lemma `not_forall : (¬ ∀ x, P x) ↔ ∃ x, ¬ P x`.
Placeholders: `{α : Type} (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ¬∀ (x : α), P x` | `⊢ ∃ x, ¬P x` |

**R2 · `push Not` on `¬ (a < b)`** changes the **goal**. Lemma `not_lt : ¬ a < b ↔ b ≤ a`. Placeholders:
`{α : Type} [LinearOrder α] (a b : α)`. In a real goal R1 and R2 happen in the same `push Not` call.

| Before | After |
|---|---|
| `⊢ ¬a < b` | `⊢ b ≤ a` |

**R6 · `use a`** changes the **goal**: it fills the witness of the outer `∃`, like `refine ⟨a, ?_⟩` (E007,
TACTIC_STATES "Structure"). Placeholders: `{α : Type} (P : α → Prop) (a : α)`. If the rest cannot be closed
automatically (R7), it stays as the goal.

| Before | After |
|---|---|
| `⊢ ∃ x, P x` | `⊢ P a` |

**R7 · `use a` that closes the goal** changes the **goal list**: after filling the witness, `use` runs `rfl`
and `trivial` on what is left. `a ≤ a` is closed by `rfl` (Mathlib registers `le_refl : a ≤ a` with `rfl`), a
numeral equation such as `4 * 4 = 16` by evaluation. Placeholders: `{α : Type} [Preorder α] (a : α)`.

| Before | After |
|---|---|
| `⊢ ∃ x, a ≤ x` | no goals |
| `⊢ ∃ n, n * n = 16` (`use 4`) | no goals |

**W1 · R1 + R3, R6, then `norm_num`.** A strict inequality of numerals is *not* closed by `use`:

| Before | After `push Not` | After `use 11` | After `norm_num` |
|---|---|---|---|
| `⊢ ¬∀ (x : ℤ), x ≤ 10` | `⊢ ∃ x, 10 < x` | `⊢ 10 < 11` | no goals |

## Part 2 · `exists_pair`

Statement: `∃ a b : ℕ, a + b = 7 ∧ a * b = 12`: two naturals with sum 7 and product 12. Find them on paper,
then give both witnesses at once (R8); `use` checks both conjuncts itself (R9).

**R8 · `use a, b`** changes the **goal**: one witness per `∃`, in order. Placeholders:
`{α : Type} (P : α → α → Prop) (a b : α)`.

| Before | After |
|---|---|
| `⊢ ∃ x y, P x y` | `⊢ P a b` |

**R9 · `use a, b` on `∃ x y, A ∧ B`** changes the **goal list**: after the witnesses, `use` also splits the
`∧` and tries `rfl` on each side; when both close, no goal is left. Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ ∃ x y, x = a ∧ y = b` | no goals |

**W3 · R8 + R9 with numerals.** `use 3, 5` evaluates `3 * 5 = 15` and `3 + 5 = 8`:

| Before | After |
|---|---|
| `⊢ ∃ a b, a * b = 15 ∧ a + b = 8` | no goals |

If one conjunct is false for your witnesses, `use` leaves the whole `∧` as the goal (for example
`2 + 3 = 5 ∧ 2 * 3 = 7` after `use 2, 3`): a sign the witnesses are wrong.

## Part 3 · `unbounded`

Statement: for `f : ℕ → ℕ` with `hf : ∀ n, f n = 2 * n`, `¬ ∃ M, ∀ n, f n ≤ M`: no `M` bounds every value of
`f`. Push the negation through both quantifiers and the `≤` (R4, R5, R3) to get a `∀ M, ∃ n, …` goal.
Introduce `M` (R10), pick an `n` that beats it (R6), rewrite `f` with `hf` (R11), finish with `omega` (R12).

**R4 · `push Not` on `¬ ∃`** changes the **goal**. Lemma `not_exists : (¬ ∃ x, P x) ↔ ∀ x, ¬ P x`.
Placeholders: `{α : Type} (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ¬∃ x, P x` | `⊢ ∀ (x : α), ¬P x` |

**R5 · `push Not` through nested quantifiers** changes the **goal**: one call goes all the way in, flipping
each quantifier it passes (`∃ ↔ ∀`). Placeholders: `{α β : Type} (Q : α → β → Prop)`.

| Before | After |
|---|---|
| `⊢ ¬∃ x, ∀ (y : β), Q x y` | `⊢ ∀ (x : α), ∃ y, ¬Q x y` |

**R3 · `push Not` on `¬ (a ≤ b)`** changes the **goal**. Lemma `not_le : ¬ a ≤ b ↔ b < a`. Placeholders:
`{α : Type} [LinearOrder α] (a b : α)`. When the innermost statement of R5 is an order, this happens in the
same call.

| Before | After |
|---|---|
| `⊢ ¬a ≤ b` | `⊢ b < a` |

**R10 · `intro x`** (E003) changes the **context and the goal**: the `∀` variable becomes a hypothesis.
Placeholders: `{α : Type} (P : α → Prop)`. The name you write is the name you get.

| Before | After |
|---|---|
| `⊢ ∀ (y : α), P y` | `x : α ⊢ P x` |

**R11 · `rw [hf]` with a `∀` hypothesis** changes the **goal**. `hf : ∀ n, f n = g n` is an equation for every
`n`; `rw` chooses `n` from the first `f _` it finds. Placeholders: `(f g : ℕ → ℕ) (t : ℕ) (P : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (f t)` | `⊢ P (g t)` |

**R12 · `omega`** (E011) **closes** a linear (in)equality over `ℕ` or `ℤ`: `+`, `-`, `*` by a numeral,
`<`, `≤`, `=`. Placeholders: `(m : ℕ)`.

| Before | After |
|---|---|
| `⊢ m < 3 * (m + 1)` | no goals |

**W2 · the whole chain on another function.** `g n = n + 3`, and the claim is that no `B` is strictly above
every `g n`. Here `n := B` works because the inner goal is `≤`:

| Before | After `push Not` | After `intro B` | After `use B` | After `rw [hg]` |
|---|---|---|---|---|
| `⊢ ¬∃ B, ∀ (n : ℕ), g n < B` | `⊢ ∀ (B : ℕ), ∃ n, B ≤ g n` | `B : ℕ ⊢ ∃ n, B ≤ g n` | `⊢ B ≤ g B` | `⊢ B ≤ B + 3` |

Then `omega` closes it.

---

## The same moves on a hypothesis

**W4 · `push Not at h`** changes the **context**: the same rewrites, applied to `h` instead of the goal.
`¬ (a = b)` comes out as `a ≠ b`. Placeholders: `(g : ℕ → ℕ)`. The goal, `∃ n, g n ≠ 0`, does not change;
the table shows the hypothesis.

| Before | After |
|---|---|
| `h : ¬∀ (n : ℕ), g n = 0` | `h : ∃ n, g n ≠ 0` |

## Traps

- `push_neg` is deprecated in this Mathlib: it works but prints a warning. Write `push Not` (capital `N`; it is
  the name of the proposition `Not`).
- `use` closes `a ≤ a` and numeral equations, but not a strict `3 < 4` on numerals: add `norm_num` or `omega`
  (W1).
- `use` closes `a ≤ a` but not `a ≤ b` for different numerals: in Part 1, `use 7` leaves `⊢ 5 ≤ 7`,
  which needs `omega` (R12). Choose the witness that makes both sides equal.
- In Part 3 the inner goal after `push Not` is strict (`M < f n`). A witness equal to the bound does not work for
  every `M`; pick one that is strictly larger for all `M`, including `M = 0`.
- `rw [hf]` needs `f _` to appear in the goal: do it after `use`, when the goal mentions `f` at a concrete
  argument.
- `intro M` on `¬ ∃ M, …` does not give you `M`: `¬ A` is `A → False`, so it introduces the whole `∃` as a
  hypothesis and leaves the goal `False`. Push first, then introduce the `∀`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `¬ ∀ x, P x` → `∃ x, ¬ P x` | `push Not` | R1 |
| `¬ (a < b)` → `b ≤ a`, `¬ (a ≤ b)` → `b < a` | `push Not` | R2, R3 |
| `¬ ∃ x, P x` → `∀ x, ¬ P x` | `push Not` | R4 |
| negation through several quantifiers | one `push Not` | R5 |
| the same on a hypothesis | `push Not at h` | W4 |
| give a witness | `use a` | R6 |
| witness, goal then trivial | `use a` closes it | R7 |
| several witnesses | `use a, b` | R8, R9 |
| strict numeral inequality left after `use` | `norm_num` / `omega` | W1 |
| goal `∀ x, …` | `intro x` | R10 |
| rewrite with `hf : ∀ n, f n = …` | `rw [hf]` | R11 |
| linear arithmetic over `ℕ` | `omega` | R12 |
| see the state | infoview (cursor after a tactic) | |
