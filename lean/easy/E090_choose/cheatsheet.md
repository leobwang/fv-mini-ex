# E090 · choose: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `exact` (E003), term-mode proofs and `fun`
(E004), anonymous constructors `⟨_, _⟩` for `∧` (E005) and `∃` (E007), `unfold` (E012, E030), `refine`
with `?_` (E031). **New here:** Mathlib's `choose` tactic (Skolem functions), `Function.Surjective`, and
the term-level witness `Exists.choose` / `Exists.choose_spec` with `noncomputable def`.

## How to read an entry

Each entry is one tactic or one term. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- Placeholders: `{α β : Type}` are any types (`ℕ`, `ℤ`, …); `Q : α → β → Prop` is any relation, so
  `Q a b` is "the statement about `a` and `b`"; `A B : α → β → Prop` are two such relations.
- `P : α → Prop` is "the rest of your goal": the step changes only the part inside `P (…)`.
- Hypotheses whose types contain `, ` (every `∀`/`∃`) are listed in a separate **context** row, because a
  `⊢` cell cannot hold them; the **goal** row shows the goal Lean prints.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Skolem functions in one paragraph

A hypothesis `h : ∀ a, ∃ b, Q a b` promises, for every `a`, *some* `b`. Choosing one such `b` for every
`a` at once gives a function `g : α → β` with `∀ a, Q a (g a)`: a *Skolem function*. Building `g` needs
the axiom of choice, `Classical.choice` (Lean's axiom that turns a proof of "`α` is nonempty" into an
element of `α`). Mathlib's tactic `choose g hg using h` does this in one step. For a single `∃`, the same
axiom gives `h.choose` (the witness) and `h.choose_spec` (its property). Because there is no algorithm
behind `h.choose`, Lean cannot compile it to code: a `def` using it must be `noncomputable`. Proofs are
never compiled, so they may use it freely.

## Reading the goals

| You see | It means |
|---|---|
| `∀ (a : α), Q a (g a)` | `∀ a, Q a (g a)`; the infoview always prints the binder type |
| `∃ f, ∀ (a : α), Q a (f a)` | "some function `f : α → β` works"; the infoview drops `f`'s type |
| `∃ g, …` with `g : ℕ → ℕ` in the context | the bound `g` of the goal is a different variable from the context's `g` |
| `hg : ∀ (b : ℕ), f (g b) = b` against the goal `∀ (y : ℕ), f (g y) = y` | bound names do not matter: `∀ b, R b` and `∀ y, R y` are the same statement, so `exact` accepts it |
| `∃ n, n * n = 49` | `∃ n : ℕ, n * n = 49`; the infoview drops the binder type |
| `f g : ℤ → ℤ` | two hypotheses of the same type on one line: `f : ℤ → ℤ` and `g : ℤ → ℤ` |
| `g n > n` | notation for `n < g n` |
| `Function.Surjective f` | `∀ b, ∃ a, f a = b`: every `b` is hit by `f` (R5) |
| `h.choose` | `Exists.choose h`, the witness of `h : ∃ a, Q a` (R6) |
| `h.choose_spec` | `Exists.choose_spec h : Q h.choose`, its property (R8) |
| `noncomputable def` | a definition Lean does not compile to code (it uses choice) |

---

## Part 1 · `choose_fun`

Statement: from `h : ∀ n, ∃ m, f m > n`, produce `g : ℕ → ℕ` with `∀ n, f (g n) > n`.

**R1 · `choose g hg using h`** changes the **context**: `h` is removed; a function `g` and its property `hg`
are added; the goal `G` (any `Prop`) is unchanged.
Placeholders: `{α β : Type} (Q : α → β → Prop) (G : Prop)`, `h : ∀ a, ∃ b, Q a b`. In the exercise `Q n m` is `f m > n` and `G` is the `∃ g, …` goal.

| | Before | After |
|---|---|---|
| context | `h : ∀ (a : α), ∃ b, Q a b` | `g : α → β`, `hg : ∀ (a : α), Q a (g a)` |
| goal | `⊢ G` | `g : α → β ⊢ G` |

**R2 · `refine ⟨g, ?_⟩`** changes the **goal**: `g` is the witness of the `∃`, and the goal becomes the
property of `g`. When that property is literally a hypothesis `hg`, write `exact ⟨g, hg⟩` instead: same
step, goal closed. Placeholders: `(g : α → β) (hg : ∀ a, Q a (g a))`.

| Before | After |
|---|---|
| `⊢ ∃ f, ∀ (a : α), Q a (f a)` | `⊢ ∀ (a : α), Q a (g a)` |

## Part 2 · `choose_two`

Statement: from `h : ∀ x, ∃ y, y > x ∧ p x y`, produce `g` with `∀ x, g x > x ∧ p x (g x)`.

**R3 · `choose g hA hB using h`** changes the **context**: with one name per conjunct, `choose` also splits
the `∧` under the `∃`; the goal `G` is unchanged. Placeholders: `(A B : α → β → Prop) (G : Prop)`,
`h : ∀ a, ∃ b, A a b ∧ B a b`. In the exercise `A x y` is `y > x` and `B x y` is `p x y`.

| | Before | After |
|---|---|---|
| context | `h : ∀ (a : α), ∃ b, A a b ∧ B a b` | `g : α → β`, `hA : ∀ (a : α), A a (g a)`, `hB : ∀ (a : α), B a (g a)` |
| goal | `⊢ G` | `g : α → β ⊢ G` |

When `G` is `∃ f, ∀ a, A a (f a) ∧ B a (f a)`, R2 then gives `⊢ ∀ (a : α), A a (g a) ∧ B a (g a)`,
which is not literally `hA` or `hB`.

**R4 · `exact fun a => ⟨hA a, hB a⟩`** **closes** the goal: a proof of `∀ a, X a ∧ Y a` is a function
taking `a` to a pair of proofs. Placeholders: `(g : α → β) (hA : ∀ a, A a (g a)) (hB : ∀ a, B a (g a))`.
R2 and R4 combine into one term: `exact ⟨g, fun a => ⟨hA a, hB a⟩⟩`.

| Before | After |
|---|---|
| `⊢ ∀ (a : α), A a (g a) ∧ B a (g a)` | no goals |

## Part 3 · `right_inverse`

Statement: a surjective `f : ℕ → ℕ` has a right inverse `g`: `∀ y, f (g y) = y`.

**R5 · `Function.Surjective f`** is Mathlib's definition `∀ b, ∃ a, f a = b`. `unfold Function.Surjective
at hf` changes the **context** to show it. `choose` looks through the name by itself, so the unfold is
optional: `choose g hg using hf` gives `g : β → α`, `hg : ∀ (b : β), f (g b) = b` directly (W3).
Placeholders: `{α β : Type} (f : α → β)`.

| | Before | After |
|---|---|---|
| context | `hf : Function.Surjective f` | `hf : ∀ (b : β), ∃ a, f a = b` |
| goal | `hf : Function.Surjective f ⊢ G` | `⊢ G` |

Then R1, R2 as in Part 1.

## Part 4 · `root_spec`

Statement: `root h * root h = 49`, where `root h` is defined as `h.choose` for `h : ∃ n : ℕ, n * n = 49`.

**R6 · `Exists.choose`** is a **term**: for `h : ∃ a, Q a`, `h.choose : α` is the witness. A `def` built
from it needs `noncomputable` (the guide's `wit h := h.choose` is one, like the exercise's `root`).
Inside a proof it is an ordinary `α`. Placeholders: `{α : Type} (Q P : α → Prop) (h : ∃ a, Q a)`.

| Before | After |
|---|---|
| `⊢ P h.choose` | no goals (by `exact hP h.choose`, with `hP : ∀ a, P a`) |

**R7 · `unfold wit`** changes the **goal**: the defined name is replaced by its body. Optional, because
`exact` and term mode see through definitions anyway (W4); it shows you what to close.

| Before | After |
|---|---|
| `⊢ P (wit h)` | `⊢ P h.choose` |

**R8 · `Exists.choose_spec`** **closes** the goal. The lemma: `Exists.choose_spec (h : ∃ a, Q a) :
Q h.choose`. Placeholders: `{α : Type} (Q : α → Prop) (h : ∃ a, Q a)`. In the exercise `Q n` is
`n * n = 49`, so `Q h.choose` is `h.choose * h.choose = 49`.

| Before | After |
|---|---|
| `⊢ Q h.choose` | no goals |

### Worked combinations (W1–W4, on statements that are not the exercise's)

**W1.** `h : ∀ n, ∃ m, n < m * m`: R1 then `exact ⟨g, hg⟩` (R2).

```lean-goal
⊢ ∃ g, ∀ (n : ℕ), n < g n * g n
```

**W2.** Two `∀`s: `choose` makes a two-argument function. After `choose g hA hB using h`, the context holds
`g : ℕ → ℕ → ℕ`, `hA : ∀ (a b : ℕ), a ≤ g a b`, `hB : ∀ (a b : ℕ), b ≤ g a b`; close with
`exact ⟨g, fun a b => ⟨hA a b, hB a b⟩⟩` (R2, R4).

**W3.** `choose g hg using hf` with `hf : Function.Surjective f` and no unfold: the context becomes
`f g : ℤ → ℤ`, `hg : ∀ (b : ℤ), f (g b) = b`, and `hg y` rewrites `f (g y)` to `y`.

**W4.** `example (h : ∃ n : ℕ, n + n = 10) : wit h + wit h = 10 := h.choose_spec`: term mode unfolds
`wit h` to `h.choose` by itself, so R8 fits without R7.

---

## Traps

- `choose` takes a hypothesis of shape `∀ …, ∃ …, …` (or a name that unfolds to one); it fails on a
  hypothesis that starts with `∃` and has no `∀`. For one `∃`, use `obtain ⟨a, ha⟩ := h` (E007) or
  `h.choose` / `h.choose_spec`.
- With one name after `g`, `choose g hg using h` on `∃ b, A a b ∧ B a b` keeps the `∧` in `hg`; give two
  names to split it (R3).
- `choose … using h` removes `h` from the context.
- A `def` that uses `h.choose` must be `noncomputable`; a theorem never needs the keyword.
- `obtain ⟨m, hm⟩ := h n` gives a witness for one `n` only; it cannot build a function of `n`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `h : ∀ a, ∃ b, Q a b` → function `g`, `hg : ∀ a, Q a (g a)` | `choose g hg using h` | R1 |
| return the function for `∃ f, …` | `exact ⟨g, hg⟩` / `refine ⟨g, ?_⟩` | R2 |
| also split `∃ b, A ∧ B` | `choose g hA hB using h` | R3 |
| prove `∀ a, X a ∧ Y a` from two facts | `exact fun a => ⟨hA a, hB a⟩` | R4 |
| see what surjective means | `unfold Function.Surjective at hf` | R5 |
| witness of one `∃` (term) | `h.choose` (`noncomputable def` if stored) | R6 |
| see a definition's body | `unfold name` | R7 |
| property of the witness | `exact h.choose_spec` | R8 |
| see the state | infoview | |
