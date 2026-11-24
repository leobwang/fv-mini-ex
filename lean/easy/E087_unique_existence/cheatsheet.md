# E087 · Unique existence: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `rfl` (E001), `intro` and `exact` (E003),
`fun` and anonymous constructors `⟨_, _⟩` for `∧` and `∃` (E004, E005, E007), `obtain` (E005, E007),
`rw` (E009), `omega` (E011), `refine` with `?_` (E031). **New here:** Mathlib's `ExistsUnique` (notation
`∃!`), the real numbers `ℝ` with the tactic `linarith`, and reading the unreduced `(fun x => …) y` that
`∃!` proofs leave in the infoview.

## How to read an entry

Each entry is one tactic or one term. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- Placeholders: `{α β : Type}` are any types (`ℕ`, `ℤ`, `ℝ`, …); `p : α → Prop` is any property, so
  `p x` is "`x` satisfies `p`"; `P : α → Prop` is "the rest of your goal": the step changes only the
  part inside `P (…)`.
- Hypotheses whose types contain `, ` (every `∀`, `∃`, `∃!`) are listed in a separate **context** row,
  because a `⊢` cell cannot hold them; the **goal** row shows the goal Lean prints.
- "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## `∃!` in one paragraph

`∃! x, p x` reads "there is exactly one `x` with `p x`". Mathlib defines it (`ExistsUnique p`) as
`∃ x, p x ∧ ∀ y, p y → y = x`: an `∃` whose body is an `∧` of *existence* (`p x`) and *uniqueness*
(any `y` with `p y` is `x`). So a proof is a triple `⟨w, hw, hu⟩` (witness `w : α`, `hw : p w`,
`hu : ∀ y, p y → y = w`), and a hypothesis `h : ∃! x, p x` is taken apart into the same three pieces.
Type `∃!` as `\exists!`.

## Reading the goals

| You see | It means |
|---|---|
| `∃! x, p x` | exactly one `x` satisfies `p`; the infoview drops the binder type (`∃! n : ℕ, …` prints `∃! n, …`) |
| `(fun x => p x) w` | `p w`, not yet simplified: the property applied to `w` (R3 shows the reduced form) |
| `∀ (y : α), (fun x => p x) y → y = w` | the uniqueness part: every `y` with `p y` equals `w` |
| `ℝ` | Mathlib's real numbers; numerals in `ℝ` do not compute, so `rfl` fails on `(2 : ℝ) * 3 + 1 = 7` |
| `case refine_1`, `case refine_2` | the goals made by the first and second `?_` of a `refine` |

---

## Part 1 · `unique_sol`

Statement: exactly one natural number `n` has `n + 2 = 5`.

**R1 · `unfold ExistsUnique`** changes the **goal**: it shows the definition of `∃!`. Optional, for
reading only. Placeholders: `{α : Type} (p : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ∃! x, p x` | `⊢ ∃ x, (fun x => p x) x ∧ ∀ (y : α), (fun x => p x) y → y = x` |

**R2 · `refine ⟨w, ?_, ?_⟩`** changes the **goal list**: one goal becomes two, "`w` works" and "only `w`
works". `⟨w, ?_, ?_⟩` is `⟨w, ⟨?_, ?_⟩⟩` flattened (the `∃` takes `w`, the `∧` takes the two holes).
Placeholders: `{α : Type} (p : α → Prop) (w : α)`.

| Before | After |
|---|---|
| `⊢ ∃! x, p x` | `⊢ (fun x => p x) w`, `⊢ ∀ (y : α), (fun x => p x) y → y = w` |

**R3 · `beta_reduce`** changes the **goal**: Mathlib's tactic for *beta reduction*, substituting the
argument into a `fun`. Optional: `exact`, `rfl`, `omega`, `linarith` see through `(fun x => …) w` by
themselves. Placeholders: `(p : α → Prop) (w : α)`.

| Before | After |
|---|---|
| `⊢ (fun x => p x) w` | `⊢ p w` |

**R4 · `refine ⟨w, rfl, ?_⟩`** changes the **goal**: when "`w` works" holds by computation, `rfl` fills
that slot and only the uniqueness goal is left. Over `ℕ`, `3 + 2 = 5` computes, so `rfl` proves it.
Placeholders: `{α β : Type} (f : α → β) (c : α)`, goal `∃! x, f x = f c`.

| Before | After |
|---|---|
| `⊢ ∃! x, f x = f c` | `⊢ ∀ (y : α), (fun x => f x = f c) y → y = c` |

**R5 · `intro y hy`** changes the **context and the goal**: it takes the `y` and the hypothesis `hy`
(already beta-reduced by `intro`). Placeholders: `(p : α → Prop) (w : α)`.

| Before | After |
|---|---|
| `⊢ ∀ (y : α), (fun x => p x) y → y = w` | `y : α, hy : p y ⊢ y = w` |

**R6 · `omega`** **closes** a linear arithmetic goal over `ℕ` or `ℤ`, using the hypotheses (here `hy`).
Placeholders: `(a b y : ℕ)`.

| Before | After |
|---|---|
| `hy : y + a = b + a ⊢ y = b` | no goals |

## Part 2 · `unique_real`

Statement: exactly one real `x` has `2 * x + 1 = 7`. Same shape as Part 1, over `ℝ`.

**R7 · `linarith`** **closes** a linear equation or inequality over an ordered field such as `ℝ` or `ℚ`,
using the hypotheses (it combines them with rational coefficients). It replaces both tools that fail over
`ℝ`: `omega` (only `ℕ`, `ℤ`) and `rfl` (real numerals do not compute; `linarith` proves
`(2 : ℝ) * 3 + 1 = 7` with no hypotheses). Placeholders: `(a b y : ℝ)`.

| Before | After |
|---|---|
| `hy : 2 * y + a = b ⊢ y = (b - a) / 2` | no goals |

**R8 · `⟨w, hw, fun y hy => …⟩`** **closes** the goal as one term: witness, existence proof, uniqueness
function. Any slot may be `by tac`, e.g. `fun y hy => by linarith`. Unlike `intro` (R5), the `fun`
leaves `hy` unreduced: inside that `by` the infoview shows `hy : (fun x => 2 * x + 1 = 7) y` (for
`unique_real`'s property), which is just `2 * y + 1 = 7`; `linarith` reads it fine. Placeholders:
`(p : α → Prop) (w : α) (hw : p w)`.

| Before | After |
|---|---|
| `⊢ ∃! x, p x` | no goals |

## Part 3 · `unique_use`

Statement: if exactly one `n` satisfies `p`, and `a`, `b` both satisfy `p`, then `a = b`.

**R9 · `obtain ⟨x, hx, hu⟩ := h`** changes the **context**: `h` is removed and its three pieces are added.
Placeholders: `{α : Type} (p : α → Prop) (G : Prop)` (`G` is any goal), `h : ∃! x, p x`.

| | Before | After |
|---|---|---|
| context | `h : ∃! x, p x` | `x : α`, `hx : p x`, `hu : ∀ (y : α), (fun x => p x) y → y = x` |
| goal | `⊢ G` | `x : α, hx : p x ⊢ G` |

**R10 · `rw [hu a ha]`** changes the **goal**. `hu a ha : a = x`: apply the `∀` to `a`, then the
implication to `ha : p a`. `rw` replaces every `a` by `x`, and closes the goal by `rfl` if it becomes
`x = x`; `rw [e₁, e₂]` does two rewrites in a row. Placeholders: `(p P : α → Prop) (x a : α)`,
`hu : ∀ y, p y → y = x`.

| Before | After |
|---|---|
| `ha : p a, h : P x ⊢ P a` | `⊢ P x` |

### Worked combinations (W1–W3, on statements that are not the exercise's)

**W1.** `∃! n : ℕ, 2 * n = 8`: R4 with witness `4`, then R5, R6.

```lean-goal
⊢ ∃! n, 2 * n = 8
⊢ ∀ (y : ℕ), (fun n => 2 * n = 8) y → y = 4
⊢ y = 4
```

**W2.** `∃! x : ℝ, 3 * x - 2 = 4` as one term (R8, R7): `⟨2, by linarith, fun y hy => by linarith⟩`.

**W3.** From `h : ∃! z, q z`, `hc : q c`, `hd : q d` prove `c + 1 = d + 1`: R9, then `rw [hu c hc, hu d hd]`
(R10 twice) turns the goal into `x + 1 = x + 1`, which `rw` closes.

```lean-goal
⊢ c + 1 = d + 1
```

---

## Traps

- `rfl` works for `3 + 2 = 5` over `ℕ` but fails over `ℝ`: real numbers are not computable. Use
  `linarith` (R7). `simp` and `norm_num` are banned here.
- `omega` only knows `ℕ` and `ℤ`; over `ℝ` it fails. Use `linarith`.
- `(fun x => p x) y` is just `p y`; you never need to reduce it by hand (R3 is only for reading).
  `intro y hy` shows `hy` reduced, `fun y hy => by …` shows it unreduced; both are the same fact.
- `hu a ha` has type `a = x`, so `rw [hu a ha]` turns `a` into `x`, not the reverse. Rewrite both `a`
  and `b` to the same `x`; then the goal is `x = x`.
- `obtain … := h` removes `h`; take everything you need from it at once.
- `ExistsUnique.unique` (which proves `a = b` in one step) is banned: the point is to take `h` apart.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| see what `∃!` means | `unfold ExistsUnique` | R1 |
| prove `∃! x, p x`: two goals | `refine ⟨w, ?_, ?_⟩` | R2 |
| read `(fun x => p x) w` as `p w` | `beta_reduce` (optional) | R3 |
| existence by computation | `refine ⟨w, rfl, ?_⟩` | R4 |
| start the uniqueness part | `intro y hy` | R5 |
| linear arithmetic over `ℕ`, `ℤ` | `omega` | R6 |
| linear arithmetic over `ℝ` (also numerals) | `linarith` | R7 |
| whole `∃!` proof as a term | `⟨w, hw, fun y hy => by tac⟩` | R8 |
| take `h : ∃! x, p x` apart | `obtain ⟨x, hx, hu⟩ := h` | R9 |
| turn `a` into the unique `x` | `rw [hu a ha]` | R10 |
| see the state | infoview | |
