# E038 · Even and Odd: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `∃` with `obtain ⟨x, hx⟩ := h`,
`refine ⟨w, ?_⟩` (E007), the `rfl` pattern in `obtain` (E025), and `by` inside a term (E004).
**New here:** Mathlib (`import Mathlib`), the number types `ℕ` and `ℤ`, Mathlib's predicates `Even` and `Odd`,
and the tactic `ring`. The whole problem rests on two definitions:

- `Even n` is **defined** as `∃ r, n = r + r` (for any type with `+`).
- `Odd n` is **defined** as `∃ m, n = 2 * m + 1` (for any semiring, e.g. `ℕ`, `ℤ`).

Both are `∃`-statements, so the E007 moves apply unchanged: take a hypothesis apart to get the witness and its
equation, and prove a goal by giving a witness and checking the equation.

## How to read an entry

Each entry is one tactic or one term. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the hypotheses
  that change. "no goals" means the step closed the goal.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- A hypothesis `k` in an example only finishes it; it shows what the goal became.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Semiring α]` is a
  requirement on `α` (a *type class*); Lean shows it in the context as `inst✝ : Semiring α`. Each entry says
  which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ`, `ℤ` | Mathlib's names for `Nat` and `Int` (type `\N`, `\Z`) |
| `Even n` | `∃ r, n = r + r`: `n` is the sum of some `r` with itself |
| `Odd n` | `∃ m, n = 2 * m + 1` |
| `n ^ 2` | `n * n`; the exponent is a natural-number numeral |
| `a + b + (a + b)` | `(a + b) + (a + b)`: `+` groups to the left, so Lean drops the first pair of parentheses |
| `2 * m + 1 + 1` | `(2 * m + 1) + 1`: what `n + 1` became after `n` was replaced by `2 * m + 1` |
| `inst✝ : Add α` | the instance from `[Add α]`: `α` has a `+` |
| `inst✝ : Semiring α` | `α` has `0 1 + *` with the usual laws (`ℕ`, `ℤ`, `ℚ`, `ℝ`); needed by `Odd`, which mentions `2` and `1` |
| `inst✝ : CommSemiring α` | a semiring with commutative `*`; what `ring` needs |

---

## Part 1 · `even_mul_any`

Statement: for `m n : ℕ` with `h : Even m`, `Even (m * n)`. Unpack `h` and substitute `m := k + k` (R2); the
goal becomes `Even ((k + k) * n)`. Distribute: `(k + k) * n = k * n + k * n`, so the witness is the half
`k * n` (R4, or R7). The equation left is a ring identity (R6).

**R1 · `obtain ⟨r, hr⟩ := h`** with `h : Even n` changes the **context**: `h` is replaced by the witness
`r : α` and its equation `hr : n = r + r`. `Even n` unfolds to an `∃`, so the E007 pattern works on it
directly. The witness is the **half** `r`, and the equation says `r + r`, not `2 * r`.
Placeholders: `{α : Type} [Add α] (n : α) (P : α → Prop)`.

| Before | After |
|---|---|
| `h : Even n ⊢ P n` | `r : α, hr : n = r + r ⊢ P n` |

**R2 · `obtain ⟨r, rfl⟩ := h`** with `h : Even n` changes the **context and the goal**. Writing `rfl` in place of
a name for the equation `n = r + r` substitutes it at once (as in E025): `n` and `h` leave the
context and every `n` in the goal becomes `r + r`. `n` must be a local variable. Placeholders as in R1.

| Before | After |
|---|---|
| `h : Even n ⊢ P n` | `r : α ⊢ P (r + r)` |

**R4 · `refine ⟨w, ?_⟩`** on `⊢ Even a` changes the **goal**: you commit to the witness `w`, and what remains is
its equation. Placeholders: `{α : Type} [Add α] (a w : α)`.

| Before | After |
|---|---|
| `⊢ Even a` | `⊢ a = w + w` |

**R6 · `ring`** **closes** an equation that holds by the commutative-semiring laws alone (associativity,
commutativity, distributivity, numerals). It expands both sides into sums of monomials and compares them; it
never reads hypotheses. Placeholders: `{α : Type} [CommSemiring α] (a b : α)`; `ℕ` and `ℤ` qualify.
If the witness is wrong, the equation is false and `ring` fails: that is the signal to recompute the witness.

| Before | After |
|---|---|
| `⊢ 2 * a + 2 * b = a + b + (a + b)` | no goals |

**R7 · `exact ⟨w, by ring⟩`** **closes** `⊢ Even a` (or `⊢ Odd a`) in one step: R4 (or R5) and R6 as one term,
where `by ring` proves the equation the `?_` would have left. Placeholders: `{α : Type} [CommSemiring α] (a : α)`.

| Before | After |
|---|---|
| `⊢ Even (2 * a)` | no goals |

**W1 · Even `n` → even `n + 2`** over `ℕ` (R2, R4, R6). Witness: `r + r + 2 = (r + 1) + (r + 1)`.

| Before | After `obtain ⟨r, rfl⟩ := h` | After `refine ⟨r + 1, ?_⟩` | After `ring` |
|---|---|---|---|
| `h : Even n ⊢ Even (n + 2)` | `r : ℕ ⊢ Even (r + r + 2)` | `⊢ r + r + 2 = r + 1 + (r + 1)` | no goals |

## Part 2 · `odd_add_odd_even`

Statement: for `m n : ℕ` with `hm : Odd m` and `hn : Odd n`, `Even (m + n)`. Unpack both hypotheses with
substitution (R3 twice, with two different witness names). The goal becomes `Even (2 * a + 1 + (2 * b + 1))`.
Expand: `(2a + 1) + (2b + 1) = 2a + 2b + 2`, whose half is `a + b + 1`. Give that witness (R4, or R7) and close
the equation with R6.

**R3 · `obtain ⟨m, rfl⟩ := h`** with `h : Odd n` changes the **context and the goal**: `n` and `h` leave the
context and every `n` in the goal becomes `2 * m + 1`. Placeholders:
`{α : Type} [Semiring α] (n : α) (P : α → Prop)`; `ℕ` and `ℤ` qualify.

| Before | After |
|---|---|
| `h : Odd n ⊢ P n` | `m : α ⊢ P (2 * m + 1)` |

**W2 · Odd `n` → even `n + 1`** over `ℕ` (R3, R4, R6). Witness: `2m + 2 = (m + 1) + (m + 1)`.

| Before | After `obtain ⟨m, rfl⟩ := h` | After `refine ⟨m + 1, ?_⟩` | After `ring` |
|---|---|---|---|
| `h : Odd n ⊢ Even (n + 1)` | `m : ℕ ⊢ Even (2 * m + 1 + 1)` | `⊢ 2 * m + 1 + 1 = m + 1 + (m + 1)` | no goals |

## Part 3 · `odd_square`

Statement: for `n : ℤ` with `h : Odd n`, `Odd (n ^ 2)`. Unpack and substitute `n := 2 * k + 1` (R3); the goal
becomes `Odd ((2 * k + 1) ^ 2)`. Expand: `(2k + 1)² = 4k² + 4k + 1 = 2 · (2k² + 2k) + 1`, so the witness is
`2k² + 2k` written in Lean syntax. Give it (R5, or R7) and close the equation with R6.

**R5 · `refine ⟨w, ?_⟩`** on `⊢ Odd a` changes the **goal** to the witness's equation. Placeholders:
`{α : Type} [Semiring α] (a w : α)`.

| Before | After |
|---|---|
| `⊢ Odd a` | `⊢ a = 2 * w + 1` |

**W3 · Odd `n` → odd `3 * n`** over `ℤ` (R3, R5, R6). Witness: `3(2m + 1) = 6m + 3 = 2(3m + 1) + 1`.

| Before | After `obtain ⟨m, rfl⟩ := h` | After `refine ⟨3 * m + 1, ?_⟩` | After `ring` |
|---|---|---|---|
| `h : Odd n ⊢ Odd (3 * n)` | `m : ℤ ⊢ Odd (3 * (2 * m + 1))` | `⊢ 3 * (2 * m + 1) = 2 * (3 * m + 1) + 1` | no goals |

**W4.** The same with R7: after `obtain ⟨m, rfl⟩ := h`, the goal `⊢ Odd (3 * (2 * m + 1))` is closed by
`exact ⟨3 * m + 1, by ring⟩`.

**W5.** A numeral has nothing to unpack: `Odd (7 : ℤ)` is `⟨3, by ring⟩`, since `7 = 2 * 3 + 1`.

---

## Traps

- `Even`'s witness is the **half**: `Even 6` needs `⟨3, _⟩` with `6 = 3 + 3`, not `⟨6, _⟩`. `Odd`'s witness is
  `m` in `2 * m + 1`.
- `Even n` is stated with `r + r`, not `2 * r`. After R4 the goal is `a = w + w`; `ring` does not care, but a
  hand-written `rw` would.
- `obtain ⟨r, rfl⟩ := h` only works when the side being replaced is a local variable (`h : Even m`). For
  `h : Even (m + 1)` there is no variable to substitute: use `obtain ⟨r, hr⟩ := h` (R1) instead.
- Unpacking two hypotheses: pick two different witness names (`⟨a, rfl⟩`, `⟨b, rfl⟩`). Reusing one name shadows
  the first witness, and the goal then prints `a✝`.
- `ring` never reads the context. Substitute first (the `rfl` pattern does it for you), then call `ring`.
- `ring` failing means the equation is false: the witness is wrong. Expand the left side by hand and halve.
- `even_iff_two_dvd : Even a ↔ 2 ∣ a` is Mathlib's bridge to divisibility (`2 ∣ a`: `2` divides `a`). This
  problem does not need it; the names on the `BANNED:` line would prove the theorems for you and are off limits.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| use `h : Even n`, keep `n` | `obtain ⟨r, hr⟩ := h` (gives `hr : n = r + r`) | R1 |
| use `h : Even n`, replace `n` by `r + r` | `obtain ⟨r, rfl⟩ := h` | R2 |
| use `h : Odd n`, replace `n` by `2 * m + 1` | `obtain ⟨m, rfl⟩ := h` | R3 |
| prove `Even a` with witness `w` | `refine ⟨w, ?_⟩`, goal `a = w + w` | R4 |
| prove `Odd a` with witness `w` | `refine ⟨w, ?_⟩`, goal `a = 2 * w + 1` | R5 |
| close the witness equation | `ring` | R6 |
| witness and equation at once | `exact ⟨w, by ring⟩` | R7 |
| find the witness | substitute, expand by hand, halve (`Even`) or take `(x - 1) / 2` (`Odd`) | W1–W3 |
| see the state | infoview (cursor after a tactic) | |
