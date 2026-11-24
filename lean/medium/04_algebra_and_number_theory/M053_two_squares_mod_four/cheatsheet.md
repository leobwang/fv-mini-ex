# M053 · Sums of two squares mod 4: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's `ZMod n` (the integers mod `n`
as a finite ring), the cast `ℤ → ZMod n` and the lemma `ZMod.intCast_mod` that links it to `%`; the
tactics `decide` (on a finite type), `push_cast`, `generalize`, and `revert`.

The idea: $a^2 + b^2 \bmod 4$ depends only on $a \bmod 4$ and $b \bmod 4$. Move the hypothesis from `ℤ`
(infinite, `decide` cannot help) into `ZMod 4` (four elements, `decide` checks them all).

## How to read an entry

Each entry is one tactic or one lemma (used in `have` or inside `push_cast`). It says what changes
(**goal**, **context**, or **goal list**), gives the lemma's statement, lists the placeholders with their
types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`, `P : ℤ → Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal. `Q` plays the same role for a hypothesis.
- `G : Prop` is an arbitrary goal; a hypothesis `g : … → G` is there only to finish the example. Such
  entries show the **context** gaining a fact.
- Placeholders are written as Lean binders. `{α : Type}` is any type; a bracket such as `[CommRing R]` is a
  requirement on `R` (a *type class*: here, `R` has `+`, `*`, `-`, `0`, `1` with the usual commutative-ring
  laws; `ℤ`, `ℚ`, `ℝ`, `ℂ`, `ZMod n` qualify).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ZMod 4` | the integers mod 4, a commutative ring with the four elements `0, 1, 2, 3`; `3 + 1 = 0` there. For `n > 0`, `ZMod n` is built on `Fin n`, so it is finite and `decide` can run through it |
| `ℤ`, `a % 4` | the integers; `%` on `ℤ` is the remainder, in `0, 1, 2, 3` when the modulus is `4` (`-1 % 4 = 3`) |
| `↑a` with `a : ℤ` in a `ZMod 4` statement | `Int.cast a`, the residue class of `a` in `ZMod 4`; Lean prints every cast as `↑` |
| `↑4` inside `a % ↑4` | the **natural number** `4` cast to `ℤ` (`Nat.cast`); it comes from `ZMod.intCast_mod`, whose modulus is a `ℕ` (R4). It is not the same text as the `ℤ`-numeral `4` (R6) |
| `↑((a ^ 2 + b ^ 2) % ↑4)` | the outer `↑` is `ℤ → ZMod 4`, the inner one `ℕ → ℤ` |
| `↑2` vs `2` in `ZMod 5` | the integer `2` cast into `ZMod 5` vs the `ZMod 5` numeral `2`; equal, but different text until `push_cast` (W3) |
| `a ≠ b` | `¬ (a = b)`, defined as `a = b → False` (R3) |
| `∀ (x y : ZMod 4), Q x y → False` | for all residues `x`, `y`, `Q x y` is impossible |
| `inst✝ : CommRing R` | an anonymous type-class hypothesis from a `[…]` binder |

---

## Part 1 · `sq_mod_four`

Statement: for every `x : ZMod 4`, `x ^ 2 = 0 ∨ x ^ 2 = 1`. In words: every square is `0` or `1` mod 4
($0^2 = 0$, $1^2 = 1$, $2^2 = 4 = 0$, $3^2 = 9 = 1$). Four cases, so let Lean check them.

**R1 · `revert x`** changes the **context and the goal**: `x` leaves the context and the goal becomes a
statement about every `x`. It is the inverse of `intro x`. Placeholders: `{α : Type} (P : α → Prop) (x : α)`.

| Before | After |
|---|---|
| `x : α ⊢ P x` | `⊢ ∀ (x : α), P x` |

**R2 · `decide`** changes the **goal list**: it closes the goal by evaluating it to `true`. It needs
(a) a goal with no variables from the context and (b) a `Decidable` instance (an algorithm that computes
the truth value), which Lean has for `=` on `ZMod n`, for `∨ ∧ ¬ →`, and for `∀ x : ZMod n, …` with `n`
a numeral `> 0` (it tries all `n` values). Placeholders: none; the example is `∀ x : ZMod 3, x ^ 3 = x`.
With `x : ZMod 4` still in the context, it fails with `Expected type must not contain free variables`:
apply R1 first.

| Before | After |
|---|---|
| `⊢ ∀ (x : ZMod 3), x ^ 3 = x` | no goals |

---

## Part 2 · `two_squares_ne_three`

Statement: for all integers `a b`, `(a ^ 2 + b ^ 2) % 4 ≠ 3`. A `≠` goal is an implication into `False`;
assume `h : (a ^ 2 + b ^ 2) % 4 = 3`, transport `h` into `ZMod 4`, then forget `a`, `b` and decide.
Part 1 is not needed: `decide` covers all 16 pairs `(x, y)` at once.

### Into `ZMod 4`

**R3 · `intro h`** on a `≠` goal changes the **goal and the context**: `a ≠ b` unfolds to `a = b → False`,
so `intro` adds `h : a = b` and leaves `False`. Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ a ≠ b` | `h : a = b ⊢ False` |

**R4 · `have h1 := ZMod.intCast_mod a n`** changes the **context**. The lemma is
`ZMod.intCast_mod : ∀ (a : ℤ) (b : ℕ), ((a % ↑b : ℤ) : ZMod b) = (a : ZMod b)`: in `ZMod b` an integer
equals its remainder mod `b`. Placeholders: `(a : ℤ) (n : ℕ)`. Apply it to the whole integer expression
whose remainder `h` talks about, and to the modulus as a numeral (`… 4`).

| Before | After |
|---|---|
| `⊢ G` | `h1 : ↑(a % ↑n) = ↑a ⊢ G` |

**R5 · `push_cast at h1`** changes the **context**: it moves casts `ℤ → R` inward through `+` and `^`,
using `Int.cast_add : ↑(a + b) = ↑a + ↑b` and `Int.cast_pow : ↑(a ^ k) = ↑a ^ k`. It cannot move a cast
through `%`: `ZMod n` has no `%` for it to land on, so `↑(… % …)` stays (R4 is the tool for that). Placeholders: `{R : Type} [CommRing R] (a b : ℤ) (k : ℕ)`.

| Before | After |
|---|---|
| `h1 : ↑(a ^ k + b) = 0 ⊢ G` | `h1 : ↑a ^ k + ↑b = 0 ⊢ G` |

**R6 · `push_cast` on a numeral cast** changes the **goal** (or, with `at h1`, the context): the natural
numeral `4` cast to `ℤ`, printed `↑4`, becomes the integer numeral `4`, by
`Nat.cast_ofNat : ((OfNat.ofNat n : ℕ) : R) = OfNat.ofNat n` (`OfNat.ofNat n` is how Lean stores a
numeral literal `n` of a given type, so the lemma says: the `ℕ`-literal cast to `R` is the `R`-literal). This is what lets `h`, which says `% 4`,
match the `% ↑4` from R4. Placeholders: `(a : ℤ) (P : ℤ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (a % ↑4)` | `⊢ P (a % 4)` |

**R7 · `push_cast [h] at h1`** changes the **context**: one call does R5 and R6 on `h1` and also rewrites
with `h` wherever its left side appears, then cleans up the cast of the result. Placeholders:
`(n : ℕ) (a r : ℤ) (h : a % ↑n = r)`. In the exercise, `h1 : ↑((a ^ 2 + b ^ 2) % ↑4) = ↑(a ^ 2 + b ^ 2)`
becomes an equation in `ZMod 4` between the numeral `3` and a sum of two squares of casts.

| Before | After |
|---|---|
| `h1 : ↑(a % ↑n) = ↑a ⊢ False` | `h1 : ↑r = ↑a ⊢ False` |

### Forget `a` and `b`, then decide

**R8 · `generalize (a : ZMod n) = x at h1`** changes the **context**: it adds a fresh `x : ZMod n` and
replaces every `↑a` in `h1` by `x`. Nothing remembers that `x = ↑a`, so what is left is a claim about an
arbitrary residue. Write the term with its type, `(a : ZMod 4)`, so it matches the cast in `h1`.
Placeholders: `(a : ℤ) (n : ℕ) (Q : ZMod n → Prop)`.

| Before | After |
|---|---|
| `h1 : Q ↑a ⊢ False` | `x : ZMod n, h1 : Q x ⊢ False` |

**R9 · `revert x y`** changes the **context and the goal**: `x`, `y` leave the context, and so does every
hypothesis that mentions them (`h1`); the goal becomes `∀ x y, (type of h1) → (old goal)`. Hypotheses that
do not mention `x`, `y` (here `a b h`) stay, and that is fine for `decide`: only the goal must be free of
variables. Placeholders: `{α : Type} (Q : α → α → Prop) (G : Prop) (x y : α)`.

| Before | After |
|---|---|
| `x y : α, h1 : Q x y ⊢ G` | `⊢ ∀ (x y : α), Q x y → G` |

Then **R2** `decide` closes `∀ (x y : ZMod 4), … → False` by checking all 16 pairs.

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: cubes mod 9.** R1 then R2.

| Before | After `revert x` |
|---|---|
| `x : ZMod 9 ⊢ x ^ 3 = 0 ∨ x ^ 3 = 1 ∨ x ^ 3 = 8` | `⊢ ∀ (x : ZMod 9), x ^ 3 = 0 ∨ x ^ 3 = 1 ∨ x ^ 3 = 8` |

**W2: no square is `2 mod 3`.** R3, R4, R7, R8, R9 (one variable), R2.

| Step | State |
|---|---|
| start | `⊢ a ^ 2 % 3 ≠ 2` |
| `intro h` | `h : a ^ 2 % 3 = 2 ⊢ False` |
| `have h1 := ZMod.intCast_mod (a ^ 2) 3` | `h1 : ↑(a ^ 2 % ↑3) = ↑(a ^ 2) ⊢ False` |
| `push_cast [h] at h1` | `h1 : 2 = ↑a ^ 2 ⊢ False` |
| `generalize (a : ZMod 3) = x at h1` | `x : ZMod 3, h1 : 2 = x ^ 2 ⊢ False` |
| `revert x` | `⊢ ∀ (x : ZMod 3), 2 = x ^ 2 → False` |
| `decide` | no goals |

**W3: R7 the long way.** `push_cast` (R6 turns `↑5` into `5`), then `rw [h]`, then `push_cast` again
(`↑2`, the integer `2` cast, becomes the `ZMod 5` numeral `2`).

| Step | State |
|---|---|
| `have h1 := ZMod.intCast_mod a 5` | `h1 : ↑(a % ↑5) = ↑a ⊢ 2 = ↑a` |
| `push_cast at h1` | `h1 : ↑(a % 5) = ↑a ⊢ 2 = ↑a` |
| `rw [h] at h1` | `h1 : ↑2 = ↑a ⊢ 2 = ↑a` |
| `push_cast at h1` | `h1 : 2 = ↑a ⊢ 2 = ↑a` |

---

## Traps

- `decide` on a goal that mentions a context variable fails with
  `Expected type must not contain free variables`. `revert` it first (R1, R9).
- `decide` cannot range over `ℤ` (infinite). Get into `ZMod 4` first; that is the whole point of R4–R8.
- `rw [h] at h1` right after R4 fails with `Did not find an occurrence of the pattern`: `h1` says `% ↑4`
  (a cast natural number), `h` says `% 4`. `push_cast` first (R6), or pass `h` to it (R7).
- `generalize (a : ZMod 4) = x` without `at h1` only looks in the goal (`False`), so `h1` keeps `↑a`.
- `decide +revert` reverts the context variables itself (the error message suggests it); this guide spells
  out `revert` so you see the goal `decide` checks.
- `revert x y` also takes `h1` along because `h1` mentions `x` and `y`; that is what puts `h1` into the
  goal for `decide`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| check every element of `ZMod n` | `revert x; decide` | R1, R2 |
| prove `a ≠ b` | `intro h` (goal `False`) | R3 |
| integer fact → `ZMod n` fact | `have h1 := ZMod.intCast_mod e n` | R4 |
| `↑(a + b)`, `↑(a ^ k)` → `↑a + ↑b`, `↑a ^ k` | `push_cast at h1` | R5 |
| `↑4` (cast `ℕ` numeral) → `4` | `push_cast` | R6 |
| push casts and rewrite with `h` | `push_cast [h] at h1` | R7 |
| forget that `x` was `↑a` | `generalize (a : ZMod n) = x at h1` | R8 |
| move variables and their hypotheses into the goal | `revert x y` | R9 |
| see the state | infoview | |
