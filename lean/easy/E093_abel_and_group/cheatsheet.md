# E093 · abel and group: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `calc` (E020) and `rw` (E009).
**New here:** Mathlib's algebraic type classes `AddCommGroup` and `Group`, the scalar multiple `n • a`,
and the two normalising tactics `abel` (additive, commutative) and `group` (multiplicative, possibly
noncommutative).

## How to read an entry

Each entry is one tactic. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : G → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{G : Type}` is any type. A bracket such as `[Group G]` is a
  requirement on `G` (a *type class*): `G` must come with the operations and laws the class names. Each entry
  says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `[AddCommGroup G]`, `inst✝ : AddCommGroup G` | `G` is an abelian group written additively: `+` associative and commutative, `0`, `-a`, `a - b = a + -b`. `inst✝` is the unnamed instance hypothesis |
| `[Group G]` | `G` is a group written multiplicatively: `*` associative (not necessarily commutative), `1`, `a⁻¹` with `a⁻¹ * a = 1` |
| `n • a` (`n : ℕ`) | `a + ⋯ + a` with `n` copies ("nsmul", natural-number scalar multiple; `•` is typed `\smul`). In `2 • a` the `2` is a `ℕ` |
| `2 • a + -1 • b` after `abel_nf` | the same with **integer** coefficients (`ℤ`, "zsmul"); it prints exactly like the `ℕ` version (Traps) |
| `a⁻¹` | the inverse of `a` (typed `\inv`) |
| `a ^ (-1)` | an integer power ("zpow"); `group` rewrites `a⁻¹` into this form, and you see it when `group` fails |
| `x * y * z` | `(x * y) * z`: `*` and `+` group to the left |
| `case calc_1` | the goal for the first step of a `calc` whose proof is `?_` |

---

## Part 1 · `abel1`, `abel2`, `abel3`

Statements: three identities in an additive commutative group `G` (with `a b c : G`), one with only `+`, `-`,
two with numeral multiples `2 • a`, `3 • (a + b)`. Each is closed by one tactic.

**R1 · `abel`** **closes** the goal: it puts both sides in a normal form (a sum `k₁ • x₁ + ⋯ + kₘ • xₘ` of
atoms `xᵢ` with integer coefficients `kᵢ`) and compares. Placeholders: `{G : Type} [AddCommGroup G] (a b : G)`;
`ℤ`, `ℝ`, `ℂ` and vectors `Fin n → ℝ` meet `[AddCommGroup G]`, `ℕ` does not.

| Before | After |
|---|---|
| `⊢ a + b - a = b` | no goals |

**R2 · `abel` with numeral multiples** **closes** the goal: a numeral `n` in `n • x` is a known coefficient,
so `n • (a + b)` is expanded to `n • a + n • b` and like terms are collected. Placeholders as in R1.

| Before | After |
|---|---|
| `⊢ 2 • (a + b) - a = a + 2 • b` | no goals |

**R3 · `abel_nf`** changes the **goal**: it rewrites every additive expression into `abel`'s normal form and
stops. Use it when `abel` fails, to see the two sides `abel` could not match. `abel` itself suggests it in its
failure message (`Try this: [apply] abel_nf`, shown next to the unsolved goal, which is already in normal form). Placeholders: `{G : Type} [AddCommGroup G] (a b : G) (P : G → Prop)`.

| Before | After |
|---|---|
| `⊢ P (a - b + a)` | `⊢ P (2 • a + -1 • b)` |

---

## Part 2 · `group1`, `group2`

Statements: two identities in a group `G` (with `a b : G`) involving the inverse of a product. Each is closed by
one tactic.

**R4 · `group`** **closes** the goal: it normalises products of atoms and their integer powers (`a⁻¹ = a ^ (-1)`),
cancels neighbours `x * x⁻¹`, and compares. It does not use commutativity, so it is valid in every group.
Placeholders: `{G : Type} [Group G] (a b : G)`. Permutations `Equiv.Perm α`, invertible matrices `GL n ℝ`, and the units `ℝˣ` (nonzero reals
under `*`) meet `[Group G]`; `ℝ` itself does not (`0` has no inverse).

| Before | After |
|---|---|
| `⊢ a * b * b⁻¹ = a` | no goals |

**R5 · `group` with the inverse of a product** **closes** the goal. `group` knows that inversion reverses the
order, $(xy)^{-1} = y^{-1}x^{-1}$; you never name that lemma. Placeholders as in R4.

| Before | After |
|---|---|
| `⊢ (a * b⁻¹)⁻¹ = b * a⁻¹` | no goals |

---

## Part 3 · `group3`

Statement: in a group, if `h : a * b = 1` then `b = a⁻¹`. `group` alone fails: it ignores `h` and is left with
`⊢ b = a ^ (-1)`. Pass through a middle term in which `a * b` appears literally, rewrite with `h`, and let
`group` finish each step.

**R6 · `calc` with `?_` steps** changes the **goal list**: one goal `x = z` becomes one goal per step. In the
exercise you give each step its proof inline (`:= by group`, `:= by rw [h]; group`); the `?_` form only shows
which goal each step proof faces. Placeholders: `{G : Type} [Group G] (x y z : G)`. The first step starts with
the goal's left side, the last ends with its right side, and each later step starts with `_`.

| Before | After |
|---|---|
| `h₁ : x = y, h₂ : y = z ⊢ x = z` | `⊢ x = y`, `⊢ y = z` |

**R7 · `rw [h]` on a bracketed product** changes the **goal**: with `h : a * b = 1`, the subterm `a * b`
becomes `1`. It must appear *as a subterm*: `c * a * b` is `(c * a) * b`, which has no `a * b` in it, so `rw`
fails there. Write the brackets yourself. Placeholders:
`{G : Type} [Group G] (a b c : G) (h : a * b = 1) (P : G → Prop)`. Afterwards `c * 1 = c` is an R4 goal.

| Before | After |
|---|---|
| `h : a * b = 1 ⊢ P (c * (a * b))` | `⊢ P (c * 1)` |

### Worked combinations (W1–W3, on statements that are not the exercise's)

**W1: additive, through a hypothesis.** `h : a + b = c` gives `c - b = a`: the middle term `(a + b) - b` turns
the goal's `c` into something `abel` can cancel (R6, R7, R1).

```lean-goal
⊢ c - b = a
```

**W2: noncommutative, with a commutation fact.** `h : a * b = b * a` gives `a * b * a⁻¹ = b`. Here the left
side already *starts with* `a * b`, so `rw [h]` works without new brackets; then `group` cancels `a * a⁻¹`
(R6, R7, R4).

```lean-goal
⊢ a * b * a⁻¹ = b
```

**W3: left cancellation.** `h : a * c = a * d` gives `c = d`. The goal contains no `a * c`, so the first step
inserts it with a pure group identity (`c = a⁻¹ * (a * c)`, by `group`), the second rewrites with `h`, the third
cancels again with `group` (R6, R4, R7, R4). This is the shape of Part 3.

```lean-goal
⊢ c = d
```

---

## Traps

- `abel` and `group` **ignore hypotheses**. Rewrite with `h` first (inside a `calc` step), then normalise.
- `abel` needs a numeral in `n • x`. With a variable `n : ℕ` it fails on `n • (a + b) = n • a + n • b` with
  ``error: `abel_nf` made no progress on the goal``: it treats `n • (a + b)` as an opaque atom.
- `ring` needs a ring (a multiplication *and* an addition). In a bare `AddCommGroup` or `Group` it does not
  apply; use `abel` or `group`.
- `abel` is for commutative `+`. A `Group` is written with `*` and may be noncommutative: use `group`, which never
  swaps `a * b` into `b * a`. `group` cannot prove `a * b = b * a`, which is false in general.
- After `abel_nf`, `2 • a` has a `ℤ` coefficient even though it prints like the `ℕ` one; `exact h` with
  `h : P (2 • a)` (a `ℕ` multiple) then fails with a type mismatch `P ((2 : ℕ) • a)` vs `P ((2 : ℤ) • a)`.
  Use `abel_nf` only to look, and close with `abel`.
- `rw [h]` with `h : a * b = 1` fails on `c * a * b` ("did not find an occurrence of the pattern"): brackets
  matter (R7).
- When `group` fails, the leftover goal is written with `a ^ (-1)` instead of `a⁻¹`. That is the same element.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| identity with `+`, `-`, `0` in an `AddCommGroup` | `abel` | R1 |
| identity with numeral multiples `n • x` | `abel` | R2 |
| see what `abel` is stuck on | `abel_nf` | R3 |
| identity with `*`, `⁻¹`, `1` in a `Group` | `group` | R4 |
| inverse of a product, $(xy)^{-1} = y^{-1}x^{-1}$ | `group` | R5 |
| use a hypothesis: pass through a middle term | `calc x = y := by … _ = z := by …` | R6 |
| `rw [h]` with `h : a * b = 1` | bracket the term as `c * (a * b)` first | R7 |
| insert a pure identity, e.g. `b = a⁻¹ * (a * b)` | a `calc` step `:= by group` | R6, R4 |
| see the state | infoview | |
