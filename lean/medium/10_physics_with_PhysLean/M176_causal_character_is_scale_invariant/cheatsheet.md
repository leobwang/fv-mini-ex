# M176 · Causal character is scale invariant: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's Lorentz vectors
`Lorentz.Vector d`, the Minkowski product `⟪p, q⟫ₘ` as a bilinear map, the classification
`causalCharacter`; Mathlib's `map_smul` / `smul_apply` for linear maps, sign lemmas for products
(`mul_pos`, `mul_ne_zero`, `pos_of_mul_pos_right`), and the closer `positivity`; deciding `if`s with
`by_cases` + `simp`.

The physics: in `d` space dimensions a 4-vector `p` has a time component `p⁰` and space components
`p¹ … pᵈ`. The Minkowski product is `⟪p, q⟫ₘ = p⁰ q⁰ − ∑ᵢ pⁱ qⁱ` (signature `(+, −, …, −)`), so
`⟪p, p⟫ₘ` is the squared "length". `p` is *lightlike* if `⟪p, p⟫ₘ = 0`, *timelike* if `⟪p, p⟫ₘ > 0`,
*spacelike* if `⟪p, p⟫ₘ < 0`. Bilinearity gives `⟪c • p, c • p⟫ₘ = c² ⟪p, p⟫ₘ`, and `c² > 0` for
`c ≠ 0`, so the sign, hence the class, is unchanged.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`, `P : α → Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal. `G : Prop` is a goal the entry does not touch.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Mul α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Lorentz.Vector d` | a 4-vector: a function `Fin 1 ⊕ Fin d → ℝ` (one time + `d` space components); a real vector space, so `c • p` (scalar times vector) is defined |
| `c • p` | `c : ℝ` times the vector `p`, componentwise. Between two reals, `a • b` is just `a * b` (R3) |
| `⟪p, q⟫ₘ` | Minkowski product `p⁰ q⁰ − ∑ᵢ pⁱ qⁱ`. Scoped notation: it needs `open Lorentz Vector` |
| `(minkowskiProduct p) q` | how the infoview prints `⟪p, q⟫ₘ`. `minkowskiProduct : Vector d →L[ℝ] Vector d →L[ℝ] ℝ` is linear in `p` and returns a linear map, which is applied to `q` (`→L[ℝ]`: continuous ℝ-linear map) |
| `c • minkowskiProduct p` | the linear map `q ↦ c * ⟪p, q⟫ₘ` (a scaled linear map, R1, R2) |
| `CausalCharacter` | physlib's three-valued type with constructors `.timeLike`, `.lightLike`, `.spaceLike` |
| `p.causalCharacter` | how the infoview prints `causalCharacter p` (dot notation) |
| `have v0 := e; body` | inside a goal: `body` with the local name `v0` for `e`. Not a hypothesis; `simp` substitutes `e` for `v0` |
| `if Q then x else y` | `x` when `Q` holds, `y` otherwise (`Q` must be decidable; on `ℝ` it is, classically) |
| `¬a = 0` | `a ≠ 0` (the same proposition, printed two ways) |
| `h.ne'`, `h.le` | dot notation: for `h : 0 < a`, `LT.lt.ne' h : a ≠ 0` and `LT.lt.le h : 0 ≤ a` (R10, R13) |
| `case pos`, `case neg` | the two goals after `by_cases`: the condition holds / fails |

---

## Part 1 · `causalCharacter_smul`

Statement: for `c : ℝ` with `c ≠ 0` and `p : Lorentz.Vector d`, `causalCharacter (c • p) = causalCharacter p`.
Route: compute `⟪c • p, c • p⟫ₘ = c ^ 2 * ⟪p, p⟫ₘ` and `0 < c ^ 2` first, open both sides into their
`if`s, rewrite, then split on `⟪p, p⟫ₘ = 0` and on `0 < ⟪p, p⟫ₘ` and let `simp` pick the branches.

### Pulling the scalar out

**R1 · `rw [map_smul]`** changes the **goal**. The lemma is `map_smul : f (c • x) = c • f x` for any linear
map `f`. `minkowskiProduct` is linear and so is each `minkowskiProduct p`, so it works in both slots. In the
first slot the scalar lands on the map (then R2); in the second it lands on the number. Placeholders:
`{d : ℕ} (c : ℝ) (p q : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `⊢ P ((minkowskiProduct (c • p)) q)` | `⊢ P ((c • minkowskiProduct p) q)` |
| `⊢ P ((minkowskiProduct p) (c • q))` | `⊢ P (c • (minkowskiProduct p) q)` |

**R2 · `rw [smul_apply]`** changes the **goal**. The lemma is `smul_apply : (c • f) x = c • f x`: a scaled
map applied to `x` is the scaled value. (`ContinuousLinearMap.smul_apply` is the deprecated name and
gives a warning.) Placeholders: as in R1.

| Before | After |
|---|---|
| `⊢ P ((c • minkowskiProduct p) q)` | `⊢ P (c • (minkowskiProduct p) q)` |

**R3 · `rw [smul_eq_mul]`** changes the **goal**. The lemma is `smul_eq_mul : a • b = a * b` when `a, b`
live in the same type. Placeholders: `{α : Type} [Mul α] (a b : α)`; `ℝ` qualifies.

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**R4 · `ring`** **closes** a commutative-ring identity. `simp [map_smul]` applies R1–R3 by itself but
leaves nested products such as `c * (c * x)`, never `c ^ 2`; `ring` matches them. Placeholders: `(c x : ℝ)`.

| Before | After |
|---|---|
| `⊢ c * (c * x) = c ^ 2 * x` | no goals |

**R5 · `positivity`** **closes** a goal `0 < e` or `0 ≤ e` by looking at the shape of `e` (squares, sums of
positives, …). For `0 < c ^ 2` it needs `c ≠ 0` in the context. Placeholders: `(c : ℝ) (hc : c ≠ 0)`.

| Before | After |
|---|---|
| `hc : c ≠ 0 ⊢ 0 < c ^ 2` | no goals |

### Opening `causalCharacter`

**R6 · `unfold causalCharacter`** changes the **goal**: every `causalCharacter p` becomes its body,
physlib's definition
`have v0 := ⟪p, p⟫ₘ; if v0 = 0 then .lightLike else if 0 < v0 then .timeLike else .spaceLike`.
Placeholders: `{d : ℕ} (p : Lorentz.Vector d) (P : CausalCharacter → Prop)`.

| Before | After |
|---|---|
| `⊢ P p.causalCharacter` | `⊢ P (have v0 := (minkowskiProduct p) p; if v0 = 0 then CausalCharacter.lightLike else if 0 < v0 then CausalCharacter.timeLike else CausalCharacter.spaceLike)` |

**R7 · `rw [hab]` inside a `have … ; if …`** changes the **goal**: the bound value is an ordinary subterm,
so `rw` replaces it. This is how `rw [h]` with `h : ⟪c • p, c • p⟫ₘ = c ^ 2 * ⟪p, p⟫ₘ` reaches the
left-hand side after R6. Placeholders: `{α : Type} (a b : ℝ) (x y : α) (hab : a = b)`.

| Before | After |
|---|---|
| `hab : a = b ⊢ P (have v := a; if v = 0 then x else y)` | `⊢ P (have v := b; if v = 0 then x else y)` |

### Deciding the `if`s

**R8 · `by_cases h0 : Q`** changes the **goal list and the context**: one goal becomes two, the first with
`h0 : Q` (`case pos`), the second with `h0 : ¬Q` (`case neg`). Placeholders: `(a : ℝ) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h0 : a = 0 ⊢ G`, `h0 : ¬a = 0 ⊢ G` |

**R9 · `simp [h0]` on an `if`** changes the **goal**: with `h0 : Q` it takes the `then` branch (`if_pos`),
with `h0 : ¬Q` the `else` branch (`if_neg`). It also substitutes a `have v := e` first. Give `simp` the
condition **exactly** as it appears in the `if` (or its negation). Placeholders:
`{α : Type} (a : ℝ) (x y : α)`.

| Before | After |
|---|---|
| `h0 : a = 0 ⊢ P (if a = 0 then x else y)` | `⊢ P x` |
| `h0 : ¬a = 0 ⊢ P (if a = 0 then x else y)` | `⊢ P y` |

In the exercise both sides of `=` are such `if`s; once every condition is decided, both sides are the same
constructor (e.g. `CausalCharacter.timeLike = CausalCharacter.timeLike`) and `simp` closes the goal.

### Sign facts about products

All of these are used as terms inside `have`, so they add to the **context**. They hold in any ordered
field; the entries state them on `ℝ`.

**R10 · `h.ne'`** (`LT.lt.ne' : b < a → a ≠ b`): from `h : 0 < a`, get `a ≠ 0`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `h : 0 < a ⊢ G` | `ha : a ≠ 0 ⊢ G` |

**R11 · `mul_ne_zero`** (`a ≠ 0 → b ≠ 0 → a * b ≠ 0`). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `ha : a ≠ 0, hb : b ≠ 0 ⊢ G` | `hab : a * b ≠ 0 ⊢ G` |

**R12 · `mul_pos`** (`0 < a → 0 < b → 0 < a * b`). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `ha : 0 < a, hb : 0 < b ⊢ G` | `hab : 0 < a * b ⊢ G` |

**R13 · `h.le`** (`LT.lt.le : a < b → a ≤ b`): from `h : 0 < a`, get `0 ≤ a`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `h : 0 < a ⊢ G` | `ha : 0 ≤ a ⊢ G` |

**R14 · `pos_of_mul_pos_right`** (`0 < a * b → 0 ≤ a → 0 < b`): a positive product with a nonnegative
left factor has a positive right factor. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `hab : 0 < a * b, ha : 0 ≤ a ⊢ G` | `hb : 0 < b ⊢ G` |

**R15 · proving `¬Q`** changes the **goal and the context**. `¬Q` is by definition `Q → False`, so a proof
is a function: `fun h' => …` in term mode, or `intro h'` in tactic mode. Use it to get `¬0 < c ^ 2 * x`
from `¬0 < x`: assume the product is positive and derive `0 < x` with R14. Placeholders: `(Q R : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬Q` | `h' : Q ⊢ False` |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: `simp [map_smul]` on two scalars.** `simp` runs R1–R3 and stops at nested products; `ring` (R4)
finishes:

```lean-goal
⊢ (minkowskiProduct (2 • p)) (3 • q) = 6 * (minkowskiProduct p) q
⊢ 3 * (2 * (minkowskiProduct p) q) = 6 * (minkowskiProduct p) q
```

**W2: decide both conditions up front.** `sign3 x = if x = 0 then 0 else if 0 < x then 1 else -1`.
After `unfold sign3` (R6) prove `x ^ 2 + 1 ≠ 0` and `0 < x ^ 2 + 1` with `positivity` (R5); one
`simp [h1, h2]` (R9) then picks the branch:

```lean-goal
⊢ sign3 (x ^ 2 + 1) = 1
⊢ (if x ^ 2 + 1 = 0 then 0 else if 0 < x ^ 2 + 1 then 1 else -1) = 1
```

**W3: nested `by_cases` (R8).** For `sign3 x ≠ 2`: split on `x = 0`; in the `¬x = 0` branch split again on
`0 < x`; each of the three goals falls to `simp [h0]` / `simp [h0, hp]` (R9):

```lean-goal
⊢ (if x = 0 then 0 else if 0 < x then 1 else -1) ≠ 2
```

**W4: a negative fact (R15 + R14).** `fun h' => hp (pos_of_mul_pos_right h' (by norm_num))` proves
`¬0 < 3 * x` from `hp : ¬0 < x`; the `(by norm_num)` proves `0 ≤ 3`.

---

## Traps

- `rw [h]` with `h : ⟪c • p, c • p⟫ₘ = …` fails before `unfold causalCharacter`: the product is hidden inside
  the definition. Unfold first (R6), then rewrite (R7).
- `simp [map_smul]` leaves `c * (c * ⟪p, p⟫ₘ)`, not `c ^ 2 * ⟪p, p⟫ₘ`. End that `have` with `ring` (R4).
- After the rewrite the conditions read `c ^ 2 * ⟪p, p⟫ₘ = 0` and `0 < c ^ 2 * ⟪p, p⟫ₘ`. `h0 : ¬⟪p, p⟫ₘ = 0`
  alone does not decide them: give `simp` facts about the **product** (R11, R12, R15), stated with the
  same text.
- Symptom of a missing product fact: `simp [h0, hp]` (without `hne`) does not fail outright but leaves a
  left-hand `if c = 0 then … else …`, or the leftover goal `¬c = 0`. `simp` split the condition
  `c ^ 2 * ⟪p, p⟫ₘ = 0` with Mathlib's `mul_eq_zero` (`a * b = 0 ↔ a = 0 ∨ b = 0`) and `h0` killed one
  side. Add `hne` (R11) to the `simp` call (adding `hc` also works).
- The `have v0 := …` in the unfolded goal is not a hypothesis: `intro v0` fails. `simp` removes it.
- `positivity` proves `0 < c ^ 2` only if `c ≠ 0` is in the context (here `hc`); without it, only `0 ≤ c ^ 2`.
- `ContinuousLinearMap.smul_apply` is deprecated (a warning); write `smul_apply`.
- `hp : ¬0 < x` is not the same as `x < 0`; the spacelike case never needs `x < 0`, only `¬0 < …`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| pull a scalar out of `⟪·, ·⟫ₘ` | `simp [map_smul]` (or `rw [map_smul, smul_apply, smul_eq_mul]`) | R1–R3 |
| `c * (c * x) = c ^ 2 * x` | `ring` | R4 |
| `0 < c ^ 2` from `c ≠ 0` | `positivity` | R5 |
| see the `if`s of a definition | `unfold causalCharacter` | R6 |
| rewrite inside the unfolded goal | `rw [h]` | R7 |
| split on a condition | `by_cases h0 : x = 0` | R8 |
| pick an `if` branch | `simp [h0, hp, …]` | R9 |
| `0 < a → a ≠ 0` / `0 < a → 0 ≤ a` | `h.ne'` / `h.le` | R10, R13 |
| `a * b ≠ 0` | `mul_ne_zero ha hb` | R11 |
| `0 < a * b` | `mul_pos ha hb` | R12 |
| `0 < b` from `0 < a * b`, `0 ≤ a` | `pos_of_mul_pos_right hab ha` | R14 |
| prove `¬Q` | `fun h' => …` / `intro h'` | R15 |
