# M083 · A probabilistic program: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `do` notation, `Bool` and `||`, `if … then … else`,
`rw`, `simp`, `show`. **New here:** Mathlib's probability mass functions `PMF`, the extended
non-negative reals `ℝ≥0∞`, infinite sums `∑'`, and the map `ENNReal.toReal : ℝ≥0∞ → ℝ`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ≥0∞ → Prop` or similar). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Fintype α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ≥0∞` (`ENNReal`) | the extended non-negative reals `[0, ∞]`. Probabilities live here. Needs `open scoped ENNReal` for the notation |
| `∞` | the top element of `ℝ≥0∞` (also written `⊤`) |
| `PMF α` | a probability mass function on `α`: a function `p : α → ℝ≥0∞` whose values sum to `1` |
| `p a`, `(p.bind f) b` | the probability that `p` (resp. `p.bind f`) yields `a` (resp. `b`). The PMF is applied like a function (a coercion `DFunLike.coe` you do not see) |
| `PMF.pure a` | the point mass at `a`: probability `1` at `a`, `0` elsewhere. `return x` in a `PMF` `do` block is `PMF.pure x` |
| `p.bind f` | "draw `a` from `p`, then run `f a`". `do let a ← p; rest` is `p.bind fun a => rest` |
| `PMF.uniformOfFintype α` | the uniform distribution on a finite nonempty type `α` |
| `Fintype.card α` | the number of elements of a finite type `α` |
| `∑' (a : α), g a` | the unconditional infinite sum (`tsum`) of `g` over all `a : α`. Over `Bool` it is just two terms (R3) |
| `↑2` | the natural number `2 : ℕ` cast into `ℝ≥0∞`; `simp` turns it into the literal `2` (R8) |
| `x⁻¹` | the inverse; in `ℝ≥0∞`, `0⁻¹ = ∞` and `∞⁻¹ = 0` |
| `x / y` | division, defined as `x * y⁻¹`; `3 / 4` in the statement is in `ℝ≥0∞` |
| `if true = (false \|\| true) then 1 else 0` | the indicator of the event: `1` if the returned `Bool` equals `true`, else `0` (from `PMF.pure_apply`, R4) |
| `x.toReal`, `ENNReal.toReal x` | `x` as a real number, with `∞.toReal = 0` (junk value). Hence the side goals `x ≠ ∞` |
| `a \|\| b` | Boolean or; `!a` is Boolean not |

---

## Part 1 · `twoFlips_true`

Statement: `twoFlips true = 3 / 4` in `ℝ≥0∞`. `twoFlips` draws `a` and `b` from the fair coin and
returns `a || b`, so the claim is $P(a \lor b) = \sum_{a,b} \tfrac12 \cdot \tfrac12 \cdot [a \lor b] = \tfrac34$.

### From a `do` block to probabilities

**R1 · `show T`** changes the **goal**: it replaces the goal by `T`, which must be equal to it by
unfolding definitions (definitional equality). Here it unfolds a defined program and its `do` block
into explicit `PMF.bind` / `PMF.pure`. Placeholders: `{α β : Type} (p : PMF α) (f : α → β) (b : β)`, with
`relabel p f` defined as `do let a ← p; return f a`.

| Before | After |
|---|---|
| `⊢ P ((relabel p f) b)` | `⊢ P ((p.bind fun a => PMF.pure (f a)) b)` |

**R2 · `PMF.bind_apply`** changes the **goal**. The lemma is
`(p.bind f) b = ∑' a, p a * (f a) b`: the law of total probability over the first draw.
Placeholders: `{α β : Type} (p : PMF α) (f : α → PMF β) (b : β)`.

| Before | After |
|---|---|
| `⊢ P ((p.bind f) b)` | `⊢ P (∑' (a : α), p a * (f a) b)` |

**R3 · `tsum_bool`** changes the **goal**. The lemma is `∑' i : Bool, f i = f false + f true`.
Placeholders: `{α : Type} [AddCommMonoid α] [TopologicalSpace α] (f : Bool → α)`: α has a commutative `+`
with `0` and a topology (needed to define `∑'`); `ℝ≥0∞`, `ℝ`, `ℂ` qualify.

| Before | After |
|---|---|
| `⊢ P (∑' (i : Bool), f i)` | `⊢ P (f false + f true)` |

**R4 · `PMF.pure_apply`** changes the **goal**. The lemma is `(PMF.pure a) a' = if a' = a then 1 else 0`.
Placeholders: `{α : Type} (a a' : α)`. The `if` decides `a' = a` classically; `simp` evaluates it for
concrete `Bool`s (R7).

| Before | After |
|---|---|
| `⊢ P ((PMF.pure a) a')` | `⊢ P (if a' = a then 1 else 0)` |

**R5 · `PMF.uniformOfFintype_apply`** changes the **goal**. The lemma is
`(PMF.uniformOfFintype α) a = (↑(Fintype.card α))⁻¹`. Placeholders: `{α : Type} [Fintype α] [Nonempty α] (a : α)`:
α is finite and has at least one element; `Bool` and `Fin n` (n > 0) qualify. Before using it, unfold
the coin's name with `simp only [coin]` (TACTIC_STATES, "Rewriting and simplifying").

| Before | After |
|---|---|
| `⊢ P ((PMF.uniformOfFintype α) a)` | `⊢ P (↑(Fintype.card α))⁻¹` |

**R6 · `Fintype.card_bool`** changes the **goal**. The lemma is `Fintype.card Bool = 2`.

| Before | After |
|---|---|
| `⊢ P (Fintype.card Bool)` | `⊢ P 2` |

Put R2–R6 and `coin` into one `simp only [...]`: it rewrites everywhere and repeats as needed, so all
three `bind`s, all four `pure`s and all coins are expanded in one step.

### Cleaning up

**R7 · `simp`** changes the **goal**: it computes `!false`, `false || true` and friends, decides `true = true` /
`true = false`, picks the branch of each `if`, and simplifies `x * 1`, `x * 0`, `+ 0`. Placeholders:
`(x : ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ P ((x * if true = !false then 1 else 0) + x * if true = !true then 1 else 0)` | `⊢ P x` |

**R8 · `Nat.cast_ofNat`** changes the **goal**: `↑2`, the natural number `2` cast into `ℝ≥0∞`, becomes the
literal `2 : ℝ≥0∞`. Statement: `(↑(OfNat.ofNat n) : R) = OfNat.ofNat n` for numerals `n ≥ 2`. `simp`
applies it by itself.

| Before | After |
|---|---|
| `⊢ P (↑2)⁻¹` | `⊢ P 2⁻¹` |

**R9 · `ENNReal.inv_two_add_inv_two`** changes the **goal**. The lemma is `2⁻¹ + 2⁻¹ = 1` in `ℝ≥0∞`. Use it
when `simp` leaves `2⁻¹ + 2⁻¹` inside a larger expression.

| Before | After |
|---|---|
| `⊢ P (2⁻¹ + 2⁻¹)` | `⊢ P 1` |

**R10 · `mul_one`** changes the **goal**. The lemma is `a * 1 = a`. Placeholders:
`{α : Type} [MulOneClass α] (a : α)` (α has `*` with unit `1`; every number type qualifies).

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

### Moving an equation from `ℝ≥0∞` to `ℝ`

`norm_num` does not evaluate `2⁻¹ * 2⁻¹ + 2⁻¹ = 3 / 4` in `ℝ≥0∞` (it is not a field: `∞` has no
additive inverse). Map both sides to `ℝ`, where it does.

**R11 · `rw [← ENNReal.toReal_eq_toReal_iff']`** changes the **goal list**. The lemma is
`x ≠ ∞ → y ≠ ∞ → (x.toReal = y.toReal ↔ x = y)`; right to left it turns `x = y` into an equation of real
numbers, and adds the two finiteness side goals. Write `rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]`
to close them on the spot. Placeholders: `(x y : ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ x = y` | `⊢ x.toReal = y.toReal`, `⊢ x ≠ ∞`, `⊢ y ≠ ∞` |

**R12 · `finiteness`** **closes** a goal `t ≠ ∞` when `t` is built from `+`, `*`, inverses of nonzero
numerals, `/` by nonzero numerals (as in `3 / 4`), and variables with a hypothesis `_ ≠ ∞`. Placeholders: `(a : ℝ≥0∞)`.

| Before | After |
|---|---|
| `ha : a ≠ ∞ ⊢ a * 2⁻¹ + 3⁻¹ ≠ ∞` | no goals |

**R13 · `ENNReal.toReal_add`** changes the **goal list**. The lemma is
`a ≠ ∞ → b ≠ ∞ → (a + b).toReal = a.toReal + b.toReal`, so the side goals `a ≠ ∞`, `b ≠ ∞` are added;
`(by finiteness)` twice closes them. Placeholders: `(a b : ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ P (a + b).toReal` | `⊢ P (a.toReal + b.toReal)`, `⊢ a ≠ ∞`, `⊢ b ≠ ∞` |

**R14 · `ENNReal.toReal_mul`** changes the **goal**: `(a * b).toReal = a.toReal * b.toReal`, no side
goal (`∞ * 0 = 0` makes it hold always). Placeholders: `(a b : ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ P (a * b).toReal` | `⊢ P (a.toReal * b.toReal)` |

**R15 · `ENNReal.toReal_inv`** changes the **goal**: `a⁻¹.toReal = a.toReal⁻¹`, no side goal.
Placeholders: `(a : ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ P a⁻¹.toReal` | `⊢ P a.toReal⁻¹` |

**R16 · `ENNReal.toReal_div`** changes the **goal**: `(a / b).toReal = a.toReal / b.toReal`, no side goal.
It is a `simp` lemma; the solution names it anyway, `simp [ENNReal.toReal_div]`, to make the step explicit. Placeholders: `(a b : ℝ≥0∞)`.

| Before | After |
|---|---|
| `⊢ P (a / b).toReal` | `⊢ P (a.toReal / b.toReal)` |

**R17 · `ENNReal.toReal_ofNat`** changes the **goal**: the real value of the numeral `3 : ℝ≥0∞` is the real
numeral `3`.

| Before | After |
|---|---|
| `⊢ P (ENNReal.toReal 3)` | `⊢ P 3` |

`simp [ENNReal.toReal_div]` applies R14–R17 together. The goal then *prints* exactly as before the move
(`2⁻¹ * 2⁻¹ + 2⁻¹ = 3 / 4`), but every number is now in `ℝ`: hover over `2` in the infoview to see the type.

**R18 · `norm_num`** **closes** a numeral identity in `ℝ` (inverses and `/` included).

| Before | After |
|---|---|
| `⊢ 2⁻¹ * 3⁻¹ + 3⁻¹ = 1 / 2` | no goals |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: one coin, negated.** `flipNot = do let a ← PMF.uniformOfFintype Bool; return (!a)`. R1, then
`simp only [R2–R6]`, then `simp` (R7, R8) closes it:

```lean-goal
⊢ flipNot true = 2⁻¹
⊢ ((PMF.uniformOfFintype Bool).bind fun a => PMF.pure !a) true = 2⁻¹
⊢ (((↑2)⁻¹ * if true = !false then 1 else 0) + (↑2)⁻¹ * if true = !true then 1 else 0) = 2⁻¹
```

**W2: a numeral identity moved to `ℝ`.** `4⁻¹ + 2⁻¹ = 3 / 4` in `ℝ≥0∞`: R11 with R12, R13 with R12,
`simp [ENNReal.toReal_div]` (R14–R17), then R18. The last line is in `ℝ`:

```lean-goal
⊢ 4⁻¹ + 2⁻¹ = 3 / 4
⊢ (4⁻¹ + 2⁻¹).toReal = (3 / 4).toReal
⊢ 4⁻¹.toReal + 2⁻¹.toReal = (3 / 4).toReal
```

---

## Traps

- `norm_num` cannot evaluate `2⁻¹ * 2⁻¹ + 2⁻¹ = 3 / 4` in `ℝ≥0∞`. Move the equation to `ℝ` first (R11–R17).
- `x.toReal` is `0` for `x = ∞`, so moving to `ℝ` is only sound for finite sides: that is what the side
  goals `x ≠ ∞` of R11 and R13 say. Use the primed `ENNReal.toReal_eq_toReal_iff'`; the unprimed one has a
  disjunction on its right side.
- `show` only accepts a goal that is definitionally equal to the current one. Write the binds in the
  order of the `do` block: outer `let a ← …` is the outer `bind`.
- `simp` cannot see inside `twoFlips` or `coin` until they are unfolded: `show` does `twoFlips`, and
  `coin` goes into the `simp only` list.
- `rw [ENNReal.inv_two_add_inv_two]` needs `2⁻¹ + 2⁻¹` literally; `simp` leaves it as `2⁻¹ * (2⁻¹ + 2⁻¹)`,
  so the rewrite produces `2⁻¹ * 1` and `mul_one` (R10) finishes the clean-up.
- After moving to `ℝ` the goal prints the same; the numbers changed type, not shape.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `do` block → explicit binds | `show (p.bind fun a => …) b = c` | R1 |
| expand `bind`, `pure`, uniform, sum over `Bool` | `simp only [PMF.bind_apply, tsum_bool, PMF.pure_apply, coin, PMF.uniformOfFintype_apply, Fintype.card_bool]` | R2–R6 |
| evaluate the `if`s, `↑2 → 2` | `simp` | R7, R8 |
| `2⁻¹ + 2⁻¹ → 1`, `a * 1 → a` | `rw [ENNReal.inv_two_add_inv_two, mul_one]` | R9, R10 |
| `x = y` in `ℝ≥0∞` → in `ℝ` | `rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]` | R11, R12 |
| `(a + b).toReal` | `rw [ENNReal.toReal_add (by finiteness) (by finiteness)]` | R13, R12 |
| push `toReal` through `*`, `⁻¹`, `/`, numerals | `simp [ENNReal.toReal_div]` | R14–R17 |
| numeral identity in `ℝ` | `norm_num` | R18 |
| see the state | infoview | |
