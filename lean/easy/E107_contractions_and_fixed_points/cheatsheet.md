# E107 · Contractions and fixed points: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's nonnegative reals `NNReal` and their
cast into `ℝ`; distances `dist` and `edist`; absolute value `|·|`; the predicates `LipschitzWith`,
`ContractingWith` and `Function.IsFixedPt`; the tactic `linarith`.

Background. A map `f` on a metric space is **`K`-Lipschitz** when $d(f x, f y) \le K \, d(x, y)$ for all
`x y`, and a **contraction** when moreover $K < 1$. Banach's fixed-point theorem: a contraction on a complete
space (such as `ℝ`) has exactly one fixed point $x^\ast$ ($f x^\ast = x^\ast$), and the iteration
$x_{n+1} = f x_n$ converges to it from any start. Here `g x = x / 2 + 1`, `K = 1/2`, $x^\ast = 2$.

## How to read an entry

Each entry is one tactic or one lemma used with `simp only`/`rw`/`refine`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[PseudoMetricSpace α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it; `ℝ` meets all of them.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. A table
  cell must escape the absolute-value bars `|` as `\|`, so a state containing `|…|` is repeated below its
  table in a `lean-goal` block, which is the checked copy.

## Reading the goals

| You see | It means |
|---|---|
| `NNReal` (also written `ℝ≥0` after `open NNReal`) | the reals `≥ 0`, as the subtype `{r : ℝ // 0 ≤ r}`. Lipschitz constants live here, so the `1 / 2` in `LipschitzWith (1 / 2) …` is an `NNReal` |
| `↑K`, `↑(1 / 2)`, `↑1`, `↑2` | an `NNReal` cast into `ℝ` (the coercion `NNReal.toReal`). `↑(1 / 2)` is the cast of the `NNReal` number `1 / 2`, not yet the real `1 / 2` (R3–R5) |
| `dist x y` | the distance in a metric space, a real number `≥ 0`. On `ℝ` it is `\|x - y\|` (R2) |
| `edist x y` | the *extended* distance, a value in `ENNReal` = `[0, ∞]`. It appears only inside the definition of `LipschitzWith`; R1 replaces it by `dist` |
| `\|a\|` | the absolute value `abs a`, written with two plain `\|` characters |
| `LipschitzWith K f` | by definition `∀ x y, edist (f x) (f y) ≤ ↑K * edist x y` |
| `ContractingWith K f` | by definition `K < 1 ∧ LipschitzWith K f` (R10) |
| `Function.IsFixedPt f x` | by definition `f x = x` (R12) |
| `fun x => x / 2 + 1` | the map `g`; `/` on `ℝ` is real division |
| `PseudoMetricSpace α`, `EMetricSpace α` | type classes "`α` has a distance `dist`" / "`α` has an extended distance `edist`"; `ℝ` has both |
| `case refine_1`, `case refine_2` | the two goals left by `refine ⟨?_, ?_⟩` (R10) |

---

## Part 1 · `half_lipschitz`

Statement: `LipschitzWith (1 / 2) (fun x : ℝ => x / 2 + 1)`, i.e. $|g x - g y| \le \tfrac12 |x - y|$ for all
real `x y`. Go from `edist` to `dist` (R1), from `dist` to `|·|` (R2), turn the `NNReal` constant into a real
number (R3–R5), reshape the difference (R6–R8), and close the linear inequality (R9).

**R1 · `refine LipschitzWith.of_dist_le_mul fun x y => ?_`** changes the **goal and the context**. The lemma is
`LipschitzWith.of_dist_le_mul : (∀ x y, dist (f x) (f y) ≤ ↑K * dist x y) → LipschitzWith K f`: on a metric
space a `dist` bound suffices. `fun x y => ?_` introduces the two points and leaves the bound as the goal.
Placeholders: `{α β : Type} [PseudoMetricSpace α] [PseudoMetricSpace β] (K : NNReal) (f : α → β)`.

| Before | After |
|---|---|
| `⊢ LipschitzWith K f` | `x y : α ⊢ dist (f x) (f y) ≤ ↑K * dist x y` |

**R2 · `simp only [Real.dist_eq]`** changes the **goal**. The lemma is `Real.dist_eq : dist x y = |x - y|`
(for `x y : ℝ`). `simp only` rewrites **every** `dist`, each with its own arguments. Placeholders:
`(a b c d : ℝ) (P : ℝ → ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (dist a b) (dist c d)` | ⊢ P \|a - b\| \|c - d\| |

```lean-goal
⊢ P (dist a b) (dist c d)
⊢ P |a - b| |c - d|
```

**R3 · `simp only [NNReal.coe_div]`** changes the **goal**. The lemma is `NNReal.coe_div : ↑(r₁ / r₂) = ↑r₁ / ↑r₂`:
the cast moves inside `/`. Placeholders: `(r₁ r₂ : NNReal)`.

| Before | After |
|---|---|
| `⊢ P ↑(r₁ / r₂)` | `⊢ P (↑r₁ / ↑r₂)` |

**R4 · `simp only [NNReal.coe_one]`** changes the **goal**. The lemma is `NNReal.coe_one : ↑1 = 1`: the cast of
the `NNReal` one is the real one.

| Before | After |
|---|---|
| `⊢ P ↑1` | `⊢ P 1` |

**R5 · `simp only [NNReal.coe_ofNat]`** changes the **goal**. The lemma is `NNReal.coe_ofNat : ↑(OfNat.ofNat n) =
OfNat.ofNat n` for numerals `n ≥ 2`: the cast of an `NNReal` numeral is the same real numeral. (`0` and `1` are
separate lemmas: `NNReal.coe_zero`, R4.)

| Before | After |
|---|---|
| `⊢ P ↑2` | `⊢ P 2` |

R2–R5 go in one call: `simp only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]` (W1).

**R6 · `rw [show e₁ = e₂ by ring]`** changes the **goal**: `show e₁ = e₂ by ring` is a proof term of an identity
you state yourself, and `rw` uses it like a lemma. `e₁` must appear literally in the goal (copy it from the
infoview). Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a / c - b / c)` | `⊢ P ((a - b) / c)` |

**R7 · `rw [abs_div]`** changes the **goal**. The lemma is `abs_div : |a / b| = |a| / |b|`. Placeholders:
`{α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a b : α)`: an ordered field, such as `ℝ` or `ℚ`.

| Before | After |
|---|---|
| ⊢ P \|a / b\| | ⊢ P (\|a\| / \|b\|) |

```lean-goal
⊢ P |a / b|
⊢ P (|a| / |b|)
```

**R8 · `rw [abs_two]`** changes the **goal**. The lemma is `abs_two : |2| = 2`. Placeholders:
`{α : Type} [Ring α] [LinearOrder α] [IsOrderedRing α]`: an ordered ring, such as `ℤ`, `ℚ`, `ℝ`.

| Before | After |
|---|---|
| ⊢ P \|2\| | `⊢ P 2` |

```lean-goal
⊢ P |2|
⊢ P 2
```

**R9 · `linarith`** **closes** a goal that follows linearly from the hypotheses: `=`, `≤`, `<` between sums of
numeral multiples of unknowns. Anything that is not `+`, `-`, numeral `*` or `/` by a numeral counts as one
unknown, so `|x - y|` is an unknown `t` and `|x - y| / 3 ≤ 1 / 3 * |x - y|` is `t / 3 ≤ t / 3`. It does not see
through casts: `↑(1 / 2)` is another unknown (Traps).

---

## Part 2 · `half_contracting`

Statement: `ContractingWith (1 / 2) (fun x : ℝ => x / 2 + 1)`. By definition this is the pair
`1 / 2 < 1` (in `NNReal`) and the Lipschitz fact, which Part 1 already proved: use `half_lipschitz` by name.

**R10 · `ContractingWith K f` is `K < 1 ∧ LipschitzWith K f`** · `refine ⟨?_, ?_⟩` changes the **goal list**:
one goal becomes two (as for any `∧`, TACTIC_STATES "Structure"). As a term, write the pair `⟨hK, hf⟩`
directly after `:=`. Placeholders: `{α : Type} [EMetricSpace α] (K : NNReal) (f : α → α)`.

| Before | After |
|---|---|
| `⊢ ContractingWith K f` | `⊢ K < 1`, `⊢ LipschitzWith K f` |

**R11 · `norm_num`** **closes** a goal made of numerals, in `NNReal` as in `ℝ`: `(1 / 3 : NNReal) < 1`,
`-6 / 2 - 3 = -6`. Inside a term write `(by norm_num)`.

---

## Part 3 · `two_is_fixed`

Statement: `Function.IsFixedPt (fun x : ℝ => x / 2 + 1) 2`, i.e. `g 2 = 2`. Unfold the definition (R12); `simp`
also substitutes `2` into the `fun` (β-reduction), leaving a numeral equation for R11.

**R12 · `simp only [Function.IsFixedPt]`** changes the **goal**: it unfolds `Function.IsFixedPt f x` to `f x = x`.
`norm_num [Function.IsFixedPt]` unfolds and finishes in one call. Placeholders: `{α : Type} (f : α → α) (x : α)`.

| Before | After |
|---|---|
| `⊢ Function.IsFixedPt f x` | `⊢ f x = x` |

---

### Worked combinations (W1–W3, on the map `x ↦ x / 2 - 3`, not the exercise's)

**W1: Lipschitz with constant `1 / 2`.** R1, then R2–R5 in one `simp only`, then R6, R7 and R8, then R9:

```lean-goal
⊢ LipschitzWith (1 / 2) fun x => x / 2 - 3
⊢ dist (x / 2 - 3) (y / 2 - 3) ≤ ↑(1 / 2) * dist x y
⊢ |x / 2 - 3 - (y / 2 - 3)| ≤ 1 / 2 * |x - y|
⊢ |(x - y) / 2| ≤ 1 / 2 * |x - y|
⊢ |x - y| / 2 ≤ 1 / 2 * |x - y|
```

**W2: the contraction** is the term `⟨by norm_num, w_lipschitz⟩` (R10, R11), reusing W1 by its name.

**W3: `-6` is a fixed point.** R12 unfolds and β-reduces; R11 closes:

```lean-goal
⊢ Function.IsFixedPt (fun x => x / 2 - 3) (-6)
⊢ -6 / 2 - 3 = -6
```

---

## Traps

- `rw [Real.dist_eq]` rewrites only the first `dist` it meets (`rw` fixes the lemma's `x y` at the first match),
  so `dist x y` on the right survives. Use `simp only [Real.dist_eq]` (R2).
- The constant stays `↑(1 / 2)` (an `NNReal` cast) until R3–R5 run, and `linarith` treats it as an unknown and
  fails. Push the cast first.
- In R6, the left side must match the goal symbol for symbol: `x / 2 + 1 - (y / 2 + 1)`, with the parentheses
  Lean prints. Copy it from the infoview.
- `norm_num` alone makes no progress on `Function.IsFixedPt …`: it does not unfold that definition. Pass it:
  `norm_num [Function.IsFixedPt]`.
- `ContractingWith` needs `1 / 2 < 1` **in `NNReal`**; `norm_num` proves it there too. Do not re-prove the
  Lipschitz part: `half_lipschitz` is a theorem you can name.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `LipschitzWith K f` → `dist` bound | `refine LipschitzWith.of_dist_le_mul fun x y => ?_` | R1 |
| `dist` on `ℝ` → `\|x - y\|` (all of them) | `simp only [Real.dist_eq]` | R2 |
| `↑(1 / 2)` → `1 / 2 : ℝ` | `simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]` | R3–R5 |
| reshape an expression | `rw [show e₁ = e₂ by ring]` | R6 |
| `\|a / b\|` → `\|a\| / \|b\|` | `rw [abs_div]` | R7 |
| `\|2\|` → `2` | `rw [abs_two]` | R8 |
| linear inequality, `\|…\|` as unknowns | `linarith` | R9 |
| build `ContractingWith K f` | `⟨hK, hf⟩` | R10 |
| numeral goal in `NNReal` or `ℝ` | `norm_num` | R11 |
| `Function.IsFixedPt f x` → `f x = x` | `simp only [Function.IsFixedPt]` / `norm_num [Function.IsFixedPt]` | R12 |
| see the state | infoview | |
