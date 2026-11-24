# M124 · Catastrophic cancellation and the stable quadratic formula: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`constructor`, `have`, `rw`, `ring`, `·`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, absolute value
`|·|`, `Real.sqrt`, the order tactics `gcongr` and `linarith`, `calc` chains, `let` in a statement, and
the field tactics `field_simp` and `linear_combination`.

**The maths.** A floating-point value `x̂ = x (1 + δ)` has *relative error* `δ` (`|δ| ≤ u`, the unit
roundoff). For `x̂ - ŷ` the relative error is `|(x̂ - ŷ) - (x - y)| / |x - y| = |x δ₁ - y δ₂| / |x - y|`,
bounded by `u (|x| + |y|) / |x - y|`: the factor `(|x| + |y|) / |x - y|` (the *condition number* of
subtraction) blows up as `x → y`. In the quadratic formula with `b > 0`, `-b + √D` (`D = b² - 4ac`) is such a
cancelling difference; `-b - √D` is not. Vieta's formula `x₁ x₂ = c / a` gives the other root as
`c / (a x₁)` with no cancellation.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`calc`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is a goal the step leaves alone.
- A hypothesis `h` (or `g`) in an entry only finishes the example. `h : A ∧ True` or `h : A ∧ B` hides `A`
  from tactics that search the context, so the infoview shows the goal they leave.
- Placeholders are written as Lean binders. `{α : Type}` is any type; a bracket such as `[AddGroup α]` is a
  requirement on `α` (a *type class*: `α` has `+`, `0`, `-`). `ℝ`, `ℚ`, `ℤ` qualify. Most entries here are
  stated for `ℝ`, which meets every class these lemmas ask for.
- Every `⊢` cell and every line of a goal block is a state Lean reaches in the companion file;
  `tools/guide_sync.py` checks that. States that contain `|·|` are shown as a goal block (before, then
  after) instead of a table, because `|` would split a Markdown table cell.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (exact, not floats) |
| `\|a\|` | absolute value of `a` (Mathlib's `abs a`) |
| `√x` | `Real.sqrt x : ℝ`; it is `0` for `x < 0`, so its lemmas ask for `0 ≤ x` |
| `x ^ 2` | power with a natural-number exponent |
| `a ≠ b` | `¬ (a = b)` |
| `let x := e; P x` | a goal that names `e` as `x` first (R13) |
| `x : ℝ := e` | a context entry: `x` is a local definition with value `e` (after R13) |
| `h.1`, `h.2` | the two halves of `h : A ∧ B` |
| `h.mpr` | for `h : A ↔ B`, the direction `B → A` (`h.mp` is `A → B`) |
| `case hab`, `case calc_1` | names Lean gives the goals that `gcongr` and `calc` produce |
| `case left`, `case right` | the two goals `constructor` makes from `A ∧ B` |
| `2 ^ 2`, `a * 2 * c` | `field_simp` output: it does not evaluate numerals and reorders products (R18) |

---

## Part 1 · `sub_rel_error`

Statement: if `x ≠ y`, `|δ₁| ≤ u` and `|δ₂| ≤ u`, then
`|(x (1 + δ₁) - y (1 + δ₂)) - (x - y)| / |x - y| ≤ u (|x| + |y|) / |x - y|`.
Both sides divide by `|x - y|`: drop it (R3), simplify the numerator (R4), bound it by a chain (R5–R8).

**R1 · `sub_ne_zero`** changes the **goal**. The lemma is `sub_ne_zero : a - b ≠ 0 ↔ a ≠ b`; `rw` with an
`↔` replaces one side by the other. Placeholders: `{α : Type} [AddGroup α] (a b : α)`. As a term,
`sub_ne_zero.mpr hxy : x - y ≠ 0`.

| Before | After |
|---|---|
| `⊢ a - b ≠ 0` | `⊢ a ≠ b` |

**R2 · `abs_pos`** changes the **goal**. The lemma is `abs_pos : 0 < |a| ↔ a ≠ 0`. Placeholders: `(a : ℝ)`.
Combined with R1: `abs_pos.mpr (sub_ne_zero.mpr hxy) : 0 < |x - y|`. The solution records this as
`hpos`; `gcongr` (R3) does not need it, since it only asks for `0 ≤ |x - y|` and proves that itself.

Before, then after:

```lean-goal
⊢ 0 < |a|
⊢ a ≠ 0
```

**R3 · `gcongr`** (common denominator) changes the **goal**: `gcongr` ("generalized congruence") matches
the two sides of an inequality against each other and reduces it to inequalities between the parts that
differ. For `a / c ≤ b / c` that is `a ≤ b`; the side condition `0 ≤ c` it discharges itself (with the
`positivity` tactic, which knows `0 ≤ |d|`). Placeholders: `(a b d : ℝ)`.

Before, then after:

```lean-goal
⊢ a / |d| ≤ b / |d|
⊢ a ≤ b
```

**R4 · `rw [show e₁ = e₂ by ring]`** changes the **goal**: `show e₁ = e₂ by ring` is a proof of an equation
you write yourself, proved on the spot by `ring`; `rw` then replaces `e₁` by `e₂`. `e₁` must be written
exactly as the goal prints it (copy it from the infoview). Placeholders: `(x d : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (x * (1 + d) - x)` | `⊢ P (x * d)` |

**R5 · `calc`** changes the **goal list**. `calc a ≤ b := p₁` then `_ = c := p₂` (one step per line, `_`
is the previous right side) proves `a ≤ c` by chaining the steps; `≤` with `=` gives `≤`, and `≤` with `<`
gives `<`. A step proved by `?_` becomes a goal. The first line's left side must match the goal's left side,
and the last right side the goal's right side. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ a ≤ b`, `⊢ b = c` |

**R6 · `abs_sub`** changes the **goal** when used as the first `calc` step (`:= abs_sub _ _`): the step
`|a - b| ≤ |a| + |b|` is proved, and what is left is the rest of the chain, from `|a| + |b|` on. At this
Mathlib version the lemma is `abs_sub (a b : α) : |a - b| ≤ |a| + |b|` (the triangle inequality for a
difference). Placeholders: `(a b c : ℝ)`; `_ _` lets Lean find `a`, `b` from the step's statement. As a
fact, `have h := abs_sub a b` adds `h : |a - b| ≤ |a| + |b|` to the context instead.

Before, then after (the second `calc` step left open with `?_`):

```lean-goal
⊢ |a - b| ≤ c
⊢ |a| + |b| ≤ c
```

**R7 · `abs_mul`** changes the **goal**. The lemma is `abs_mul (a b : α) : |a * b| = |a| * |b|`.
Placeholders: `(a b : ℝ)`. `rw [abs_mul, abs_mul]` rewrites two different products (each `rw` rewrites the
first pattern it finds, and every copy of that exact instance).

Before, then after:

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R8 · `gcongr`** (monotone expression) changes the **goal list**: both sides have the same shape
`|a| * _ + |c| * _`, so the goal reduces to `p ≤ u` and `q ≤ u`. Side conditions `0 ≤ |a|`, `0 ≤ |c|` are
proved automatically, and each main goal is closed by a hypothesis in context if there is one (in the
exercise, `h1` and `h2`, so `by gcongr` closes the step). Placeholders: `(a c p q u : ℝ)`.

Before, then the two goals after:

```lean-goal
⊢ |a| * p + |c| * q ≤ |a| * u + |c| * u
⊢ p ≤ u
⊢ q ≤ u
```

The last step of the chain is a commutative-ring identity: `ring` (TACTIC_STATES, "Closing").

---

## Part 2 · `sub_rel_error_sharp`

Statement: for `0 ≤ u`, `0 < y < x`, with `δ₁ = u` and `δ₂ = -u` the relative error *equals* the bound.
The numerator is `u (x + y)` (R4), and every absolute value has a known sign (R9–R12). One `rw [R4, R9, R12,
R12]` makes both sides identical, and `rw` then closes the goal by `rfl`.

**R9 · `abs_of_nonneg`** changes the **goal**. The lemma is `abs_of_nonneg : 0 ≤ a → |a| = a`: give it the
proof, `rw [abs_of_nonneg ha]`, and it rewrites `|a|`. Placeholders: `(a : ℝ) (ha : 0 ≤ a)`.

Before, then after (with `ha : 0 ≤ a` in context):

```lean-goal
⊢ P |a|
⊢ P a
```

**R10 · `mul_nonneg`** changes the **goal list**. The lemma is `mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b`.
With `apply` it leaves one goal per factor; as a term, `mul_nonneg hu (by linarith)` supplies both proofs
inline. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ a * b` | `⊢ 0 ≤ a`, `⊢ 0 ≤ b` |

**R11 · `linarith`** **closes** a goal `s < t`, `s ≤ t`, `s = t` (and, as here, `s ≠ t`) that follows from
the hypotheses in context by adding them with nonnegative coefficients (linear arithmetic over ordered
fields). It does not multiply hypotheses together. Inside a term, `(by linarith : 0 < x)` proves `0 < x` on
the spot; the type ascription `( … : T)` says which fact you want. Placeholders: `(p q : ℝ)`.

| Before | After |
|---|---|
| `hp : 0 < p, hq : 0 ≤ q ⊢ p + q ≠ 0` | no goals |

**R12 · `abs_of_pos`** changes the **goal**. The lemma is `abs_of_pos : 0 < a → |a| = a`. Placeholders:
`(a : ℝ) (ha : 0 < a)`.

Before, then after (with `ha : 0 < a` in context):

```lean-goal
⊢ P |a|
⊢ P a
```

**W1** (on `|u * (p - q)| = u * (|p| - |q|)`, `0 ≤ u`, `0 < q < p`): one `rw` with R9 (its argument built
by R10 and R11), R12, R12 closes the goal:

```lean-goal
⊢ |u * (p - q)| = u * (|p| - |q|)
```

**W2** (on `|p * a - q| ≤ |p| * u + |q|` from `|a| ≤ u`): a three-step `calc`, R6, then `by rw [abs_mul]`
(R7), then `by gcongr` (R8), proves

```lean-goal
⊢ |p * a - q| ≤ |p| * u + |q|
```

---

## Part 3 · `stable_quadratic`

Statement: for `a ≠ 0`, `b > 0`, `D = b ^ 2 - 4 * a * c ≥ 0` and `x₁ := (-b - √D) / (2 * a)`:
`a * x₁ ^ 2 + b * x₁ + c = 0` and `(-b + √D) / (2 * a) = c / (a * x₁)`.
Introduce `x₁` (R13), record the two facts about `√D` (R14, R15), unfold `x₁` (R16), replace `√D` by a
variable `s` (R17), prove `-b - s ≠ 0` (R11), split (`constructor`), then in each half clear denominators
(R18) and close with `s ^ 2 = D` (R19).

**R13 · `intro x`** on a `let` goal changes the **context and the goal**: the context gains the local
definition `x : ℝ := e`, and the goal mentions `x`. Lean can still see through `x` (so `exact h` works),
but `rw` and `field_simp` work on the text, where `x` is just a name. Placeholders: `(e : ℝ)`.

| Before | After |
|---|---|
| `⊢ let x := e; P x` | `x : ℝ := e ⊢ P x` |

**R14 · `Real.sq_sqrt`** changes the **context**. The lemma is `Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x`;
`have hs := Real.sq_sqrt hd` adds the instance for `d`. Placeholders: `(d : ℝ) (hd : 0 ≤ d)`.

| Before | After |
|---|---|
| `⊢ G` | `hs : √d ^ 2 = d ⊢ G` |

**R15 · `Real.sqrt_nonneg`** changes the **context**. The lemma is `Real.sqrt_nonneg (x : ℝ) : 0 ≤ √x`,
with no hypothesis. Placeholders: `(d : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hn : 0 ≤ √d ⊢ G` |

**R16 · `simp only [x]`** changes the **goal**: it replaces the `let` variable `x` by its value. `x : ℝ := e`
stays in the context. Placeholders: `(e : ℝ)`.

| Before | After |
|---|---|
| `x : ℝ := e ⊢ P x` | `⊢ P e` |

**R17 · `generalize e = s at hs ⊢`** changes the **context and the goal**: every occurrence of the
expression `e` in `hs` and in the goal (`⊢`) becomes a fresh variable `s`. Anything you know about `e` must
be in a listed hypothesis first (R14, R15); afterwards `s` is an arbitrary real with only those facts.
Placeholders: `(d : ℝ)`, `e = √d`.

| Before | After |
|---|---|
| `hs : √d ^ 2 = d ⊢ P (√d + 1)` | `s : ℝ, hs : s ^ 2 = d ⊢ P (s + 1)` |

**R18 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero and
moves everything to the form `numerator = numerator`. Each denominator needs a hypothesis `≠ 0` in context
(`ha : a ≠ 0`, `hne : -b - s ≠ 0`); `2 ≠ 0` it proves itself. It reorders products and leaves numerals such as
`2 ^ 2` unevaluated, so read the result before choosing R19's coefficient. Placeholders: `(x y z a : ℝ)
(ha : a ≠ 0)`.

| Before | After |
|---|---|
| `⊢ x / a + y = z` | `⊢ x + a * y = a * z` |

**R19 · `linear_combination k * h`** **closes** an equation goal `L = R` using `h : hl = hr`: it checks by
`ring` that `L - R - k * (hl - hr) = 0`. `k` is any expression (`1` by default, `(-1 : ℝ)`, `a * 2`); use
`k₁ * h₁ + k₂ * h₂` for several facts. To find `k`: expand `L - R`, and match the coefficient of `s ^ 2`
against `hl - hr = s ^ 2 - D`. Placeholders: `(p q k : ℝ) (h : p ^ 2 = q)`.

| Before | After |
|---|---|
| `h : p ^ 2 = q ⊢ k * p ^ 2 + 1 = k * q + 1` | no goals |

**W3** (on `let r := (√d - p) / a; a * r ^ 2 + 2 * p * r = (d - p ^ 2) / a`): R13, R14, R16, R17, R18,
then `linear_combination hs`. The states, one per step:

```lean-goal
⊢ let r := (√d - p) / a; a * r ^ 2 + 2 * p * r = (d - p ^ 2) / a
⊢ a * r ^ 2 + 2 * p * r = (d - p ^ 2) / a
⊢ a * ((√d - p) / a) ^ 2 + 2 * p * ((√d - p) / a) = (d - p ^ 2) / a
⊢ a * ((s - p) / a) ^ 2 + 2 * p * ((s - p) / a) = (d - p ^ 2) / a
⊢ (s - p) * (s - p + p * 2) = d - p ^ 2
```

The last goal minus `hs` (`s ^ 2 = d`) is `0` by `ring`, so the coefficient is `1`.

---

## Traps

- **`field_simp` rewrites inside `√(…)`.** Without R17 it turns `√(b ^ 2 - 4 * a * c)` into
  `√(b ^ 2 - a * 4 * c)` in some goals, and `hs` (stated with `4 * a * c`) no longer matches, so
  `linear_combination hs` fails. Generalize the root away before `field_simp`.
- **Generalize after collecting facts.** `generalize` only rewrites the hypotheses you list after `at`; a
  fact about `√D` proved afterwards says nothing about `s`, which is now an arbitrary real.
- **Unfold the `let` first.** After R13 alone, `generalize √(…) = s` replaces only the visible `√`: the
  one inside `x₁ : ℝ := (-b - √(…)) / (2 * a)` stays, and the goal mixes `s` with `x₁`. `simp only [x₁]`
  (R16) first puts every `√` in the goal.
- **`field_simp` needs `-b - s ≠ 0` in context** to clear `c / (a * ((-b - s) / (2 * a)))`; with it missing,
  the denominator stays and `linear_combination` fails. `linarith` proves it from `hb`, `hsn`.
- **`rw` ends by trying `rfl`.** In Part 2 the goal closes as soon as both sides are identical; a further
  tactic then errors with "no goals".
- **`rw [show e₁ = e₂ by ring]`** fails with "did not find instance of the pattern" if `e₁` differs from the
  goal's text, even if it is equal by `ring`. Copy it from the infoview.
- `abs_sub` is this Mathlib version's name for `|a - b| ≤ |a| + |b|`; in other versions it may state a
  different inequality. Check with `#check abs_sub`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `0 < \|x - y\|` from `x ≠ y` | `abs_pos.mpr (sub_ne_zero.mpr hxy)` | R1, R2 |
| drop a common denominator `c ≥ 0` | `gcongr` | R3 |
| replace an expression by a ring-equal one | `rw [show e₁ = e₂ by ring]` | R4 |
| chain inequalities | `calc a ≤ b := p₁` / `_ = c := p₂` | R5 |
| `\|a - b\| ≤ \|a\| + \|b\|` | `abs_sub _ _` | R6 |
| `\|a * b\| = \|a\| * \|b\|` | `rw [abs_mul]` | R7 |
| monotone step from hypotheses | `gcongr` | R8 |
| `\|a\| = a` from `0 ≤ a` / `0 < a` | `rw [abs_of_nonneg h]` / `rw [abs_of_pos h]` | R9, R12 |
| `0 ≤ a * b` | `mul_nonneg ha hb` | R10 |
| linear fact from hypotheses | `linarith`, `(by linarith : 0 < x)` | R11 |
| enter a `let` | `intro x₁` | R13 |
| `√D ^ 2 = D`, `0 ≤ √D` | `Real.sq_sqrt hD`, `Real.sqrt_nonneg D` | R14, R15 |
| unfold a `let` variable | `simp only [x₁]` | R16 |
| hide `√D` behind a variable | `generalize √D = s at hs hsn`, plus the goal (R17) | R17 |
| clear denominators | `field_simp` (with `≠ 0` facts in context) | R18 |
| close using `s ^ 2 = D` | `linear_combination k * hs` | R19 |
| split `A ∧ B` | `constructor` | TACTIC_STATES |
