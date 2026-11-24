# H103 · Collinear boosts compose (velocity addition): cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ` with `|·|`,
`/` and `√`; the arithmetic tactics `nlinarith`, `field_simp`, `positivity`, `linear_combination`;
physlib's Lorentz group `LorentzGroup d`, Lorentz vectors `Lorentz.Vector d`, and the boost `boost i β hβ`.

**The physics (units with c = 1).** Spacetime has one time and `d` space coordinates. A boost along
space axis `i` with speed `β` (`|β| < 1`) changes only the time `t` and the coordinate `xᵢ`:

$$t' = \gamma(\beta)\,(t - \beta x_i), \qquad x_i' = \gamma(\beta)\,(x_i - \beta t), \qquad x_j' = x_j \ (j \ne i),
\qquad \gamma(\beta) = \frac{1}{\sqrt{1 - \beta^2}}.$$

The claim: applying the boost with speed `β₂` and then the one with `β₁` (the product
`boost i β₁ h₁ * boost i β₂ h₂`) is the boost with speed $\beta_3 = (\beta_1 + \beta_2)/(1 + \beta_1\beta_2)$,
and $|\beta_3| < 1$. The algebra behind it, with $s = 1 + \beta_1\beta_2 > 0$:

$$s^2 - (\beta_1 + \beta_2)^2 = (1 - \beta_1^2)(1 - \beta_2^2) \;\Longrightarrow\; \gamma(\beta_3) = \gamma(\beta_1)\,\gamma(\beta_2)\,s,$$

$$\gamma_1\bigl(\gamma_2 (t - \beta_2 x) - \beta_1 \gamma_2 (x - \beta_2 t)\bigr) = \gamma_1\gamma_2\,\bigl(s\,t - (\beta_1 + \beta_2)\,x\bigr) = \gamma(\beta_3)\,(t - \beta_3 x).$$

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- States that contain `|` (absolute values, `match` arms) cannot sit in a table, so they are given in
  a `lean-goal` block, one goal per line.
- Every `⊢` cell and every `lean-goal` line is a state Lean reaches in the companion file;
  `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `\|a\|` | absolute value of `a : ℝ` |
| `√x` | `Real.sqrt x`; it is `0` for `x < 0`, so its lemmas need `0 ≤ x` |
| `γ β` | physlib's `LorentzGroup.γ β = 1 / √(1 - β ^ 2)`, the Lorentz factor (R5) |
| `Fin 1 ⊕ Fin d` | the index type "time or one of `d` space axes"; `⊕` is the sum (disjoint union) type |
| `Sum.inl 0`, `Sum.inr k` | the time index, and space axis `k : Fin d` |
| `Lorentz.Vector d` | `Fin 1 ⊕ Fin d → ℝ`: a spacetime vector `p`, with `p (Sum.inl 0)` = t, `p (Sum.inr k)` = xₖ |
| `LorentzGroup d`, printed `↑(𝓛 d)` | the Lorentz group: real matrices indexed by `Fin 1 ⊕ Fin d` that preserve the Minkowski metric, as a subtype |
| `↑Λ`, written `Λ.1` | the matrix underlying `Λ : LorentzGroup d` (the coercion out of the subtype) |
| `M *ᵥ x` | `Matrix.mulVec M x`: matrix times column vector |
| `Λ • p` | the group element `Λ` acting on the vector `p`; it equals `↑Λ *ᵥ p` (R16) |
| `Λ * Λ'` | product in the group: first apply `Λ'`, then `Λ` |
| `boost i β hβ` | the boost along axis `i : Fin d` with speed `β`; `hβ : \|β\| < 1` |
| `⋯` | a proof term the infoview does not print (here the proof of `\|β₃\| < 1`) |
| `match j with \| Sum.inl 0 => … \| Sum.inr j => …` | a function defined by cases on the index `j` |
| `j✝` | an old `j` that a newer `j` hides (after `match j with \| Sum.inr j`); you cannot type its name |
| `inst✝ : Monoid α` | an unnamed type-class hypothesis |
| `case pos`, `case neg` | the two goals of `by_cases`: the condition holds / fails |
| `case left`, `case right` | the two goals of `constructor` on `A ∧ B` |
| `j_1`, `j_2` | bound variables Lean renamed so they do not clash with a `j` in the context (after `subst`) |
| `x • y • b` | `x • (y • b)`: act by `y`, then by `x` |

---

## Part 1 · `abs_add_lt` (milestone)

Statement: `|β₁| < 1 → |β₂| < 1 → |(β₁ + β₂) / (1 + β₁ * β₂)| < 1`. The composed speed is again below
the speed of light. Prove it first: `boost_mul_boost` needs it as the witness of its `∃`.

**R1 · `rw [abs_lt] at *`** changes the **goal and the context**. The lemma is
`abs_lt : |a| < b ↔ -b < a ∧ a < b`; `rw` with an `↔` replaces one side by the other. `at *` rewrites the
goal and every hypothesis where the pattern occurs. Placeholders: `(a b c : ℝ)`. Here `h : |a| < b`
becomes `h : -b < a ∧ a < b`, and the goal becomes:

```lean-goal
⊢ |c| < 1
⊢ -1 < c ∧ c < 1
```

**R2 · `nlinarith`** **closes** an inequality (or equality) between polynomial expressions over `ℝ`. It
splits `∧` hypotheses, multiplies pairs of hypotheses together, and then searches for a linear
combination. Use it for `0 < 1 + β₁ * β₂` from `-1 < βₖ < 1`, and for `0 < 1 - β ^ 2`. Placeholders:
`(a b : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)`, goal `a * b < 1`.

**R3 · `rw [lt_div_iff₀ hc]`** changes the **goal**. The lemma is
`lt_div_iff₀ : 0 < c → (a < b / c ↔ a * c < b)`. Placeholders: `(a b c : ℝ) (hc : 0 < c)` (it holds in any
ordered field; `ℝ` qualifies).

| Before | After |
|---|---|
| `hc : 0 < c ⊢ a < b / c` | `⊢ a * c < b` |

**R4 · `rw [div_lt_iff₀ hc]`** changes the **goal**. The lemma is
`div_lt_iff₀ : 0 < c → (b / c < a ↔ b < a * c)`. Placeholders: `(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ b / c < a` | `⊢ b < a * c` |

After R3/R4 the goal has no division and R2 closes it.

---

## Part 2 · `gamma_add` (milestone)

Statement: `γ ((β₁ + β₂) / (1 + β₁ * β₂)) = γ β₁ * γ β₂ * (1 + β₁ * β₂)`. Prove the positivity facts first
(`have` + R1 + R2), then the key identity for `1 - β₃ ^ 2` (R6, `ring`), then take square roots
(R5, R7–R11) and clear the fractions (R6).

**R5 · `unfold γ`** changes the **goal**: every `γ β` becomes its definition. Placeholders: `(β : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (γ β)` | `⊢ P (1 / √(1 - β ^ 2))` |

**R6 · `field_simp`** changes the **goal** (or **closes** it): it multiplies out every denominator it can
prove nonzero, using `c ≠ 0` or `0 < c` facts from the context, and moves everything to one fraction-free
equation. It often leaves the factors in a different order; follow it with `ring`. Placeholders:
`(a b c : ℝ)`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ a / c + b = (a + b * c) / c` | closed |
| `hc : c ≠ 0 ⊢ a / c = b` | `⊢ a = c * b` |

**R7 · `rw [Real.sqrt_div' x hy]`** changes the **goal**. The lemma is
`Real.sqrt_div' (x : ℝ) : 0 ≤ y → √(x / y) = √x / √y` (only the denominator needs a sign). Placeholders:
`(x y : ℝ) (hy : 0 ≤ y)`. Write `Real.sqrt_div' _ (by positivity)` (R8) to prove `0 ≤ y` on the spot.

| Before | After |
|---|---|
| `hy : 0 ≤ y ⊢ P √(x / y)` | `⊢ P (√x / √y)` |

**R8 · `positivity`** **closes** a goal `0 ≤ e` or `0 < e` (also `e ≠ 0`) when `e` is visibly nonnegative:
squares, even powers, sums and products of such, positive numerals, and hypotheses `0 < x` in the context.
Placeholders: `(a b : ℝ)`, goal `0 ≤ (a - b) ^ 2`.

**R9 · `rw [Real.sqrt_sq hx]`** changes the **goal**. The lemma is `Real.sqrt_sq : 0 ≤ x → √(x ^ 2) = x`.
Placeholders: `(x : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `hx : 0 ≤ x ⊢ P √(x ^ 2)` | `⊢ P x` |

**R10 · `rw [Real.sqrt_mul hx]`** changes the **goal**. The lemma is
`Real.sqrt_mul : 0 ≤ x → ∀ y, √(x * y) = √x * √y` (only the left factor needs a sign). Placeholders:
`(x y : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `hx : 0 ≤ x ⊢ P √(x * y)` | `⊢ P (√x * √y)` |

**R11 · `h.le`, `h.ne'`** change the **context** (inside a `have`). From `h : 0 < c`, `h.le : 0 ≤ c`
(`LT.lt.le`) and `h.ne' : c ≠ 0` (`LT.lt.ne'`; plain `h.ne` gives `0 ≠ c`). Use them as arguments, e.g.
`Real.sqrt_sq hpos.le`, `div_mul_cancel₀ _ hpos.ne'`. Placeholders: `(c : ℝ) (h : 0 < c)`.

| Before | After `have h1 : 0 ≤ c := h.le` | After `have h2 : c ≠ 0 := h.ne'` |
|---|---|---|
| `h : 0 < c ⊢ P` | `h1 : 0 ≤ c ⊢ P` | `h2 : c ≠ 0 ⊢ P` |

### Worked combinations (W1, W2, on objects that are not the exercise's)

**W1: `field_simp` then `ring`.** For `1 - (2a/(1+a²))² = ((1-a²)/(1+a²))²`, first
`have h : 0 < 1 + a ^ 2 := by positivity`, then R6 leaves a polynomial identity that `ring` closes:

```lean-goal
⊢ 1 - (2 * a / (1 + a ^ 2)) ^ 2 = ((1 - a ^ 2) / (1 + a ^ 2)) ^ 2
⊢ (1 + a ^ 2) ^ 2 - 2 ^ 2 * a ^ 2 = (1 - a ^ 2) ^ 2
```

**W2: the square-root chain.** `rw [Real.sqrt_div' _ (by positivity)]` (R7, R8), `rw [Real.sqrt_sq ht.le]`
(R9, R11), `rw [Real.sqrt_mul hx]` (R10); the last `rw` closes the goal by `rfl`:

```lean-goal
⊢ √(x * y / t ^ 2) = √x * √y / t
⊢ √(x * y) / √(t ^ 2) = √x * √y / t
⊢ √(x * y) / t = √x * √y / t
```

---

## Part 3 · `mul_smul_apply` (milestone)

Statement: `(boost i β₁ h₁ * boost i β₂ h₂) • p = boost i β₁ h₁ • (boost i β₂ h₂ • p)`: acting by a product
is acting twice. It is one instance of R12.

**R12 · `SemigroupAction.mul_smul`** changes the **goal**. The lemma is `(x * y) • b = x • y • b` (and
`x • y • b` means `x • (y • b)`). It holds for any action of a monoid on a type; `LorentzGroup d` acting
on `Lorentz.Vector d` is one. Use the full name: under `open Lorentz Vector` plain `mul_smul` is ambiguous.
Placeholders: `{α β : Type} [Monoid α] [MulAction α β] (x y : α) (b : β)` (α has an associative `*` with
`1`; `MulAction α β` says how `α` acts on `β`).

| Before | After |
|---|---|
| `⊢ P ((x * y) • b)` | `⊢ P (x • y • b)` |

---

## Part 4 · `boost_mul_boost`

Statement: `∃ h : |β₃| < 1, boost i β₁ h₁ * boost i β₂ h₂ = boost i β₃ h` with
`β₃ = (β₁ + β₂) / (1 + β₁ * β₂)`. The `∃` ranges over proofs: you must give the bound (Part 1), then the
equation of group elements. Reduce it to vectors (R14), then to coordinates (R16, R17, R18, R19), then to
three scalar identities (R20–R24), each fed the cancellation fact `h3` (R15).

### Setting up

**R13 · `refine ⟨hp, ?_⟩`** on `∃ h : p, Q h` changes the **goal**: the witness is the proof `hp`, and the
goal becomes the body with that proof plugged in. The infoview prints the plugged-in proof as `⋯`.
Placeholders: `(p : Prop) (Q : p → Prop) (hp : p)`.

| Before | After |
|---|---|
| `⊢ ∃ (h : p), Q h` | `⊢ Q hp` |

**R14 · `apply LorentzGroup.eq_of_mulVec_eq`** changes the **goal**. The lemma is
`(∀ x, ↑Λ *ᵥ x = ↑Λ' *ᵥ x) → Λ = Λ'`: two Lorentz transformations are equal when their matrices agree on
every vector. `apply` leaves the premise as the goal; continue with `intro x`. Placeholders:
`{d : ℕ} (Λ Λ' : LorentzGroup d)`.

| Before | After |
|---|---|
| `⊢ Λ = Λ'` | `⊢ ∀ (x : Fin 1 ⊕ Fin d → ℝ), ↑Λ *ᵥ x = ↑Λ' *ᵥ x` |

**R15 · `div_mul_cancel₀`** changes the **context** (with `have`). The lemma is
`div_mul_cancel₀ (a : ℝ) : b ≠ 0 → a / b * b = a`. You need it because `ring` and `linear_combination`
treat `a / b` as `a * b⁻¹` and do not know `b⁻¹ * b = 1`. Placeholders: `(a b : ℝ) (hb : 0 < b)`; the
`b ≠ 0` comes from `hb.ne'` (R11).

| Before | After `have h3 : a / b * b = a := div_mul_cancel₀ a hb.ne'` |
|---|---|
| `hb : 0 < b ⊢ P` | `h3 : a / b * b = a ⊢ P` |

### Into coordinates

**R16 · `rw [← Lorentz.Vector.smul_eq_mulVec]`** changes the **goal**. The lemma is `Λ • p = ↑Λ *ᵥ p`;
right to left it turns a matrix-vector product back into the group action, where R12 and R17 apply.
`rw` rewrites every copy of the first instance it finds, so the two sides (different `Λ`) need two
rewrites. Placeholders: `{d : ℕ} (Λ : LorentzGroup d) (p : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `⊢ P (↑Λ *ᵥ p)` | `⊢ P (Λ • p)` |

**R17 · `rw [Lorentz.Vector.boost_toCoord_eq]`** changes the **goal**: a boosted vector becomes the
explicit function of the index `j` from the physics box above. Each `rw` rewrites one boost; the exercise
has three. Placeholders: `{d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1) (p : Lorentz.Vector d)`.

```lean-goal
⊢ P (boost i β hβ • p)
⊢ P fun j => match j with | Sum.inl 0 => γ β * (p (Sum.inl 0) - β * p (Sum.inr i)) | Sum.inr j => if j = i then γ β * (p (Sum.inr i) - β * p (Sum.inl 0)) else p (Sum.inr j)
```

(In the infoview the second goal is spread over four lines.) After the three R17 rewrites, `rw [gamma_add h₁ h₂]`
replaces `γ β₃` on the right by `γ β₁ * γ β₂ * (1 + β₁ * β₂)`.

**R18 · `funext j`** changes the **goal and the context**: an equation of functions becomes the equation of
their values at a new `j`. Placeholders: `{d : ℕ} (f g : Fin 1 ⊕ Fin d → ℝ)`.

| Before | After |
|---|---|
| `⊢ f = g` | `j : Fin 1 ⊕ Fin d ⊢ f j = g j` |

**R19 · `match j with | Sum.inl 0 => tacs | Sum.inr k => tacs`** changes the **goal list**: one goal per
constructor of `Fin 1 ⊕ Fin d`, with `j` replaced by `Sum.inl 0` (time) or `Sum.inr k` (a new
`k : Fin d`). The literal `0` covers `Fin 1`, which has no other element. Placeholders:
`{d : ℕ} (P : Fin 1 ⊕ Fin d → Prop) (j : Fin 1 ⊕ Fin d)`. In `guide.lean` the same split is also written
as `refine match j with | Sum.inl 0 => ?_ | Sum.inr k => ?_` so the infoview shows the two goals:

| Before | After |
|---|---|
| `j : Fin 1 ⊕ Fin d ⊢ P j` | `⊢ P (Sum.inl 0)`, `k : Fin d ⊢ P (Sum.inr k)` |

In the exercise, writing `| Sum.inr j` reuses the name: the old `j` is shown as `j✝`.

### Evaluating each coordinate

**R20 · `simp only [if_true]`** changes the **goal**. After R19 the goal still reads
`match Sum.inl 0 with …` and `(fun j => …) (Sum.inr i)`; `simp only` evaluates a `match` on a constructor,
applies `fun`s to their arguments, and with `if_true` turns `if a = a then x else y` into `x` (it first
proves `a = a` is `True`). Do this before R21, which cannot see through `match` or `if`. Placeholders:
`{d : ℕ} (k : Fin d) (x y : ℝ)`.

```lean-goal
⊢ P ((fun j => match j with | Sum.inl 0 => if k = k then x else y | Sum.inr val => y) (Sum.inl 0))
⊢ P x
```

**R21 · `linear_combination e * h`** **closes** a goal `L = R` when `L - R - e * (h.lhs - h.rhs)` is `0` by
`ring`. Here `h` is the cancellation fact `h3` (R15). To find `e`, expand `L - R` by hand, treating
`β₃ = (β₁ + β₂) / (1 + β₁ * β₂)` as one unknown and writing `s = 1 + β₁ * β₂`: every term cancels except
`c * (β₃ * s) - c * (β₁ + β₂)` for a single product `c` (γ factors times one coordinate of `x`), and that
`c` is `e` (with its sign: `L - R = e * (h.lhs - h.rhs)`). Placeholders:
`(s t u : ℝ) (h : s / t * t = s)`, goal `u * (s / t * t) + u = u * s + u`, closed by `linear_combination u * h`.

**R22 · `by_cases hj : j = i`** changes the **goal list and the context**: two goals, one with
`hj : j = i` (`case pos`) and one with `hj : ¬j = i` (`case neg`). Placeholders: `{d : ℕ} (i j : Fin d)`.

| Before | After |
|---|---|
| `⊢ P` | `hj : j = i ⊢ P`, `hj : ¬j = i ⊢ P` |

**R23 · `subst hj`** changes the **context**: with `hj : j = i` and `i` a local variable, it deletes `i` and
`hj` and writes `j` wherever `i` was. Afterwards every `if j = j` is an R20 job. Placeholders:
`{d : ℕ} (i j : Fin d) (P : Fin d → Fin d → Prop)`.

| Before | After |
|---|---|
| `hj : j = i ⊢ P j i` | `⊢ P j j` |

**R24 · `simp [hj]`** with `hj : ¬j = i` changes the **goal** (and usually **closes** it): it rewrites
`j = i` to `False`, so `if j = i then x else y` becomes `y`. In the exercise both sides then read
`x (Sum.inr j)` and `simp` closes the goal. Placeholders: `{d : ℕ} (i j : Fin d) (hj : ¬j = i) (x y : ℝ)`.

| Before | After |
|---|---|
| `hj : ¬j = i ⊢ P (if j = i then x else y)` | `⊢ P y` |

### Worked combinations (W3, W4, on objects that are not the exercise's)

**W3: coordinatewise identity.** `F i v` doubles time and adds `xᵢ`, triples axis `i`, leaves the
rest. `F i (F i v)` is checked with `unfold F`, R18, R19, then in the time row R20 and `ring`; in the
space row R22, then R23, R20, `ring` (`j = i`) or R24 (`j ≠ i`). This is the shape of Part 4 after R17,
with `ring` in place of R21 because no division occurs.

**W4: `linear_combination` against a cancellation fact.** With `h3 : s / t * t = s` from R15,
`w * (u - s / t * (t * u)) = w * u * (1 - s)` is closed by `linear_combination (-(w * u)) * h3`: the
goal's two sides differ by `-(w * u)` times `(s / t * t - s)`.

---

## Traps

- With `open Lorentz Vector`, plain `mul_smul` and `smul_eq_mulVec` are ambiguous, and so is a bare
  `Λ.1 *ᵥ x`. Write `SemigroupAction.mul_smul`, `Lorentz.Vector.smul_eq_mulVec`, and give `x` its type.
- `rw [abs_lt] at *` inside `have hpos : … := by …` changes `h₁ h₂` only inside that proof; outside,
  they are still `|βₖ| < 1`, which the milestones expect.
- `field_simp` only clears a denominator it can prove nonzero: put `hpos : 0 < 1 + β₁ * β₂` in the context
  first.
- `div_mul_cancel₀` wants `b ≠ 0`, not `0 < b`: pass `hpos.ne'` (R11). `hpos.ne` is `0 ≠ b`.
- `ring` and `linear_combination` cannot evaluate `match` or `if`. Run `simp only [if_true]` (R20) first,
  or the call fails with a goal that still contains `match`.
- `subst hj` with `hj : j = i` removes `i`: after it, the boosted axis is called `j`.
- `rw [← Lorentz.Vector.smul_eq_mulVec]` rewrites one matrix at a time: write it twice, once per side.
- `t1 ; t2` runs `t2` on the first goal only. Handle the `match` and `by_cases` branches one by one.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `\|a\| < b` → two inequalities | `rw [abs_lt] at *` | R1 |
| polynomial inequality from bounds | `nlinarith` | R2 |
| clear `/ c` in `<` | `rw [lt_div_iff₀ hc]` / `rw [div_lt_iff₀ hc]` | R3, R4 |
| open `γ` | `unfold γ` | R5 |
| clear denominators | `field_simp` (then `ring`) | R6 |
| `√(x / y)`, `√(x ^ 2)`, `√(x * y)` | `Real.sqrt_div' _ hy`, `Real.sqrt_sq hx`, `Real.sqrt_mul hx` | R7, R9, R10 |
| `0 ≤ square` | `positivity` | R8 |
| `0 < c` → `0 ≤ c`, `c ≠ 0` | `h.le`, `h.ne'` | R11 |
| act by a product | `SemigroupAction.mul_smul` | R12 |
| `∃ h : p, Q h` | `refine ⟨hp, ?_⟩` | R13 |
| Lorentz elements equal | `apply eq_of_mulVec_eq; intro x` | R14 |
| `a / b * b = a` | `div_mul_cancel₀ a hb.ne'` | R15 |
| `↑Λ *ᵥ x` → `Λ • x` | `rw [← Lorentz.Vector.smul_eq_mulVec]` | R16 |
| boost in coordinates | `rw [Lorentz.Vector.boost_toCoord_eq]` | R17 |
| functions equal | `funext j` | R18 |
| split time / space index | `match j with \| Sum.inl 0 => … \| Sum.inr j => …` | R19 |
| evaluate `match`, `if a = a` | `simp only [if_true]` | R20 |
| ring identity up to `h` | `linear_combination e * h` | R21 |
| `j = i` or not | `by_cases hj : j = i` | R22 |
| substitute a variable | `subst hj` | R23 |
| `if` with false condition | `simp [hj]` | R24 |
| see the state | infoview | |
