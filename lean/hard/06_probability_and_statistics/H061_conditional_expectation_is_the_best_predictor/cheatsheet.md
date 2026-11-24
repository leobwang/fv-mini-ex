# H061 · Conditional expectation is the best predictor: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `have`, `exact`, `apply`, `intro`, `rw`,
`funext`, `ring`, `calc`. **New here:** Mathlib's measure theory and probability: σ-algebras
(`MeasurableSpace`), measures and probability measures, the Bochner integral `∫ ω, f ω ∂μ`,
`Integrable` (L¹), `MemLp f 2 μ` (L²), `StronglyMeasurable[m]` (measurable for a sub-σ-algebra), the
conditional expectation `μ[f | m]`, almost-everywhere equality `=ᵐ[μ]`, and the tactics `congr 1` and
`linarith`.

**The maths.** `(Ω, mΩ, μ)` is a probability space; `m ≤ mΩ` is a sub-σ-algebra (the information you
have: an `m`-measurable function is one whose value you know once you know which `m`-events occurred).
`X ∈ L²(μ)` means `E[X²] < ∞`. Write `Z = E[X | m]` for the conditional expectation: the (a.e. unique)
`m`-measurable, integrable function with `∫_A Z dμ = ∫_A X dμ` for every `A ∈ m`. Two facts about it are
all this problem needs:

- **Tower property:** `E[E[F | m]] = E[F]` (R4).
- **Pull-out:** if `W` is `m`-measurable then `E[W G | m] = W · E[G | m]` almost everywhere (R5).

1. **Orthogonality** (`cross_term_zero`). For `m`-measurable `W ∈ L²`:
   `E[W X] = E[E[W X | m]] = E[W Z]` (tower, then pull-out), so `E[W (X - Z)] = E[W X] - E[W Z] = 0`.
   Geometrically: `X - Z` is orthogonal in `L²` to the subspace of `m`-measurable variables, so `Z` is the
   orthogonal projection of `X` onto it.
2. **Expansion** (`integral_sq_split`). Pointwise `(X - Y)² = (X - Z)² + 2 (Z - Y)(X - Z) + (Z - Y)²`;
   integrate each term (each is integrable because all three variables are in `L²`).
3. **Pythagoras** (`condExp_best_predictor`). With `W = Z - Y` (`m`-measurable, in `L²`), the middle
   term is `2 E[W (X - Z)] = 0` by step 1, and `E[W²] ≥ 0`, so `E[(X - Z)²] ≤ E[(X - Y)²]`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. `G : Prop` with `h : T → G` is a goal the entry does not touch; `h`
  only shows which fact `T` the step added.
- Placeholders are written as Lean binders. `{Ω : Type}` is the sample space. `[MeasurableSpace Ω]` says
  `Ω` carries a σ-algebra; `{m mΩ : MeasurableSpace Ω}` declares two, and Lean uses the **last** one,
  `mΩ`, as the ambient σ-algebra of `μ : Measure Ω`, so `m` is the sub-σ-algebra. `[IsProbabilityMeasure μ]`
  says `μ Ω = 1`. A bracket `[…]` is a requirement Lean finds by itself (a *type class*).
- A goal containing `μ[f | m]` is shown in a `lean-goal` block: the `|` would break a table cell.
- Every `⊢` cell and goal line is a state Lean reaches in the companion file; `tools/guide_sync.py`
  checks that.

## Reading the goals

| You see | It means |
|---|---|
| `{Ω : Type*}`, `Ω : Type u_1` | `Ω` is any type (the sample space); `Type*` lets it live in any universe `u_1`. The guide writes `{Ω : Type}` |
| `m mΩ : MeasurableSpace Ω`, `hm : m ≤ mΩ` | two σ-algebras on `Ω`; every `m`-event is an `mΩ`-event |
| `μ : Measure Ω` | a measure on the ambient σ-algebra `mΩ`; with `IsProbabilityMeasure μ` a probability `P` |
| `∫ (ω : Ω), f ω ∂μ` | the (Bochner) integral of `f : Ω → ℝ`, i.e. `E[f]`; it is `0` if `f` is not integrable |
| `μ[f \| m]` | `E[f \| m]`, the conditional expectation: a function `Ω → ℝ`; `μ[f \| m] ω` is its value at `ω` |
| `μ[f]` (no `\| m`) | just the integral `E[f]`, a number; a different thing |
| `MemLp f 2 μ` | `f ∈ L²(μ)`: measurable (a.e. strongly) with `E[f²] < ∞`; the `2` lives in `ℝ≥0∞` (`ENNReal`, the extended nonnegative reals `[0, ∞]`), the type of exponents `p` |
| `one_le_two` | the lemma `1 ≤ 2`, here at type `ℝ≥0∞`: the `1 ≤ p` argument of R1 and R3 |
| `Integrable f μ` | `f ∈ L¹(μ)`: measurable (a.e. strongly) with `E[\|f\|] < ∞` |
| `StronglyMeasurable[m] f` | `f` is `m`-measurable; the **infoview prints it as `StronglyMeasurable f`** |
| `f =ᵐ[μ] g` | `f ω = g ω` for `μ`-almost every `ω` (outside a null set) |
| `f * g`, `f - g` (functions) | pointwise: `(f * g) ω = f ω * g ω` (R8) |
| `0 ≤ f` (functions) | pointwise `∀ ω, 0 ≤ f ω`; after `intro ω` it prints `0 ω ≤ f ω` |
| `fun x => f x ^ 2` | the function `ω ↦ f(ω)²`; Lean renames bound variables (`ω`, `x`, `a`) freely |
| `inst✝ : …` | an unnamed type-class hypothesis (`[MeasurableSpace Ω]` etc.) |
| `case calc_1`, `case e_f` | goal names after `calc … := ?_` and `congr 1` |

---

## Part 1 · `cross_term_zero` (milestone 1)

Statement: for `m`-measurable `W ∈ L²`, `∫ ω, W ω * (X ω - μ[X | m] ω) ∂μ = 0`. Prove it first:
`condExp_best_predictor` applies it with `W := μ[X | m] - Y` (Part 3). Plan: integrability facts
(R1–R3), the key equation `E[W X] = E[W Z]` (R4 → R6 with R5), then rewrite the integrand (R7, R8) and
split the integral (R9, R10).

### L² facts

**R1 · `MemLp.condExp`** changes the **context**. Lemma: `1 ≤ p → MemLp f p μ → MemLp μ[f | m] p μ`;
write `hf.condExp one_le_two`. Placeholders: `{Ω : Type} {m mΩ : MeasurableSpace Ω} (μ : Measure Ω)
(f : Ω → ℝ) (hf : MemLp f 2 μ)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, plus `hc : MemLp μ[f \| m] 2 μ` |

**R2 · `MemLp.integrable_mul`** changes the **context**. Lemma (Hölder with `1/2 + 1/2 = 1`):
`MemLp f 2 μ → MemLp g 2 μ → Integrable (f * g) μ`; write `hf.integrable_mul hg`. Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hfg : Integrable (f * g) μ ⊢ G` |

**R3 · `MemLp.integrable`** changes the **context**. Lemma: `1 ≤ q → MemLp f q μ → Integrable f μ` on a
finite measure; write `hf.integrable one_le_two`. Needed for R5's last argument `Integrable X μ`.
Placeholders: as R2, plus `[IsProbabilityMeasure μ]`.

| Before | After |
|---|---|
| `⊢ G` | `hi : Integrable f μ ⊢ G` |

### Tower property and pull-out

**R4 · `integral_condExp`** changes the **goal**. Lemma: `(hm : m ≤ mΩ) → ∫ x, μ[f | m] x ∂μ = ∫ x, f x ∂μ`
(it also needs `SigmaFinite (μ.trim hm)`, which Lean finds for a probability measure). Read right to left
it wraps an integrand in `μ[· | m]`: `rw [← integral_condExp hm (f := F)]`. Name `f`, otherwise the
right side `∫ x, ?f x ∂μ` is ambiguous. Placeholders: `{Ω : Type} {m mΩ : MeasurableSpace Ω}
(hm : m ≤ mΩ) (μ : Measure Ω) (F : Ω → ℝ) [IsProbabilityMeasure μ]`.

```lean-goal
⊢ P (∫ (ω : Ω), F ω ∂μ)
⊢ P (∫ (x : Ω), μ[F | m] x ∂μ)
```

**R5 · `condExp_mul_of_stronglyMeasurable_left`** changes the **context**. Lemma:
`StronglyMeasurable[m] f → Integrable (f * g) μ → Integrable g μ → μ[f * g | m] =ᵐ[μ] f * μ[g | m]`:
the known factor `f` comes out. Placeholders: `{Ω : Type} {m mΩ : MeasurableSpace Ω} (μ : Measure Ω)
(f g : Ω → ℝ)`; arguments `hfm : StronglyMeasurable[m] f` (R1–R3 give the other two).

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, plus `hp : μ[f * g \| m] =ᵐ[μ] f * μ[g \| m]` |

**R6 · `integral_congr_ae`** changes the **goal**. Lemma: `f =ᵐ[μ] g → ∫ a, f a ∂μ = ∫ a, g a ∂μ`. After
R4 the goal is `∫ μ[W * X | m] = ∫ W * μ[X | m]`, and R5 is exactly the a.e. equality it asks for:
`exact integral_congr_ae (…R5…)`. Placeholders: `(f g : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∫ (ω : Ω), f ω ∂μ = ∫ (ω : Ω), g ω ∂μ` | `⊢ f =ᵐ[μ] g` |

### Rewriting the integrand

**R7 · `funext ω`** changes the **goal and the context**: an equation of functions becomes the equation
at a fresh point `ω`. Use it to prove `e : (fun ω => …) = fun ω => …` before `rw [e]`. Placeholders:
`(f g : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ (fun ω => f ω) = fun ω => g ω` | `ω : Ω ⊢ f ω = g ω` |

**R8 · `simp only [Pi.mul_apply]`** changes the **goal**. Lemma: `(f * g) i = f i * g i` (the product of
functions is pointwise). After it, `ring` sees ordinary real products. Placeholders: `(f g : Ω → ℝ) (ω : Ω)`.

| Before | After |
|---|---|
| `⊢ P ((f * g) ω)` | `⊢ P (f ω * g ω)` |

**R9 · `rw [integral_sub hf hg]`** changes the **goal**. Lemma: `Integrable f μ → Integrable g μ →
∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ`. Placeholders: `(f g : Ω → ℝ) (hf : Integrable f μ)
(hg : Integrable g μ)`. With `f := W * X` the integrand must read `(W * X) ω - …`; that is why the plan
rewrites to that form first (R7, R8).

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), f ω - g ω ∂μ)` | `⊢ P (∫ (a : Ω), f a ∂μ - ∫ (a : Ω), g a ∂μ)` |

**R10 · `rw [sub_self]`** changes the **goal**. Lemma: `a - a = 0`. `rw` also closes the goal when the
result is `0 = 0` (it tries `rfl`). Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a - a)` | `⊢ P 0` |

**W2: the error has mean zero** (`W = 1`, a different statement). R1 and R3 give `hZ : Integrable μ[X | m] μ`,
then R9, R4 (left to right), R10; the last `rw [sub_self]` closes the goal: the two integrals differ only in
the bound variable's name.

```lean-goal
⊢ ∫ (ω : Ω), X ω - μ[X | m] ω ∂μ = 0
⊢ ∫ (a : Ω), X a ∂μ - ∫ (a : Ω), μ[X | m] a ∂μ = 0
⊢ ∫ (a : Ω), X a ∂μ - ∫ (x : Ω), X x ∂μ = 0
```

---

## Part 2 · `integral_sq_split` (milestone 2)

Statement: for `X, Y, Z ∈ L²`,
`∫ (X - Y)² = ∫ (X - Z)² + 2 * ∫ (Z - Y)(X - Z) + ∫ (Z - Y)²`. No conditional expectation here; it is
linearity of the integral. Plan: L² differences (R11), integrability of each summand in lambda form
(R12, R2 → R13, R14), then a `calc` (R15): reshape the integrand (R16, R7, `ring`), split (R17, R18).

### Integrability of the expansion, in lambda form

**R11 · `MemLp.sub`** changes the **context**. Lemma: `MemLp f p μ → MemLp g p μ → MemLp (f - g) p μ`;
write `hf.sub hg`. Placeholders: `(f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)`.

| Before | After |
|---|---|
| `⊢ G` | `hd : MemLp (f - g) 2 μ ⊢ G` |

**R12 · `MemLp.integrable_sq`** changes the **context**. Lemma: `MemLp f 2 μ → Integrable (fun x => f x ^ 2) μ`.
For `hd : MemLp (f - g) 2 μ`, state the result with `(f ω - g ω)`: `(f - g) ω` and `f ω - g ω` are equal
by definition, and the second is how the goal's integrand reads. Placeholders: `(f g : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hs : Integrable (fun ω => (f ω - g ω) ^ 2) μ ⊢ G` |

**R13 · `Integrable.const_mul`** changes the **context**. Lemma: `Integrable f μ → ∀ c, Integrable
(fun x => c * f x) μ`; write `hf.const_mul c`. For the cross term, `f` is a product given by R2.
Placeholders: `(f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hc : Integrable (fun ω => c * f ω) μ ⊢ G` |

**R14 · `Integrable.add`** changes the **context**. Lemma: `Integrable f μ → Integrable g μ →
Integrable (f + g) μ`; write `hf.add hg` and state the `have` in lambda form. Placeholders:
`(f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)`.

| Before | After |
|---|---|
| `⊢ G` | `hs : Integrable (fun ω => f ω + g ω) μ ⊢ G` |

### Expanding the square under the integral

**R15 · `calc`** changes the **goal list**: one goal per step. Write the middle expression in full and the
last step as `_ = _ := by …`, so the right side is taken from the goal. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a = c` | `⊢ a = b`, `⊢ b = c` |

**R16 · `congr 1`** changes the **goal**: two integrals against the same `μ` are equal if the integrands
are; the goal becomes an equation of functions, then R7. Placeholders: `(f g : Ω → ℝ)`.

| Before | After `congr 1` | After `funext ω` |
|---|---|---|
| `⊢ ∫ (ω : Ω), f ω + g ω ∂μ = ∫ (ω : Ω), g ω + f ω ∂μ` | `⊢ (fun ω => f ω + g ω) = fun ω => g ω + f ω` | `ω : Ω ⊢ f ω + g ω = g ω + f ω` |

**R17 · `rw [integral_add hf hg]`** changes the **goal**. Lemma: `Integrable f μ → Integrable g μ →
∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ`. `rw` must find `fun a => f a + g a` with `f`, `g` read off
`hf`, `hg`, so these must be stated in lambda form with exactly the goal's summands (R12–R14). For
`A + B + C` (which is `(A + B) + C`), split the outer `+` first, with `hf` for `A + B`. Placeholders:
`(f g : Ω → ℝ) (hf : Integrable (fun ω => f ω ^ 2) μ) (hg : Integrable (fun ω => 2 * g ω) μ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), f ω ^ 2 + 2 * g ω ∂μ)` | `⊢ P (∫ (a : Ω), f a ^ 2 ∂μ + ∫ (a : Ω), 2 * g a ∂μ)` |

**R18 · `rw [integral_const_mul]`** changes the **goal**. Lemma: `∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ`; no
integrability needed. Placeholders: `(f : Ω → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (ω : Ω), c * f ω ∂μ)` | `⊢ P (c * ∫ (a : Ω), f a ∂μ)` |

**W1: a three-term integral.** For `∫ f + g + 3 * k = ∫ f + ∫ g + 3 * ∫ k`: `hfg` by R14, `hk3` by R13,
then `rw [integral_add hfg hk3, integral_add hf hg, integral_const_mul]` (R17, R17, R18) closes it.

---

## Part 3 · `condExp_best_predictor`

Statement: `∫ ω, (X ω - μ[X | m] ω) ^ 2 ∂μ ≤ ∫ ω, (X ω - Y ω) ^ 2 ∂μ` for every `m`-measurable `Y ∈ L²`.
Plan: facts about `Z = μ[X | m]` and `W = Z - Y` (R1, R11, R19 → R20), milestone 1 gives the cross term,
milestone 2 rewrites the right side, R21 drops the zero, R22 → R23 and R24 finish.

**R19 · `stronglyMeasurable_condExp`** changes the **context**: `StronglyMeasurable[m] μ[f | m]`, with no
hypotheses. State the type with `[m]`; the infoview drops it. Placeholders: `{Ω : Type}
{m mΩ : MeasurableSpace Ω} (μ : Measure Ω) (f : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, plus `hc : StronglyMeasurable μ[f \| m]` (meaning `StronglyMeasurable[m]`) |

**R20 · `StronglyMeasurable.sub`** changes the **context**. Lemma: `StronglyMeasurable f →
StronglyMeasurable g → StronglyMeasurable (f - g)`, for one σ-algebra; write `hf.sub hg`.
Placeholders: `{m : MeasurableSpace Ω} (f g : Ω → ℝ) (hf : StronglyMeasurable[m] f)
(hg : StronglyMeasurable[m] g)`.

| Before | After |
|---|---|
| `⊢ G` | `hd : StronglyMeasurable (f - g) ⊢ G` |

**R21 · `rw [mul_zero]`, `rw [add_zero]`** change the **goal**. Lemmas: `a * 0 = 0`, `a + 0 = a`.
After `rw [h0]` turns the cross integral into `0`, these remove the `2 * 0`. Placeholders: `(a b c : ℝ)`.

| Before | After `rw [mul_zero]` | After `rw [add_zero]` |
|---|---|---|
| `⊢ P (a + b * 0 + c)` | `⊢ P (a + 0 + c)` | `⊢ P (a + c)` |

**R22 · `integral_nonneg`** changes the **goal**. Lemma: `0 ≤ f → 0 ≤ ∫ x, f x ∂μ`, where `0 ≤ f` is
pointwise. As a term: `integral_nonneg fun ω => …`. Placeholders: `(f : Ω → ℝ)`.

| Before | After `apply integral_nonneg` | After `intro ω` |
|---|---|---|
| `⊢ 0 ≤ ∫ (ω : Ω), f ω ^ 2 ∂μ` | `⊢ 0 ≤ fun x => f x ^ 2` | `ω : Ω ⊢ 0 ω ≤ (fun x => f x ^ 2) ω` |

**R23 · `sq_nonneg`** **closes** `0 ≤ a ^ 2`: `sq_nonneg a`. It also closes R22's last goal (equal by
definition to `0 ≤ f ω ^ 2`); write `sq_nonneg _`.

**R24 · `linarith`** **closes** a goal that is a linear consequence of the hypotheses (it treats each
integral as an unknown number). Placeholders: `(a b c : ℝ) (h : a = b + c) (hc : 0 ≤ c)`.

| Before | After |
|---|---|
| `h : a = b + c, hc : 0 ≤ c ⊢ b ≤ a` | closed |

**W3: drop the zero term, then compare.** `rw [mul_zero, add_zero] at hs` (R21 in a hypothesis), the
nonnegativity fact by R22 → R23, then R24:

| Before | After `rw … at hs` |
|---|---|
| `⊢ b ≤ a`, with `hs : a = b + 2 * 0 + ∫ (ω : Ω), f ω ^ 2 ∂μ` | `⊢ b ≤ a`, with `hs : a = b + ∫ (ω : Ω), f ω ^ 2 ∂μ` |

---

## Traps

- **Lambda form for `integral_add` / `integral_sub`** (was the card's NOTE). `rw [integral_add hf hg]`
  matches only if `hf`, `hg` describe exactly the goal's summands. Restate them with `have hf :
  Integrable (fun ω => …) μ := …` (R12–R14) before the `rw`.
- **`StronglyMeasurable[m] f` prints as `StronglyMeasurable f`.** The infoview hides the σ-algebra.
  When you write the type, write `[m]`; without it Lean means the ambient `mΩ`, and the fact no longer fits R5.
- **`μ[X | m]` is a function, `μ[X]` is a number.** `μ[X | m] ω` is its value at `ω`.
- **Name the function in `rw [← integral_condExp hm (f := W * X)]`.** Without `(f := …)`, the pattern
  `∫ x, ?f x ∂μ` is ambiguous and `rw` may wrap the wrong integral.
- **The order `{m mΩ : MeasurableSpace Ω}` matters.** The last-declared σ-algebra is the ambient one; keep
  the order of the statement when you write a helper lemma.
- **State `h0`'s type in the main proof.** `have h0 := cross_term_zero hm μ X (μ[X | m] - Y) …` gives
  `h0 : ∫ ω, (μ[X | m] - Y) ω * (X ω - μ[X | m] ω) ∂μ = 0`. After `rw [integral_sq_split …]` the goal reads
  `(μ[X | m] ω - Y ω) * …`; the two are equal by definition but not the same text, so `rw [h0]` fails with
  "did not find an occurrence". Write `have h0 : ∫ ω, (μ[X | m] ω - Y ω) * (X ω - μ[X | m] ω) ∂μ = 0 := …`.
- **Integrability of `X` itself** for R5's third argument: `hX.integrable one_le_two` (R3), not `hX`.
- `have h : T` with no `:= …` makes `T` your next goal instead of adding `h` (TACTIC_STATES, "Adding facts").

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `E[X \| m] ∈ L²` | `hX.condExp one_le_two` | R1 |
| product of two L² functions is L¹ | `hf.integrable_mul hg` | R2 |
| L² → L¹ (finite measure) | `hf.integrable one_le_two` | R3 |
| tower: `∫ F = ∫ μ[F \| m]` | `rw [← integral_condExp hm (f := F)]` | R4 |
| pull out an `m`-measurable factor | `condExp_mul_of_stronglyMeasurable_left hfm hfg hg` | R5 |
| `∫ f = ∫ g` from `f =ᵐ[μ] g` | `exact integral_congr_ae h` | R6 |
| function equation → pointwise | `funext ω` | R7 |
| `(f * g) ω → f ω * g ω` | `simp only [Pi.mul_apply]` | R8 |
| `∫ (f - g) → ∫ f - ∫ g` | `rw [integral_sub hf hg]` | R9 |
| `a - a → 0` | `rw [sub_self]` | R10 |
| `f - g ∈ L²` | `hf.sub hg` | R11 |
| `(f - g)²` integrable | `hd.integrable_sq` | R12 |
| `c * f` integrable | `hf.const_mul c` | R13 |
| `f + g` integrable (lambda form) | `have : Integrable (fun ω => …) μ := hf.add hg` | R14 |
| chain of equalities | `calc a = b := by … _ = _ := by …` | R15 |
| equal integrands → equal integrals | `congr 1; funext ω; ring` | R16, R7 |
| `∫ (f + g) → ∫ f + ∫ g` | `rw [integral_add hf hg]` | R17 |
| `∫ c * f → c * ∫ f` | `rw [integral_const_mul]` | R18 |
| `E[f \| m]` is `m`-measurable | `stronglyMeasurable_condExp` | R19 |
| difference of `m`-measurable | `hf.sub hg` | R20 |
| drop `2 * 0` | `rw [mul_zero, add_zero]` | R21 |
| `0 ≤ ∫ f²` | `integral_nonneg fun ω => sq_nonneg _` | R22, R23 |
| linear finish | `linarith` | R24 |
| see the state | infoview | |
