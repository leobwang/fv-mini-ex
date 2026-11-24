# M101 · Two independent dice (product measure): cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's measure theory and probability:
measures with values in `ENNReal`, the product measure `Measure.pi`, probability mass functions (`PMF`),
independence (`⟂ᵢ`, `iIndepFun`), and finite sets (`Finset`) with their sums, products and counts.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`apply`/`exact`. It says what changes
(**goal**, **context**, or **goal list**), gives the lemma's statement, lists the placeholders with their
types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` (or `Q`) is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommMonoid M]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- A state containing `|` (set-builder braces) cannot sit in a table code cell; it is written plainly in the
  table and repeated, checked, in the ```` ```lean-goal ```` block below it.

## Reading the goals

| You see | It means |
|---|---|
| `ω : Fin 2 → Fin 6` | one outcome of two rolls: `ω 0` is the first roll, `ω 1` the second, each in `Fin 6 = {0, …, 5}` |
| `↑(ω 0)` | the roll cast to `ℕ` (`Fin.val`), a number `0..5`; the die shows `↑(ω 0) + 1` pips |
| `Measure α` | a measure on `α`: it assigns each set `s : Set α` a size `μ s : ENNReal` |
| `ENNReal` (also written `ℝ≥0∞`) | the extended non-negative reals `[0, ∞]`, where measures take values |
| `a.toReal`, `ENNReal.toReal a` | `a : ENNReal` as a real number (`∞` is sent to `0`) |
| `μ.real s` | `(μ s).toReal`: the measure of `s` as a real number (R11) |
| `PMF α` | a probability mass function: weights `p a : ENNReal` on the points of `α` summing to 1 |
| `PMF.uniformOfFintype α` | the uniform PMF on a finite type: every point has weight `(card α)⁻¹` |
| `p.toMeasure` | the measure of a PMF: `p.toMeasure s` is the total weight of `s` |
| `Measure.pi μ`, `(Measure.pi μ) {f}` | the product measure on `ι → α`: coordinate `i` has law `μ i`, coordinates independent |
| `X ⟂ᵢ[μ] Y` | `IndepFun X Y μ`: the random variables `X`, `Y` are independent under `μ` |
| `iIndepFun f μ` | the family `f i` (`i : ι`) is mutually independent under `μ` |
| `Measurable f`, `AEMeasurable f μ` | preimages of measurable sets are measurable (everywhere / outside a `μ`-null set) |
| `inst✝ : …` | an unnamed type-class hypothesis, such as `IsProbabilityMeasure (μ i)` |
| `{ω \| p ω}` | **either** a `Set` (set-builder) **or** the `Finset` `Finset.univ.filter p`: both print this way |
| `↑s` (`s : Finset α`) | the finite set `s` cast to a `Set α`. A `↑` in front of `{ω \| …}` marks the Finset one |
| `Finset.filter p Finset.univ` | the same Finset, printed this way when `p` is a variable |
| `{x}` | the singleton set containing only `x` (a `Set`) |
| `Finset.univ` | the `Finset` of all elements of a finite type |
| `s.card`, `Finset.univ.card`, `Fintype.card α` | the number of elements of `s`, of all of `α` |
| `∑ x ∈ s, f x`, `∏ i, f i` | a sum over the Finset `s`, a product over all `i` |
| `∑ x with p x, f x` | the sum over `Finset.univ.filter p` |
| `n • a` (`n : ℕ`) | `a + ⋯ + a`, `n` times |

---

## Part 1 · `rolls_indep`

Statement: under `twoDice` the first roll `ω ↦ ω 0` and the second roll `ω ↦ ω 1` are independent. Route:
the whole family of coordinates is mutually independent (R1, with measurability from R2 and R3); then pick
coordinates 0 and 1 (R4).

**R1 · `iIndepFun_pi`** changes the **goal**: the lemma is
`(∀ i, AEMeasurable (X i) (μ i)) → iIndepFun (fun i ω => X i (ω i)) (Measure.pi μ)`, so after `apply` only the
measurability premise is left. Placeholders: `{ι Ω 𝓧 : Type} [Fintype ι]` (finitely many coordinates, as
`Fin 2`), `[MeasurableSpace Ω] [MeasurableSpace 𝓧]` (σ-algebras; `Fin n` and `Bool` have them),
`(μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]` (each `μ i` has total mass 1; a `PMF`'s
`toMeasure` does), `(X : ι → Ω → 𝓧)`. To read off the coordinates themselves take `X i = id`, i.e.
`(X := fun _ x => x)`: then `X i (ω i)` is `ω i`. `f (μ := m) (X := g) h` fills implicit arguments by name;
Lean can often infer them, but naming them makes the instance explicit.

| Before | After `apply iIndepFun_pi` |
|---|---|
| `⊢ iIndepFun (fun i ω => X i (ω i)) (Measure.pi μ)` | `⊢ ∀ (i : ι), AEMeasurable (X i) (μ i)` |

**R2 · `Measurable.aemeasurable`** changes the **goal**: the lemma is `Measurable f → AEMeasurable f μ`.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)`. In term mode: `measurable_id.aemeasurable`.

| Before | After `apply Measurable.aemeasurable` |
|---|---|
| `⊢ AEMeasurable (fun x => x) μ` | `⊢ Measurable fun x => x` |

**R3 · `measurable_id`** **closes** `Measurable id`; `fun x => x` is `id` by definition, so it closes the
goal of R2 too.

| Before | After `exact measurable_id` |
|---|---|
| `⊢ Measurable fun x => x` | no goals |

**R4 · `iIndepFun.indepFun`** changes the **goal**: the lemma is `iIndepFun f μ → i ≠ j → f i ⟂ᵢ[μ] f j`;
written `hf.indepFun` for `hf : iIndepFun f μ`. Placeholders: `{ι Ω β : Type} (μ : Measure Ω)
(f : ι → Ω → β) (i j : ι)`. The side goal `(0 : Fin 2) ≠ 1` is closed by `decide`.

| Before | After `apply hf.indepFun` |
|---|---|
| `⊢ f i ⟂ᵢ[μ] f j` | `⊢ i ≠ j` |

**W1** in `guide.lean` chains R1 → R2, R3 → R4 → `decide` for three coin tosses `Fin 3 → Bool`, once as a
term and once with tactics. With tactics, build the family's fact first with `have hf := iIndepFun_pi (μ := …)
(X := …) (fun _ => measurable_id.aemeasurable)`; it reads `hf : iIndepFun (fun i ω => ω i) (Measure.pi fun x =>
coin)`. Then `apply hf.indepFun` leaves the side goal, and `decide` closes it:

```lean-goal
⊢ (fun ω => ω 0) ⟂ᵢ[threeCoins] fun ω => ω 2
⊢ 0 ≠ 2
```

`apply iIndepFun.indepFun` or `apply iIndepFun_pi` straight on the problem's goal **fails** ("could not
unify"): Lean cannot guess the family `f` (or `X`) from `fun ω => ω 0`. Name the arguments and build `hf`
first.

---

## Part 2 · `prob_sum_seven`

Statement: the event "total pips `= 7`" has probability `1/6` under `twoDice`. Route: write the event as a
`Finset` of outcomes (R5–R7), split its measure into a sum of point masses (R11, R12), compute one point mass
`6⁻¹ * 6⁻¹ = 6⁻¹ ^ 2` (R13, R8, R9, R14, R15), count the 6 outcomes (R10, R16), and convert to `ℝ`
(R17–R21, `norm_num`). Prove the three facts (`hs`, `hdie`, `hcard`) with `have` first.

### The event as a finite set (`hs`)

**R5 · `ext x`** (lemma `Set.ext`) changes the **goal and the context**: two sets are equal when they have the
same members. Placeholders: `{α : Type} (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ s = t` | `x : α ⊢ x ∈ s ↔ x ∈ t` |

**R6 · `Set.mem_setOf_eq`** changes the **goal**: `x ∈ {y | p y} = p x`. Placeholders: `{α : Type}
(p : α → Prop) (x : α)`. `simp` applies it by itself.

| Before | After |
|---|---|
| ⊢ Q (x ∈ {y \| p y}) | `⊢ Q (p x)` |

```lean-goal
⊢ Q (x ∈ {y | p y})
⊢ Q (p x)
```

**R7 · `Finset.coe_filter`, then R6, then `Finset.mem_univ`, `true_and`** change the **goal**:
`↑(Finset.filter p s) = {x | x ∈ s ∧ p x}`, and every `x` is in `Finset.univ`. Placeholders: `{α : Type}
[Fintype α]` (finitely many elements, as `Fin 2 → Fin 6`), `(p : α → Prop) [DecidablePred p]` (`p x` can be
computed to true/false, as an equation of naturals can). `simp` applies all of them by itself, so after R5 a
plain `simp` closes `hs`.

| Before | After `rw [Finset.coe_filter]` | After `rw [Set.mem_setOf_eq]` | After `simp only [Finset.mem_univ, true_and]` |
|---|---|---|---|
| `⊢ Q (x ∈ ↑(Finset.filter p Finset.univ))` | ⊢ Q (x ∈ {x \| x ∈ Finset.univ ∧ p x}) | `⊢ Q (x ∈ Finset.univ ∧ p x)` | `⊢ Q (p x)` |

```lean-goal
⊢ Q (x ∈ ↑(Finset.filter p Finset.univ))
⊢ Q (x ∈ {x | x ∈ Finset.univ ∧ p x})
⊢ Q (x ∈ Finset.univ ∧ p x)
⊢ Q (p x)
```

### The mass of one face (`hdie`)

**R8 · `PMF.toMeasure_apply_singleton`** changes the **goal list**: the lemma is
`MeasurableSet {a} → p.toMeasure {a} = p a`, so `rw` rewrites the goal and adds the side goal
`MeasurableSet {a}`, which `measurableSet_singleton a` closes (or pass it: `rw [PMF.toMeasure_apply_singleton
p a (measurableSet_singleton a)]`). Placeholders: `{α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]`
(every point is a measurable set; true for `Fin n`, `Bool` and their function types), `(p : PMF α) (a : α)`.

| Before | After |
|---|---|
| `⊢ P (p.toMeasure {a})` | `⊢ P (p a)`, `⊢ MeasurableSet {a}` |

**R9 · `PMF.uniformOfFintype_apply`** changes the **goal**: `PMF.uniformOfFintype α a = (↑(Fintype.card α))⁻¹`.
Placeholders: `{α : Type} [Fintype α] [Nonempty α] (a : α)`. For `α = Fin 6`, `Fintype.card (Fin 6)` is `6`
(`Fintype.card_fin`, R15).

| Before | After |
|---|---|
| `⊢ P ((PMF.uniformOfFintype α) a)` | `⊢ P (↑(Fintype.card α))⁻¹` |

`simp [die]` does R8, R9 and the card computation by itself (W2 shows it on a coin).

### The count (`hcard`)

**R10 · `decide`** **closes** `(Finset.univ.filter p).card = n` when the type is finite and `p` is decidable:
it lists all outcomes (36 maps `Fin 2 → Fin 6` here) and counts. The goal prints with the Finset braces:

| Before | After |
|---|---|
| ⊢ {ω \| ω 0 = ω 1}.card = 3 | no goals |

```lean-goal
⊢ {ω | ω 0 = ω 1}.card = 3
```

### From `μ.real` to a sum of point masses

**R11 · `measureReal_def`** changes the **goal**: `μ.real s = (μ s).toReal`. Placeholders: `{α : Type}
[MeasurableSpace α] (μ : Measure α) (s : Set α)`.

| Before | After |
|---|---|
| `⊢ P (μ.real s)` | `⊢ P (μ s).toReal` |

After R11, `rw [hs]` replaces the `Set` event by `↑` of the Finset; that is what R12 needs.

**R12 · `rw [← sum_measure_singleton]`** changes the **goal**: the lemma is `∑ x ∈ s, μ {x} = μ ↑s`, and `←`
turns the measure of a finite set into the sum of its point masses. Placeholders: `{α : Type}
[MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α) (s : Finset α)`.

| Before | After |
|---|---|
| `⊢ P (μ ↑s)` | `⊢ P (∑ x ∈ s, μ {x})` |

### One outcome's mass

Here the goal is `(∑ x with …, twoDice {x}).toReal = 1 / 6`. The point mass sits under the `∑` binder (it
mentions the bound `x`), and `rw` cannot rewrite there ("did not find an occurrence of the pattern"). So the unfolding of `twoDice`, R13, `hdie`, R14 and R15 all go into **one** `simp only [twoDice,
…]`, which does rewrite under binders. After it the summand is `6⁻¹ ^ 2`; outside the binder `rw` works again
(R16, `hcard`).

**R13 · `Measure.pi_singleton`** changes the **goal**: `Measure.pi μ {f} = ∏ i, μ i {f i}` (a point of the
product has mass the product of its coordinates' masses). Placeholders: `{ι α : Type} [Fintype ι]
[MeasurableSpace α] (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)]` (every finite measure qualifies) `(f : ι → α)`.

| Before | After |
|---|---|
| `⊢ P ((Measure.pi μ) {f})` | `⊢ P (∏ i, (μ i) {f i})` |

Then `hdie` turns every `die {x i}` into `6⁻¹`.

**R14 · `Finset.prod_const`** changes the **goal**: `∏ _x ∈ s, b = b ^ s.card`. Placeholders: `{ι M : Type}
[CommMonoid M]` (commutative `*` with `1`; `ENNReal`, `ℝ`, `ℕ` qualify) `(s : Finset ι) (b : M)`.

| Before | After |
|---|---|
| `⊢ P (∏ _x ∈ s, b)` | `⊢ P (b ^ s.card)` |

**R15 · `Finset.card_univ`, then `Fintype.card_fin`** change the **goal**: `Finset.univ.card = Fintype.card α`
and `Fintype.card (Fin n) = n`. Placeholders: `(n : ℕ)`.

| Before | After `rw [Finset.card_univ]` | After `rw [Fintype.card_fin]` |
|---|---|---|
| `⊢ P Finset.univ.card` | `⊢ P (Fintype.card (Fin n))` | `⊢ P n` |

### The count enters

**R16 · `Finset.sum_const`** changes the **goal**: `∑ _x ∈ s, b = s.card • b`. Placeholders: `{ι M : Type}
[AddCommMonoid M]` (commutative `+` with `0`; `ENNReal`, `ℝ` qualify) `(s : Finset ι) (b : M)`. Then `hcard`
replaces `s.card` by `6`.

| Before | After |
|---|---|
| `⊢ P (∑ _x ∈ s, b)` | `⊢ P (s.card • b)` |

### From `ENNReal` to `ℝ`

**R17 · `ENNReal.toReal_nsmul`** changes the **goal**: `(n • a).toReal = n • a.toReal`. Placeholders:
`(n : ℕ) (a : ENNReal)`.

| Before | After |
|---|---|
| `⊢ P (n • a).toReal` | `⊢ P (n • a.toReal)` |

**R18 · `ENNReal.toReal_pow`** changes the **goal**: `(a ^ n).toReal = a.toReal ^ n`.

| Before | After |
|---|---|
| `⊢ P (a ^ n).toReal` | `⊢ P (a.toReal ^ n)` |

**R19 · `ENNReal.toReal_inv`** changes the **goal**: `a⁻¹.toReal = a.toReal⁻¹` (it holds even at `0` and `∞`,
because `0⁻¹ = ∞` in `ENNReal` and both sides become `0`). `simp` does not use it unless you name it.

| Before | After |
|---|---|
| `⊢ P a⁻¹.toReal` | `⊢ P a.toReal⁻¹` |

**R20 · `ENNReal.toReal_ofNat`** changes the **goal**: a numeral `≥ 2` in `ENNReal` becomes the same numeral
in `ℝ`. (`ENNReal.toReal 5` is how `(5 : ENNReal).toReal` prints.)

| Before | After |
|---|---|
| `⊢ P (ENNReal.toReal 5)` | `⊢ P 5` |

**R21 · `nsmul_eq_mul`** changes the **goal**: `n • a = ↑n * a`. Placeholders: `(n : ℕ) (a : ℝ)` (any semiring).

| Before | After |
|---|---|
| `⊢ P (n • a)` | `⊢ P (↑n * a)` |

`simp [ENNReal.toReal_inv]` applies R18–R21 by itself (plus `inv_pow` and `1 / a = a⁻¹`), and `norm_num`
finishes the arithmetic.

### Worked combination W3 (three coins, "toss 0 = toss 1", probability 1/2)

After `have hs …, have hcoin …, have hcard …` the chain runs:

```lean-goal
⊢ threeCoins.real {ω | ω 0 = ω 1} = 1 / 2
⊢ (∑ x with x 0 = x 1, threeCoins {x}).toReal = 1 / 2
⊢ (4 • 2⁻¹ ^ 3).toReal = 1 / 2
⊢ 4 • (2⁻¹ ^ 3).toReal = 1 / 2
⊢ 4 * (2 ^ 3)⁻¹ = 2⁻¹
```

(after `rw [measureReal_def, hs, ← sum_measure_singleton]`; after the `simp only [threeCoins,
Measure.pi_singleton, hcoin, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.sum_const,
hcard]`; after R17; after `simp [ENNReal.toReal_inv]`; then `norm_num` closes it.)

---

## Traps

- `{ω | …}` prints the same for a `Set` and for the `Finset` `Finset.univ.filter …`. A `↑` in front, a
  `.card` after, or `∑ x with …` tells you it is the Finset.
- In `hs`, copy the event's predicate exactly as the spec writes it (`((ω 0 : ℕ) + 1) + ((ω 1 : ℕ) + 1) = 7`)
  and give `ω` its type in both sides (`fun ω : Fin 2 → Fin 6 => …`); otherwise `rw [hs]` finds no match.
- `rw [PMF.toMeasure_apply_singleton]` leaves the side goal `MeasurableSet {a}` (R8). `simp [die]` avoids it.
- `decide` works on the count (finite type, decidable predicate) but not on goals in `ℝ` or `ENNReal`; those
  need `simp`/`norm_num`.
- `twoDice` is a name: unfold it (`simp only [twoDice]`) so `Measure.pi_singleton` can see `Measure.pi`.
- `rw` does not rewrite under a binder: inside `∑ x with …, twoDice {x}` use `simp only [twoDice,
  Measure.pi_singleton, hdie, …]`, not `rw [Measure.pi_singleton]`.
- `apply iIndepFun.indepFun` (or `apply iIndepFun_pi`) on the goal fails to unify; build
  `hf := iIndepFun_pi (μ := …) (X := …) (…)` first, then `hf.indepFun` (W1).
- Plain `simp` does not move `toReal` through `⁻¹`; name `ENNReal.toReal_inv` (R19).
- `1 / 6` becomes `6⁻¹` under `simp`; `norm_num` closes the remaining `6 * (6 ^ 2)⁻¹ = 6⁻¹`.
- `iIndepFun.indepFun` needs a proof of `(0 : Fin 2) ≠ 1`: `by decide`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| coordinates of `Measure.pi μ` independent | `iIndepFun_pi (μ := …) (X := fun _ x => x) h` | R1 |
| `AEMeasurable id μ` | `measurable_id.aemeasurable` | R2, R3 |
| two members of an independent family | `hf.indepFun (by decide)` | R4 |
| set equality | `ext ω; simp` | R5–R7 |
| `p.toMeasure {a}` → `p a` | `rw [PMF.toMeasure_apply_singleton p a (measurableSet_singleton a)]` | R8 |
| uniform weight | `rw [PMF.uniformOfFintype_apply]`, or `simp [die]` for both | R9 |
| count outcomes | `decide` | R10 |
| `μ.real s` → `(μ s).toReal` | `rw [measureReal_def]` | R11 |
| `μ ↑s` → sum of point masses | `rw [← sum_measure_singleton]` | R12 |
| mass of a point of a product | `simp only [Measure.pi_singleton]` | R13 |
| `∏` / `∑` of a constant | `Finset.prod_const` / `Finset.sum_const` | R14, R16 |
| `Finset.univ.card` for `Fin n` | `Finset.card_univ, Fintype.card_fin` | R15 |
| `toReal` through `•`, `^`, `⁻¹`, numerals | `rw [ENNReal.toReal_nsmul]`, then `simp [ENNReal.toReal_inv]` | R17–R21 |
| final arithmetic | `norm_num` | |
| see the state | infoview | |
