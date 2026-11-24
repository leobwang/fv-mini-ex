# H052 · Inclusion–exclusion for n events: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `intro`, `exact`, `have`, `rw`, `simp`,
anonymous constructors `⟨_, _⟩`, `∃`/`∀`/`¬`/`∈`. **New here:** Mathlib's finite sets (`Finset`) with
their big operators `∑`/`∏`, `powerset`, `filter`, `erase`; set indicators (`Set.indicator`); indexed
unions and intersections; measures, measurable sets, integrability and the integral `∫ … ∂μ`; the
tactics `by_cases`, `obtain`, `push Not`, `simpa`, `simp_rw`.

**The maths.** For a finite index set `s` and events `Aᵢ` (measurable sets), write `𝟙_B(ω)` for the
indicator: `1` if `ω ∈ B`, else `0`. Three pointwise facts, one per milestone, and one integration:

1. `𝟙_{⋃_{i∈s} Aᵢ}(ω) = 1 - ∏_{i∈s} (1 - 𝟙_{Aᵢ}(ω))`. If `ω` is in some `Aᵢ`, that factor is `0`;
   otherwise every factor is `1`.
2. `∏_{i∈t} 𝟙_{Aᵢ}(ω) = 𝟙_{⋂_{i∈t} Aᵢ}(ω)`. A product of 0/1 values is `1` iff all are `1`.
3. Expand: `∏_{i∈s} (1 - xᵢ) = ∑_{t⊆s} (-1)^{|t|} ∏_{i∈t} xᵢ` (`Finset.prod_sub` with `f = 1`, `g = x`).
   The `t = ∅` term is `1` and cancels the leading `1 -`, so
   `𝟙_{⋃}(ω) = ∑_{∅≠t⊆s} (-1)^{|t|+1} 𝟙_{⋂_{i∈t} Aᵢ}(ω)`.
4. Integrate against `μ`: `∫ 𝟙_B dμ = μ(B)`, and the integral of a finite sum is the sum of integrals.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G`, `Q` are arbitrary propositions or predicates.
- Placeholders are written as Lean binders. `{Ω ι : Type}` are any types: `Ω` the sample space, `ι` the
  index type of the events. A bracket such as `[Zero M]` is a requirement on a type (a *type class*);
  each entry says which familiar types meet it. `[DecidableEq ι]` says equality on `ι` can be decided
  (needed to form `s \ t` and `u.erase a`); every concrete type you know qualifies, and in the exercise it
  is an assumption.
- After a `rw`, Lean often renames a bound variable (`∑ t ∈ …` becomes `∑ x ∈ …`). The meaning is the
  same.
- A hypothesis whose type contains a comma (`h : ∃ i ∈ s, Q i`) gets its own code span, written just
  before the `⊢` span of its state.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `{Ω ι : Type*}`, `Ω : Type u_1` | `Ω`, `ι` are arbitrary types; `Type*` lets each live in its own universe level, which the infoview names `u_1`, `u_2`. Read it as `Type` |
| `inst✝ : DecidableEq ι` | an unnamed instance argument from the statement (here: equality on `ι` is decidable). You never refer to it |
| `Set Ω` | a set of elements of `Ω` (a predicate `Ω → Prop`). `x ∈ S` is membership, `x ∉ S` is `¬(x ∈ S)`, `Set.univ` is all of `Ω` |
| `Finset ι` | a finite set of elements of `ι` (`s`, `t`, `u`) |
| `∑ i ∈ s, f i`, `∏ i ∈ s, f i` | the finite sum / product of `f i` over `i ∈ s` |
| `s.powerset` | the `Finset` of all subsets `t ⊆ s` (its elements are `Finset ι`) |
| `s \ t` | the elements of `s` not in `t` |
| `t.card`, `∅.card` | the number of elements `\|t\|`; `∅` here is the empty `Finset` |
| `t.Nonempty` | `∃ x, x ∈ t` |
| `u.erase a` | `u` with the element `a` removed |
| `∑ t ∈ u with p t, f t` | the sum over `u.filter p`: the elements of `u` satisfying `p`. The exercise writes `s.powerset.filter (·.Nonempty)`, where `(·.Nonempty)` is `fun t => t.Nonempty` |
| `{x ∈ u \| p x}` | the same `u.filter p`, as it is printed inside a hypothesis |
| `if c then a else b` | `a` when `c` holds, else `b`; `c` needs a `Decidable c` instance |
| `S.indicator f x` | `Set.indicator S f x`: `f x` if `x ∈ S`, else `0`. With `f = 1` it is `𝟙_S(x)` |
| `1 x` | the constant function `(1 : Ω → ℝ)` applied to `x`; it equals `1` (R5) |
| `⋃ i ∈ s, A i`, `⋂ i ∈ s, A i` | union / intersection of the `A i` over `i ∈ s`. Internally a double union `⋃ i, ⋃ (_ : i ∈ s), A i`, so the membership lemmas carry a `₂` (R3, R11) |
| `∃ i, ∃ (_ : i ∈ s), Q i` | `∃ i ∈ s, Q i` with the bounded `∃` written out; `⟨i, hi, hq⟩` proves it |
| `⋂ i ∈ ∅, A i` | the intersection of no sets: all of `Ω` (`Set.univ`) |
| `x_1`, `a✝` | names Lean invents. A name with `✝` cannot be typed; name it yourself (`intro i hi`) |
| `case pos`, `case neg` | the two branches of `by_cases` (R1). `case neg.h` is a side goal `rw` added inside the `neg` branch (R8 without its argument) |
| `MeasurableSpace Ω` | a σ-algebra on `Ω`: the family of sets that may be measured |
| `MeasurableSet S` | `S` is in that σ-algebra |
| `Measure Ω`, `μ` | a measure on `Ω`. `μ S` lives in `ℝ≥0∞` (`[0, ∞]`) |
| `μ.real S` | `(μ S).toReal`: the measure as a real number (`∞` would become `0`) |
| `IsFiniteMeasure μ` | `μ Ω < ∞`; every probability measure is one |
| `∫ (x : Ω), f x ∂μ` | the (Bochner) integral of `f : Ω → ℝ` against `μ`. Mathlib defines it as `0` when `f` is not integrable, so the lemmas that move it need `Integrable` hypotheses |
| `Integrable f μ` | `f` is (almost-everywhere strongly) measurable and `∫ \|f\| dμ < ∞` |
| `fun x => c` | the constant function with value `c` |

---

## Part 1 · `indicator_biUnion` (milestone 1)

Statement: `𝟙_{⋃_{i∈s} Aᵢ}(ω) = 1 - ∏_{i∈s} (1 - 𝟙_{Aᵢ}(ω))`, pointwise at one `ω`. Split on whether `ω`
is in some `Aᵢ`.

**R1 · `by_cases h : Q`** changes the **goal list**: one goal becomes two, the first with `h : Q`, the second
with `h : ¬Q`. Works for any proposition `Q` (Mathlib supplies decidability classically). Placeholders:
`(Q G : Prop)`. Here `Q` is `∃ i ∈ s, ω ∈ A i`.

| Before | After |
|---|---|
| `⊢ G` | `h : Q ⊢ G`, `h : ¬Q ⊢ G` |

**R2 · `obtain ⟨i, hi, hx⟩ := h`** changes the **context**: it takes apart `h : ∃ i ∈ s, Q i` into a witness
and its two facts (`∃ i ∈ s, Q i` is `∃ i, i ∈ s ∧ Q i`). Placeholders: `{ι : Type} (s : Finset ι)
(Q : ι → Prop)`.

| Before | After |
|---|---|
| `h : ∃ i ∈ s, Q i` `⊢ G` | `i : ι, hi : i ∈ s, hx : Q i ⊢ G` |

**R3 · `Set.mem_iUnion₂`** changes the **goal**. The lemma is
`x ∈ ⋃ i, ⋃ j, B i j ↔ ∃ i j, x ∈ B i j`; for `⋃ i ∈ s` the inner index `j` is a proof of `i ∈ s`.
As a term, `Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩ : x ∈ ⋃ i ∈ s, B i`, which is how you feed it to R4.
Placeholders: `{Ω ι : Type} (s : Finset ι) (B : ι → Set Ω) (x : Ω)`.

| Before | After |
|---|---|
| `⊢ x ∈ ⋃ j ∈ s, B j` | `⊢ ∃ i, ∃ (_ : i ∈ s), x ∈ B i` |

**R4 · `rw [Set.indicator_of_mem hx]`** changes the **goal**. The lemma is
`x ∈ S → ∀ f, S.indicator f x = f x`. Placeholders: `{Ω M : Type} [Zero M] (S : Set Ω) (f : Ω → M)
(x : Ω)`; `[Zero M]` means `M` has a `0` (`ℝ` does).

| Before | After |
|---|---|
| `hx : x ∈ S ⊢ P (S.indicator f x)` | `⊢ P (f x)` |

**R5 · `Pi.one_apply`** changes the **goal**: `(1 : Ω → ℝ) x = 1`. After R4 with `f = 1` the goal shows
`1 x`; `simp` applies R5 by itself. Placeholders: `{Ω : Type} (x : Ω)`.

| Before | After |
|---|---|
| `⊢ P (1 x)` | `⊢ P 1` |

**R6 · `rw [Finset.prod_eq_zero hi hf]`** changes the **goal**. The lemma is
`i ∈ s → f i = 0 → ∏ j ∈ s, f j = 0`. In the exercise the factor is `1 - (A i).indicator 1 ω`, and the
fact `hf` that it is `0` comes from `(by simp [hω])`. Placeholders: `{ι : Type} (s : Finset ι)
(f : ι → ℝ) (i : ι)`; any `CommMonoidWithZero` (a commutative `*` with `0`, such as `ℝ`) works.

| Before | After |
|---|---|
| `⊢ P (∏ j ∈ s, f j)` | `⊢ P 0` |

**R7 · `push Not at h`** changes the **context**: it pushes `¬` inward, `¬∃ x ∈ s, Q x` → `∀ x ∈ s, ¬Q x`
and `¬∀ x ∈ s, Q x` → `∃ x ∈ s, ¬Q x` (and `¬(x ∈ S)` is printed `x ∉ S`). It is the current name of
`push_neg`, which is deprecated. Placeholders: `{ι : Type} (s : Finset ι) (Q : ι → Prop)`.

| Before | After |
|---|---|
| `h : ¬∃ i ∈ s, Q i` `⊢ G` | `h : ∀ i ∈ s, ¬Q i` `⊢ G` |

**R8 · `rw [Set.indicator_of_notMem hx]`** changes the **goal**. The lemma is
`x ∉ S → ∀ f, S.indicator f x = 0`. Without the argument, `rw [Set.indicator_of_notMem]` rewrites anyway
and adds the side goal `x ∉ S` to the **goal list** (used in Part 2). Placeholders as in R4.

| Before | After |
|---|---|
| `hx : x ∉ S ⊢ P (S.indicator f x)` | `⊢ P 0` |

**R9 · `simpa using h`** **closes** the goal: it simplifies both `h` and the goal with the `simp` set and
then closes the goal with the simplified `h`. Here `simp` turns `x ∉ ⋃ i ∈ s, B i` into
`∀ i ∈ s, x ∉ B i`. Placeholders: `{Ω ι : Type} (s : Finset ι) (B : ι → Set Ω) (x : Ω)`.

| Before | After |
|---|---|
| `h : ∀ i ∈ s, x ∉ B i` `⊢ x ∉ ⋃ i ∈ s, B i` | no goals |

**R10 · `rw [Finset.prod_eq_one hf]`** changes the **goal**. The lemma is
`(∀ i ∈ s, f i = 1) → ∏ i ∈ s, f i = 1`. Build `hf` as `fun i hi => by simp [...]`. Placeholders:
`{ι : Type} (s : Finset ι) (f : ι → ℝ)`; any `CommMonoid` works.

| Before | After |
|---|---|
| `hf : ∀ i ∈ s, f i = 1` `⊢ P (∏ i ∈ s, f i)` | `⊢ P 1` |

Each branch ends with numbers such as `1 - 0 = 1` next to `1 ω`; `simp` closes them (R5).

**W1** (R1, R4, R8): `𝟙_S · 𝟙_S = 𝟙_S`, by a case split on `x ∈ S`. Both branches start from

```lean-goal
⊢ S.indicator 1 x * S.indicator 1 x = S.indicator 1 x
```

and `rw [Set.indicator_of_mem hx]` / `rw [Set.indicator_of_notMem hx]` followed by `simp` closes them.

---

## Part 2 · `prod_indicator` (milestone 2)

Statement: `∏_{i∈t} 𝟙_{Aᵢ}(ω) = 𝟙_{⋂_{i∈t} Aᵢ}(ω)`. Split on whether `ω` is in every `Aᵢ`. Uses R1, R2,
R4–R8, R10 from Part 1 and:

**R11 · `Set.mem_iInter₂`** changes the **goal**. The lemma is
`x ∈ ⋂ i, ⋂ j, B i j ↔ ∀ i j, x ∈ B i j`. As a term, `Set.mem_iInter₂.mpr h : x ∈ ⋂ i ∈ s, B i` for
`h : ∀ i ∈ s, x ∈ B i`. Placeholders: `{Ω ι : Type} (s : Finset ι) (B : ι → Set Ω) (x : Ω)`.

| Before | After |
|---|---|
| `⊢ x ∈ ⋂ i ∈ s, B i` | `⊢ ∀ i ∈ s, x ∈ B i` |

**R12 · `simp only [Set.mem_iInter, not_forall]`** changes the **goal**: `x ∉ ⋂ …` becomes an `∃`.
`Set.mem_iInter : x ∈ ⋂ i, B i ↔ ∀ i, x ∈ B i` (used twice, once per `⋂`) and
`not_forall : (¬∀ x, p x) ↔ ∃ x, ¬p x`. Placeholders as in R11. Close with `exact ⟨i, hi, hx⟩`.

| Before | After |
|---|---|
| `⊢ x ∉ ⋂ j ∈ s, B j` | `⊢ ∃ x_1, ∃ (_ : x_1 ∈ s), x ∉ B x_1` |

---

## Part 3 · `indicator_expand` (milestone 3)

Statement: `𝟙_{⋃_{i∈s} Aᵢ}(ω) = ∑_{t ∈ s.powerset, t ≠ ∅} (-1)^{|t|+1} 𝟙_{⋂_{i∈t} Aᵢ}(ω)`. Rewrite with
milestone 1, expand the product over subsets, use milestone 2 inside the sum, split off `t = ∅`, and
compare the remaining sums term by term.

### Expanding the product

**R13 · `rw [Finset.prod_sub]`** changes the **goal**. The lemma is
`∏ i ∈ s, (f i - g i) = ∑ t ∈ s.powerset, ((-1) ^ t.card * ∏ i ∈ s \ t, f i) * ∏ i ∈ t, g i`. With
`1 - g i`, Lean takes `f` to be the constant `1`, so `∏ i ∈ s \ t, 1` appears. Placeholders:
`{ι : Type} [DecidableEq ι] (s : Finset ι) (g : ι → ℝ)`; any `CommRing` (`ℝ`, `ℤ`, `ℂ`) works.

| Before | After |
|---|---|
| `⊢ P (∏ i ∈ s, (1 - g i))` | `⊢ P (∑ t ∈ s.powerset, ((-1) ^ t.card * ∏ i ∈ s \ t, 1) * ∏ i ∈ t, g i)` |

**R14 · `simp only [Finset.prod_const_one, mul_one]`** changes the **goal**:
`Finset.prod_const_one : ∏ _x ∈ s, 1 = 1`, then `mul_one : a * 1 = a`. `simp` rewrites under the `∑`
binder, `rw` would not (R15). Placeholders as in R13.

| Before | After |
|---|---|
| `⊢ P (∑ t ∈ s.powerset, ((-1) ^ t.card * ∏ _i ∈ s \ t, 1) * ∏ i ∈ t, g i)` | `⊢ P (∑ x ∈ s.powerset, (-1) ^ x.card * ∏ i ∈ x, g i)` |

**R15 · `simp_rw [hfg]`** (or `simp only [hfg]`) changes the **goal**: it rewrites with `hfg : ∀ i, f i = g i`
**under a binder** (`∑ i ∈ s, …`, `∫ x, …`). `rw [hfg]` fails there, because the `i` in `f i` is bound by
the sum (Lean reports "Did not find an occurrence of the pattern"). Use it with milestone 2 inside the sum (put `prod_indicator` in the R14 `simp only`), and with
milestone 3 under the integral in Part 4. Placeholders: `{ι : Type} (s : Finset ι) (f g : ι → ℝ)`.

| Before | After |
|---|---|
| `hfg : ∀ (i : ι), f i = g i` `⊢ P (∑ i ∈ s, f i)` | `⊢ P (∑ x ∈ s, g x)` |

### Splitting off the empty subset

**R16 · `rw [Finset.sum_filter]`** changes the **goal**. The lemma is
`∑ a ∈ s with p a, f a = ∑ a ∈ s, if p a then f a else 0`: a filtered sum becomes a sum over the whole
`Finset` with an `if`. Then both sides of the exercise sum over `s.powerset`. Placeholders:
`{ι : Type} (s : Finset ι) (p : ι → Prop) [DecidablePred p] (f : ι → ℝ)`; `[DecidablePred p]` says `p a`
can be decided for each `a` (`Finset.Nonempty` can).

| Before | After |
|---|---|
| `⊢ P (∑ a ∈ s with p a, f a)` | `⊢ P (∑ a ∈ s, if p a then f a else 0)` |

**R17 · `rw [← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset s)]`** changes the **goal**: the `t = ∅`
term is split off. `Finset.sum_erase_add s f : a ∈ s → ∑ x ∈ s.erase a, f x + f a = ∑ x ∈ s, f x`, used
right to left; `Finset.empty_mem_powerset s : ∅ ∈ s.powerset` is its hypothesis. Placeholders:
`{ι : Type} [DecidableEq ι] (s : Finset ι) (F : Finset ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ t ∈ s.powerset, F t)` | `⊢ P (∑ x ∈ s.powerset.erase ∅, F x + F ∅)` |

**W2** (R17, then `rw [add_comm]`) puts the `∅` term in front:

```lean-goal
⊢ ∑ t ∈ s.powerset, F t = F ∅ + ∑ t ∈ s.powerset.erase ∅, F t
⊢ ∑ x ∈ s.powerset.erase ∅, F x + F ∅ = F ∅ + ∑ t ∈ s.powerset.erase ∅, F t
```

**R18 · `simp only [Finset.card_empty, pow_zero, one_mul]`** changes the **goal**:
`Finset.card_empty : (∅ : Finset ι).card = 0`, `pow_zero : a ^ 0 = 1`, `one_mul : 1 * a = a`.
Placeholders: `{ι : Type} (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((-1) ^ ∅.card * a)` | `⊢ P a` |

**R19 · `simp only [Finset.not_nonempty_empty, if_false]`** changes the **goal**:
`Finset.not_nonempty_empty : ¬(∅ : Finset ι).Nonempty` turns the condition into `False`, and
`if_false : (if False then a else b) = b`. Add `add_zero` (`a + 0 = a`) to clean the `+ 0` this leaves in
the exercise. Placeholders: `{ι : Type} (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (if ∅.Nonempty then a else 0)` | `⊢ P 0` |

**R20 · `simp`** **closes** `(⋂ i ∈ (∅ : Finset ι), B i).indicator f x = f x`: there is no `i ∈ ∅`, so the
intersection is `Set.univ` and every `x` is in it. In the exercise, prove
`(⋂ i ∈ (∅ : Finset ι), A i).indicator (1 : Ω → ℝ) ω = 1` as a `have` (write the type ascriptions out)
and `rw` with it. Placeholders: `{Ω ι : Type} (B : ι → Set Ω) (f : Ω → ℝ) (x : Ω)`.

| Before | After |
|---|---|
| `⊢ (⋂ i ∈ ∅, B i).indicator f x = f x` | no goals |

**R21 · `rw [sub_add_cancel_right]`** changes the **goal**. The lemma is `a - (b + a) = -b` (any additive
group; `ℝ` qualifies). This is where the `∅` term `1` cancels the leading `1 -`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a - (b + a))` | `⊢ P (-b)` |

**R22 · `rw [← Finset.sum_neg_distrib]`** changes the **goal**. The lemma is
`∑ x ∈ s, -f x = -∑ x ∈ s, f x`; right to left, the minus moves inside the sum so both sides are sums over
the same `Finset`. Placeholders: `{ι : Type} (s : Finset ι) (f : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (-∑ i ∈ s, f i)` | `⊢ P (∑ x ∈ s, -f x)` |

### Term by term

**R23 · `refine Finset.sum_congr rfl fun t ht => ?_`** changes the **goal and the context**: two sums over the
same `Finset` are equal if the terms agree on it. `Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) →
s₁.sum f = s₂.sum g`; `rfl` proves `s₁ = s₂`, and `?_` is the termwise goal. Placeholders:
`{ι : Type} (s : Finset ι) (f g : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ i ∈ s, f i = ∑ i ∈ s, g i` | `t : ι, ht : t ∈ s ⊢ f t = g t` |

**R24 · `Finset.ne_of_mem_erase`** changes the **context** (as a `have`): `t ∈ u.erase a → t ≠ a`. In the
exercise `u = s.powerset`, `a = ∅`. Placeholders: `{ι : Type} [DecidableEq ι] (u : Finset (Finset ι))
(t : Finset ι)`.

| Before | After |
|---|---|
| `ht : t ∈ u.erase ∅ ⊢ G` | `hne : t ≠ ∅ ⊢ G` |

**R25 · `Finset.nonempty_iff_ne_empty`** changes the **goal**: `t.Nonempty ↔ t ≠ ∅`. With R24 as a term:
`Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht) : t.Nonempty`. Placeholders:
`{ι : Type} (t : Finset ι)`.

| Before | After |
|---|---|
| `⊢ t.Nonempty` | `⊢ t ≠ ∅` |

**R26 · `rw [if_pos hc]`** changes the **goal**. The lemma is `c → (if c then a else b) = a` (`if_neg` is the
`¬c` version). Placeholders: `(c : Prop) [Decidable c] (hc : c) (a b : ℝ)`.

| Before | After |
|---|---|
| `hc : c ⊢ P (if c then a else b)` | `⊢ P a` |

**R27 · `rw [pow_succ]`** changes the **goal**. The lemma is `a ^ (n + 1) = a ^ n * a` (any monoid). After it
the term goal is `-(x * y) = x * -1 * y` up to names, which `ring` closes. Placeholders: `(a : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

---

## Part 4 · `inclusion_exclusion`

Statement: for a finite measure `μ` and measurable `Aᵢ`,
`μ.real (⋃ i ∈ s, A i) = ∑_{t ∈ s.powerset, t ≠ ∅} (-1)^{|t|+1} μ.real (⋂ i ∈ t, A i)`. Turn the left side
into `∫ 𝟙_{⋃}`, expand the integrand with milestone 3 (R15), swap `∫` and `∑`, and integrate each term.

### Side facts: measurability and integrability

**R28 · `Finset.measurableSet_biUnion`** (and `Finset.measurableSet_biInter`) changes the **goal**: a union
(intersection) over a `Finset` of measurable sets is measurable. The lemma is
`(s : Finset ι) → (∀ b ∈ s, MeasurableSet (B b)) → MeasurableSet (⋃ b ∈ s, B b)`; `_biInter` is the same
with `⋂`. Placeholders:
`{Ω ι : Type} [MeasurableSpace Ω] (s : Finset ι) (B : ι → Set Ω)`.

| Before | After `apply Finset.measurableSet_biUnion` | After `intro i _` |
|---|---|---|
| `⊢ MeasurableSet (⋃ i ∈ s, B i)` | `⊢ ∀ b ∈ s, MeasurableSet (B b)` | `i : ι ⊢ MeasurableSet (B i)` |

**R29 · `integrable_const c`** **closes** `Integrable (fun _ => c) μ` when `[IsFiniteMeasure μ]`.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ Integrable (fun x => c) μ` | no goals |

**R30 · `Integrable.indicator`** changes the **goal list**:
`Integrable f μ → MeasurableSet S → Integrable (S.indicator f) μ`. With `apply`, one goal per hypothesis.
As a term, `(integrable_const (1 : ℝ)).indicator hS : Integrable (S.indicator fun _ => 1) μ`.
Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω) (f : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ Integrable (S.indicator f) μ` | `⊢ Integrable f μ`, `⊢ MeasurableSet S` |

**R31 · `Integrable.const_mul`** changes the **goal**: `Integrable f μ → ∀ c, Integrable (fun x => c * f x) μ`.
As a term: `hf.const_mul c`, or `hf.const_mul _` and let Lean find `c`. Placeholders as in R30, `(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ Integrable (fun x => c * f x) μ` | `⊢ Integrable f μ` |

### Integrals

**R32 · `integral_indicator_one`** changes the **goal**. The lemma is
`MeasurableSet S → ∫ x, S.indicator 1 x ∂μ = μ.real S`. Right to left (`rw [← integral_indicator_one hS]`)
it turns a measure into an integral; left to right it turns it back. Placeholders:
`{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω)`.

| Before | After |
|---|---|
| `hS : MeasurableSet S ⊢ P (μ.real S)` | `⊢ P (∫ (x : Ω), S.indicator 1 x ∂μ)` |

**R33 · `rw [integral_finsetSum s hf]`** changes the **goal**: the integral of a finite sum is the sum of the
integrals, given `hf : ∀ i ∈ s, Integrable (f i) μ`. Placeholders: `{Ω ι : Type} [MeasurableSpace Ω]
(μ : Measure Ω) (s : Finset ι) (f : ι → Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : Ω), ∑ i ∈ s, f i x ∂μ)` | `⊢ P (∑ i ∈ s, ∫ (a : Ω), f i a ∂μ)` |

**R34 · `rw [integral_const_mul]`** changes the **goal**: `∫ x, c * f x ∂μ = c * ∫ x, f x ∂μ`. No
integrability needed. Placeholders: `{Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ) (f : Ω → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : Ω), c * f x ∂μ)` | `⊢ P (c * ∫ (a : Ω), f a ∂μ)` |

**W3: expected number of events that occur.** `rw [integral_finsetSum s]` without `hf` leaves the
integrability goal second; then R23 and R32 on the first, R30 + R29 on the second:

```lean-goal
⊢ ∫ (x : Ω), ∑ i ∈ s, (B i).indicator 1 x ∂μ = ∑ i ∈ s, μ.real (B i)
⊢ ∑ i ∈ s, ∫ (a : Ω), (B i).indicator 1 a ∂μ = ∑ i ∈ s, μ.real (B i)
⊢ ∀ i ∈ s, Integrable ((B i).indicator 1) μ
```

**W4** (R34, R32):

```lean-goal
⊢ ∫ (x : Ω), c * S.indicator 1 x ∂μ = c * μ.real S
⊢ c * ∫ (a : Ω), S.indicator 1 a ∂μ = c * μ.real S
```

---

## Traps

- `rw` cannot rewrite under a binder (`∑ t ∈ …, …`, `∫ x, …`, `fun x => …`): use `simp only [h]` or
  `simp_rw [h]` (R15). In Part 4, `simp_rw [indicator_expand s A]` rewrites inside the integral.
- `rw [← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset s)]` fixes the summand `f` at the first sum it
  matches and rewrites only that sum. Both sides of milestone 3 sum over `s.powerset`, with different
  summands: write the rewrite twice.
- `integrable_const (1 : ℝ)` is about `fun _ => 1`, while the goal has the function `1`. They are equal by
  definition, so `exact` and dot notation (`.indicator`, `.const_mul`) accept it, but a `rw` whose argument
  is such a term may fail to find its pattern. State the integrability fact as a `have` with its type
  written out, e.g. `∀ t ∈ s.powerset.filter (·.Nonempty), Integrable (fun ω => … ) μ`, or let `rw` leave
  the side goal (W3).
- Write the ascriptions in `have`s: `(1 : Ω → ℝ)`, `(∅ : Finset ι)`, `(-1 : ℝ)`. Without them Lean may elaborate
  `1` or `∅` in another type and `rw` finds nothing.
- `μ S` is an extended non-negative real (`ℝ≥0∞`); the exercise uses `μ.real S : ℝ`, which is what
  `integral_indicator_one` produces.
- `push_neg` is deprecated in this Mathlib; write `push Not at h` (R7).
- The milestones are stated pointwise (at one `ω`); the integral needs a function. `simp_rw` with the
  milestone applied to `s A` rewrites the integrand for every `ω` at once.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| case split on a proposition | `by_cases h : Q` | R1 |
| unpack `∃ i ∈ s, Q i` | `obtain ⟨i, hi, hx⟩ := h` | R2 |
| `x ∈ ⋃ i ∈ s, B i` from a witness | `Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩` | R3 |
| `x ∈ ⋂ i ∈ s, B i` from `∀` | `Set.mem_iInter₂.mpr h` | R11 |
| indicator at a member / non-member | `rw [Set.indicator_of_mem hx]` / `rw [Set.indicator_of_notMem hx]` | R4, R8 |
| `1 x → 1` | `simp` (`Pi.one_apply`) | R5 |
| product with a zero factor | `rw [Finset.prod_eq_zero hi (by simp [hx])]` | R6 |
| product of ones | `rw [Finset.prod_eq_one fun i hi => by simp [...]]` | R10 |
| `¬∃` → `∀ ¬`, `¬∀` → `∃ ¬` | `push Not at h` | R7 |
| `x ∉ ⋃ …` from `∀ i ∈ s, x ∉ B i` | `simpa using h` | R9 |
| `x ∉ ⋂ …` → `∃` | `simp only [Set.mem_iInter, not_forall]` | R12 |
| `∏ (1 - g i)` → sum over subsets | `rw [Finset.prod_sub]` | R13 |
| `∏ 1`, `* 1` | `simp only [Finset.prod_const_one, mul_one]` | R14 |
| rewrite under `∑` / `∫` | `simp_rw [h]` / `simp only [h]` | R15 |
| filtered sum → `if` sum | `rw [Finset.sum_filter]` | R16 |
| split off `t = ∅` | `rw [← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset s)]` | R17 |
| `(-1) ^ ∅.card * a`, `if ∅.Nonempty …` | `simp only [Finset.card_empty, pow_zero, one_mul, Finset.not_nonempty_empty, if_false, add_zero]` | R18, R19 |
| indicator of `⋂ i ∈ ∅` | `simp` | R20 |
| `a - (b + a) → -b` | `rw [sub_add_cancel_right]` | R21 |
| `-∑ → ∑ -` | `rw [← Finset.sum_neg_distrib]` | R22 |
| compare sums termwise | `refine Finset.sum_congr rfl fun t ht => ?_` | R23 |
| `t.Nonempty` from `t ∈ u.erase ∅` | `Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht)` | R24, R25 |
| resolve an `if` | `rw [if_pos hc]` | R26 |
| `a ^ (n + 1) → a ^ n * a` | `rw [pow_succ]` | R27 |
| finite union / intersection measurable | `Finset.measurableSet_biUnion s fun i _ => hA i` (`_biInter`) | R28 |
| `c * 𝟙_S` integrable | `((integrable_const (1 : ℝ)).indicator hS).const_mul c` | R29–R31 |
| `μ.real S ↔ ∫ 𝟙_S` | `rw [← integral_indicator_one hS]` / `rw [integral_indicator_one hS]` | R32 |
| `∫ ∑ → ∑ ∫` | `rw [integral_finsetSum s hInt]` | R33 |
| `∫ c * f → c * ∫ f` | `rw [integral_const_mul]` | R34 |
| see the state | infoview | |
