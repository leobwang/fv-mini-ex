# H054 · Fixed points of a random permutation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's finite sets (`Finset`, `filter`,
`card`, big sums `∑`), permutations (`Equiv.Perm`, `Equiv.swap`), probability mass functions (`PMF`),
the extended non-negative reals `ENNReal`, and the integral `∫ … ∂μ` as an expectation.

**The mathematics.** Write $\mathbf 1[\cdot]$ for the indicator (1 if true, 0 if false) and $S_n$ for the
$n!$ permutations of $\{0,\dots,n-1\}$. Under the uniform law each $\sigma$ has probability $1/n!$, so

$$\mathbb E[\#\mathrm{Fix}] = \frac{1}{n!}\sum_{\sigma\in S_n}\sum_{i}\mathbf 1[\sigma i = i]
= \frac{1}{n!}\sum_{i}\#\{\sigma \mid \sigma i = i\} = \frac{1}{n!}\cdot n\cdot\frac{n!}{n} = 1 .$$

The middle step swaps the two sums (double counting, Part 3). The value $\#\{\sigma \mid \sigma i = i\} = n!/n$
comes from splitting $S_n$ by the value $\sigma i = j$ (Part 2): the $n$ classes all have the same size
(Part 1), because $\sigma \mapsto \mathrm{swap}(j,k)\circ\sigma$ is a bijection from class $j$ to class $k$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Group G]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Equiv.Perm α` | the permutations of `α` (bijections `α → α`); `σ x` applies `σ` to `x` |
| `σ * τ` | composition: `(σ * τ) x = σ (τ x)` (R3). `1` is the identity permutation |
| `(Equiv.swap a b) x` | the transposition exchanging `a` and `b`: sends `a ↦ b`, `b ↦ a`, fixes the rest |
| `Finset α` | a finite set of elements of `α`. `Finset.univ` is all of a finite type `α` |
| `Finset.filter p s` | the elements of `s` satisfying `p`. With a `fun` for `p` it prints as `{a ∈ s \| p a}`, and as `{x \| p x}` when `s = Finset.univ`. This is a `Finset`, not a `Set` |
| `s.card` | the number of elements of `s` (Mathlib docs write `#s`; that notation needs `open Finset`) |
| `∑ x ∈ s, f x`, `∑ x, f x` | finite sum over `s`, or over all of `Finset.univ`. `s.sum g` is `∑ x ∈ s, g x` printed without the binder |
| `Fintype.card α` | the number of elements of a finite type `α` (`Fintype α` = "α is finite, with a list of its elements") |
| `n.factorial` | `n!` |
| `ENNReal` | the extended non-negative reals `[0, ∞]` (Mathlib docs write `ℝ≥0∞`); probabilities live here |
| `x.toReal` | `ENNReal → ℝ`, the identity on finite values and `∞ ↦ 0` |
| `PMF α` | a probability mass function: `p : α → ENNReal` with `∑ p a = 1`; `p a` is the probability of `a` |
| `PMF.uniformOfFintype α` | the uniform PMF: every `a` gets `(Fintype.card α)⁻¹` (needs `Nonempty α`) |
| `p.toMeasure` | the probability measure of `p` |
| `∫ (a : α), f a ∂μ` | the integral of `f` against `μ`; for a probability measure, the expectation `E[f]` |
| `↑n` | `n : ℕ` cast into `ℝ` or into `ENNReal` (the target type is the surrounding one) |
| `n • a` | `n`-fold sum `a + ⋯ + a` (`n : ℕ`); `smul_eq_mul` / `nsmul_eq_mul` turn it into a product |
| `if c then 1 else 0` | the indicator of the proposition `c` |
| `Set.MapsTo f ↑s ↑t` | `∀ x, x ∈ s → f x ∈ t`; `↑s` is the finset `s` seen as a `Set` |
| `∃ a, ∃ (_ : a ∈ s), f a = b` | "some `a ∈ s` has `f a = b`" (R8) |
| `case hi`, `case i_inj`, `case i_surj` | the three goals after `Finset.card_bij` (R1) |
| `x⁻¹` | the inverse `1 / x`; in `ENNReal`, `0⁻¹ = ∞` |
| `case i_surj.refine_2` | the second `?_` goal left by `refine` inside the `i_surj` goal |
| `inst✝ : DecidableEq α`, `ha₁✝ : a ∈ s` | a hypothesis with no usable name (an instance, or one you introduced as `_`); it is still used automatically |
| `∑ x, ∑ x_1, …` | `x_1` is a bound variable Lean renamed to avoid a clash with `x` |

---

## Part 1 · `card_apply_eq` (MILESTONE)

Statement: for fixed `i j k : Fin n`, `#{σ | σ i = j} = #{σ | σ i = k}`. Proof: the map
`σ ↦ Equiv.swap j k * σ` is a bijection between the two sets.

**R1 · `apply Finset.card_bij (fun a _ => f a)`** changes the **goal list**: `s.card = t.card` becomes three
goals: `f` maps `s` into `t`, `f` is injective on `s`, `f` hits every element of `t`. The function takes the
element and a proof that it is in `s` (ignored with `_`). Lemma:
`Finset.card_bij (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t) (i_inj : …) (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) : s.card = t.card`.
Placeholders: `{α β : Type} (s : Finset α) (t : Finset β) (f : α → β)`. In the exercise, open each goal with
`intro` (TACTIC_STATES does not cover `intro`; it moves `∀ x ∈ s,` into the context as `x`, `hx : x ∈ s`).

| Before | After |
|---|---|
| `⊢ s.card = t.card` | `⊢ ∀ a ∈ s, f a ∈ t`, `⊢ ∀ a₁ ∈ s, ∀ a₂ ∈ s, f a₁ = f a₂ → a₁ = a₂`, `⊢ ∀ b ∈ t, ∃ a, ∃ (_ : a ∈ s), f a = b` |

**R2 · `simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢`** changes the **context and the
goal**: membership in a filtered `Finset.univ` becomes the predicate itself.
`Finset.mem_filter : a ∈ Finset.filter p s ↔ a ∈ s ∧ p a`, `Finset.mem_univ : a ∈ Finset.univ` (so it becomes
`True`), `true_and : True ∧ q ↔ q`. `at h ⊢` rewrites `h` and the goal. Placeholders:
`{α : Type} [Fintype α] (p q : α → Prop) [DecidablePred p] [DecidablePred q] (a : α)`. `DecidablePred p`
(Lean can compute `p a` to true/false) holds for `fun σ => σ i = j` because `Fin n` has decidable equality.

| Before | After |
|---|---|
| `h : a ∈ Finset.filter p Finset.univ ⊢ a ∈ Finset.filter q Finset.univ` | `h : p a ⊢ q a` |

**R3 · `Equiv.Perm.mul_apply`** changes the **goal**: `(σ * τ) x = σ (τ x)`, the product of permutations is
composition. Placeholders: `{α : Type} (σ τ : Equiv.Perm α) (x : α)`.

| Before | After |
|---|---|
| `⊢ P ((σ * τ) x)` | `⊢ P (σ (τ x))` |

**R4 · `Equiv.swap_apply_left`** changes the **goal**: `Equiv.swap a b a = b`. Placeholders:
`{α : Type} [DecidableEq α] (a b : α)`; `Fin n` has `DecidableEq`.

| Before | After |
|---|---|
| `⊢ P ((Equiv.swap a b) a)` | `⊢ P b` |

**R5 · `Equiv.swap_apply_right`** changes the **goal**: `Equiv.swap a b b = a`. Same placeholders as R4.

| Before | After |
|---|---|
| `⊢ P ((Equiv.swap a b) b)` | `⊢ P a` |

In the "maps into" goal you have `hσ : σ i = j` and need `(Equiv.swap j k * σ) i = k`: R3, then `rw [hσ]`,
then R4. `simp [hσ]` does all three.

**R6 · `mul_right_inj`** changes the **context** here (`rw … at h`): `a * b = a * c ↔ b = c`, a common left
factor cancels. Placeholders: `{G : Type} [Group G] (a b c : G)`; `Equiv.Perm α` is a group under `*`.

| Before | After |
|---|---|
| `h : a * b = a * c ⊢ b = c` | `h : b = c ⊢ b = c` |

**R7 · `simpa using h`** **closes** the goal: it simplifies both `h` and the goal with `simp` (which knows
R6) and then closes the goal with the simplified `h`. This is the whole "injective" case. Placeholders:
as R6.

| Before | After |
|---|---|
| `h : a * b = a * c ⊢ b = c` | no goals |

**R8 · `refine ⟨x, ?_, ?_⟩`** changes the **goal list**: it supplies the witness `x` of an
`∃ a, ∃ (_ : a ∈ s), …` and leaves two goals, the membership and the equation. Placeholders:
`{α β : Type} (s : Finset α) (f : α → β) (b : β) (x : α)`. In the "surjective" goal for `τ`, the witness is
`Equiv.swap j k * τ` (a swap undoes itself).

| Before | After |
|---|---|
| `⊢ ∃ a, ∃ (_ : a ∈ s), f a = b` | `⊢ x ∈ s`, `⊢ f x = b` |

**R9 · `rw [← mul_assoc]`** changes the **goal**. `mul_assoc : a * b * c = a * (b * c)` (`*` groups to the
left); `←` regroups to the left. Placeholders: `{G : Type} [Monoid G] (a b c : G)` (a type with an
associative `*` and a `1`; every group, so `Equiv.Perm α`).

| Before | After |
|---|---|
| `⊢ P (a * (b * c))` | `⊢ P (a * b * c)` |

**R10 · `Equiv.swap_mul_self`** changes the **goal**: `Equiv.swap a b * Equiv.swap a b = 1`.
Placeholders: `{α : Type} [DecidableEq α] (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (Equiv.swap a b * Equiv.swap a b)` | `⊢ P 1` |

**R11 · `one_mul`** changes the **goal**: `1 * a = a`. Placeholders: `{G : Type} [Monoid G] (a : G)`.

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

R9 → R10 → R11 is the chain `swap * (swap * τ) = (swap * swap) * τ = 1 * τ = τ`. `simp [← mul_assoc]`
runs it (R10, R11 are `simp` lemmas).

**W2** in the guide runs the whole Part 1 pattern on elements instead of permutations,
`{x | x = j}.card = {x | x = k}.card` in `Fin n` via `x ↦ Equiv.swap j k x`. After R1 its goals read:

```lean-goal
⊢ {x | x = j}.card = {x | x = k}.card
⊢ ∀ a ∈ {x | x = j}, (Equiv.swap j k) a ∈ {x | x = k}
⊢ ∀ a₁ ∈ {x | x = j}, ∀ a₂ ∈ {x | x = j}, (Equiv.swap j k) a₁ = (Equiv.swap j k) a₂ → a₁ = a₂
⊢ ∀ b ∈ {x | x = k}, ∃ a, ∃ (_ : a ∈ {x | x = j}), (Equiv.swap j k) a = b
```

---

## Part 2 · `card_fix_mul` (MILESTONE, uses Part 1)

Statement: `#{σ | σ i = i} * n = n!`. Split all `n!` permutations by the value `σ i`: `n! = ∑ⱼ #{σ | σ i = j}`;
by Part 1 every summand equals `#{σ | σ i = i}`; a sum of `n` equal terms is `n` times the term.

**R12 · `have h := Finset.card_eq_sum_card_fiberwise (s := s) (t := t) (f := f) hf`** changes the
**context**: it adds the fibre decomposition of `s` by the value of `f`. Lemma:
`Finset.card_eq_sum_card_fiberwise [DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β} (H : Set.MapsTo f ↑s ↑t) : s.card = ∑ b ∈ t, {a ∈ s | f a = b}.card`.
`(s := s)` fills an implicit argument by name. `H` can be given as `fun a ha => …` or as a hypothesis
`∀ a ∈ s, f a ∈ t`; with `s = t = Finset.univ` it is `fun _ _ => Finset.mem_univ _`. Placeholders:
`{α β : Type} [DecidableEq β] (s : Finset α) (t : Finset β) (f : α → β)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, with the new hypothesis below in the context |

```
h : s.card = ∑ b ∈ t, {a ∈ s | f a = b}.card
```

**R13 · `Finset.card_univ`** changes the **context** here (`rw … at h`): `Finset.univ.card = Fintype.card α`.
Placeholders: `{α : Type} [Fintype α]`.

| Before | After |
|---|---|
| `h : Finset.univ.card = m ⊢ Fintype.card α = m` | `h : Fintype.card α = m ⊢ Fintype.card α = m` |

**R14 · `Fintype.card_perm`** changes the **goal**: `Fintype.card (Equiv.Perm α) = (Fintype.card α).factorial`.
Placeholders: `{α : Type} [DecidableEq α] [Fintype α]`.

| Before | After |
|---|---|
| `⊢ P (Fintype.card (Equiv.Perm α))` | `⊢ P (Fintype.card α).factorial` |

**R15 · `Fintype.card_fin`** changes the **goal**: `Fintype.card (Fin n) = n`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Fintype.card (Fin n))` | `⊢ P n` |

R13 → R14 → R15 turn `Finset.univ.card` (over `Equiv.Perm (Fin n)`) into `n.factorial`, and (over `Fin n`) into `n`.

**R16 · `rw [Finset.sum_congr rfl hfg]`** changes the **goal**: it replaces every summand. Lemma:
`Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`; `rfl` says the index set is
unchanged. In the exercise `hfg` is `fun j _ => card_apply_eq n i j i`. Placeholders:
`{α β : Type} [AddCommMonoid β] (s : Finset α) (f g : α → β)` (β has `+` and `0`; `ℕ`, `ℝ` qualify).

| Before | After |
|---|---|
| `⊢ P (∑ x ∈ s, f x)` | `⊢ P (s.sum g)` |

**R17 · `Finset.sum_const`** changes the **goal**: `∑ _x ∈ s, c = s.card • c`. Placeholders:
`{α β : Type} [AddCommMonoid β] (s : Finset α) (c : β)`.

| Before | After |
|---|---|
| `⊢ P (∑ _x ∈ s, c)` | `⊢ P (s.card • c)` |

**R18 · `smul_eq_mul`** changes the **goal**: `a • b = a * b` when the scalar and the vector have the same
type (here `n • m` with both in `ℕ`, or `x • y` in `ℝ` after R24). Placeholders: `{α : Type} [Mul α] (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**R19 · `mul_comm`** changes the **goal**: `a * b = b * a`, applied to the first product `rw` finds (and to
every copy of it). `rw` then tries `rfl`, which can close the goal. Placeholders:
`{α : Type} [CommMonoid α] (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (a * b)` | `⊢ P (b * a)` |

---

## Part 3 · `sum_numFixed` (MILESTONE)

Statement (in `ℝ`): `∑_σ ↑(numFixed σ) = ∑_i ↑#{σ | σ i = i}`. Unfold `numFixed` (`simp only [numFixed]`),
write each card as a sum of indicators (R20), push the casts inside (R21, R22), swap the sums (R23).

**R20 · `Finset.card_filter`** changes the **goal**:
`(Finset.filter p s).card = ∑ x ∈ s, if p x then 1 else 0`. Placeholders:
`{α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p]`.

| Before | After |
|---|---|
| `⊢ P (Finset.filter p s).card` | `⊢ P (∑ i ∈ s, if p i then 1 else 0)` |

**R21 · `Nat.cast_sum`** changes the **goal**: `↑(∑ x ∈ s, f x) = ∑ x ∈ s, ↑(f x)`, the cast `ℕ → ℝ` moves
inside the sum. Placeholders: `{α : Type} (s : Finset α) (f : α → ℕ)`, target `ℝ`.

| Before | After |
|---|---|
| `⊢ P ↑(∑ x ∈ s, f x)` | `⊢ P (∑ x ∈ s, ↑(f x))` |

**R22 · `simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]`** changes the **goal**: the cast moves into
the `if` (`↑(if c then m else k) = if c then ↑m else ↑k`) and `↑1 = 1`, `↑0 = 0`. Placeholders:
`(c : Prop) [Decidable c]`.

| Before | After |
|---|---|
| `⊢ P ↑(if c then 1 else 0)` | `⊢ P (if c then 1 else 0)` |

**R23 · `Finset.sum_comm`** changes the **goal**:
`∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y`. When the goal is exactly this equation,
`exact Finset.sum_comm` closes it. Placeholders:
`{α β γ : Type} [AddCommMonoid γ] (s : Finset α) (t : Finset β) (f : α → β → γ)`.

| Before | After |
|---|---|
| `⊢ P (∑ x ∈ s, ∑ y ∈ t, f x y)` | `⊢ P (∑ y ∈ t, ∑ x ∈ s, f x y)` |

---

## Part 4 · `expected_fixed_points`

Statement: `∫ σ, ↑(numFixed σ) ∂(PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure = 1` for `1 ≤ n`.
Integral → finite sum (R24), probabilities → `(↑n!)⁻¹` (R25, R14, R15, R18), factor out (R26), Part 3, each
summand → `n!/n` (via Part 2, R27–R29), then the arithmetic (R16, R17, R13, R15, R30–R33).

**R24 · `PMF.integral_eq_sum`** changes the **goal**: on a finite type an integral against a PMF is a
weighted sum, `∫ a, f a ∂p.toMeasure = ∑ a, (p a).toReal • f a`. It needs `MeasurableSpace α` and
`MeasurableSingletonClass α` (singletons are measurable): the two spec `instance`s provide exactly these for
`Equiv.Perm (Fin n)`. Placeholders:
`{α : Type} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α) (f : α → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (a : α), f a ∂p.toMeasure)` | `⊢ P (∑ a, (p a).toReal • f a)` |

**R25 · `PMF.uniformOfFintype_apply`** changes the **goal**:
`PMF.uniformOfFintype α a = (↑(Fintype.card α))⁻¹` in `ENNReal`. Placeholders:
`{α : Type} [Fintype α] [Nonempty α] (a : α)`; `Equiv.Perm (Fin n)` is nonempty (it contains `1`).

| Before | After |
|---|---|
| `⊢ P ((PMF.uniformOfFintype α) a)` | `⊢ P (↑(Fintype.card α))⁻¹` |

**R26 · `rw [← Finset.mul_sum]`** changes the **goal**. `Finset.mul_sum : c * ∑ i ∈ s, f i = ∑ i ∈ s, c * f i`;
right to left it pulls a common factor out of the sum. Placeholders: `{α : Type} (s : Finset α) (f : α → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, c * f i)` | `⊢ P (c * ∑ i ∈ s, f i)` |

**R27 · `rw [eq_div_iff hc]`** changes the **goal**: `eq_div_iff : c ≠ 0 → (a = b / c ↔ a * c = b)`. Use it
to turn `↑{σ | σ i = i}.card = ↑n.factorial / ↑n` into the product form that Part 2 proves. Write
`eq_div_iff (by positivity)` to discharge `c ≠ 0` on the spot. Placeholders: `(a b c : ℝ) (hc : c ≠ 0)`.

| Before | After |
|---|---|
| `⊢ a = b / c` | `⊢ a * c = b` |

**R28 · `positivity`** **closes** goals `0 < e`, `0 ≤ e`, `e ≠ 0` by the shape of `e`. For a bare variable it
looks in the context: `hn : 1 ≤ n` gives `(↑n : ℝ) ≠ 0`; `(↑n.factorial : ℝ) ≠ 0` needs nothing.
Placeholders: `(m : ℕ) (hm : 1 ≤ m)`.

| Before | After |
|---|---|
| `hm : 1 ≤ m ⊢ ↑m ≠ 0` | no goals |

**R29 · `exact_mod_cast h`** **closes** a goal that is `h` up to casts: `h : a * b = c` in `ℕ` proves
`↑a * ↑b = ↑c` in `ℝ`. Part 2 is stated in `ℕ`, the main goal lives in `ℝ`. Placeholders: `(a b c : ℕ)`.

| Before | After |
|---|---|
| `h : a * b = c ⊢ ↑a * ↑b = ↑c` | no goals |

**R30 · `nsmul_eq_mul`** changes the **goal**: `n • a = ↑n * a` for `n : ℕ` and `a` in a ring (here `ℝ`);
R17 produces such an `n • a`. Placeholders: `(n : ℕ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (n • a)` | `⊢ P (↑n * a)` |

**R31 · `ENNReal.toReal_inv`** changes the **goal**: `a⁻¹.toReal = a.toReal⁻¹`. Placeholders: `(a : ENNReal)`.

| Before | After |
|---|---|
| `⊢ P a⁻¹.toReal` | `⊢ P a.toReal⁻¹` |

**R32 · `ENNReal.toReal_natCast`** changes the **goal**: `(↑n : ENNReal).toReal = (↑n : ℝ)`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (↑n).toReal` | `⊢ P ↑n` |

**R33 · `field_simp`** changes or **closes** the goal: it multiplies out every denominator and inverse whose
non-vanishing is known (from `≠ 0` hypotheses in the context, or obvious), then normalises. Put
`have : (n.factorial : ℝ) ≠ 0 := by positivity` and `have : (n : ℝ) ≠ 0 := by positivity` in the context first.

| Before | After |
|---|---|
| `ha : a ≠ 0, hb : b ≠ 0 ⊢ a⁻¹ * (a / b) * b = 1` | no goals |

**W1: the same pipeline on a fair coin.** `∫ b, (if b then 1 else 0) ∂(uniformOfFintype Bool).toMeasure = 1/2`.
After R24, then `simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, smul_eq_mul]` (R25, R18):

```lean-goal
⊢ (∑ a, ((PMF.uniformOfFintype Bool) a).toReal • if a = true then 1 else 0) = 1 / 2
⊢ (∑ x, (↑2)⁻¹.toReal * if x = true then 1 else 0) = 1 / 2
```

and `simp` finishes. In the exercise, the same `simp only` with `Fintype.card_perm, Fintype.card_fin`
instead of `Fintype.card_bool` leaves `(↑n.factorial)⁻¹.toReal * ↑(numFixed x)` under the sum.

---

## Traps

- The two spec `instance`s only give `Equiv.Perm (Fin n)` the discrete σ-algebra (`⊤`: every set is
  measurable), so that R24 applies. Nothing to prove about them.
- `.toReal` sends `∞` to `0` (and in `ENNReal`, `0⁻¹ = ∞`). R31 still holds for every `a` (both sides are `0`
  at `a = 0` and `a = ∞`), so no side goal appears. Move to `ℝ` with R31, R32 first and do the arithmetic
  there; `field_simp` and `positivity` are for fields such as `ℝ`, not for `ENNReal`.
- `Finset.filter` prints as `{x | p x}`: it is a `Finset`, so `.card` and `∑` work on it; `Set` lemmas do not.
  When you type a statement (such as `hc` in Part 4), write `Finset.univ.filter fun σ => σ i = i`: the
  printed `{σ | σ i = i}` typed by hand elaborates to a `Set`, which has no `.card`.
- Casts: Part 2 is in `ℕ`, the main goal in `ℝ`. Do not `rw` with a `ℕ` equation in a real goal; go through
  R27 and `exact_mod_cast` (R29).
- `rw [eq_div_iff (by positivity)]` needs `(↑n : ℝ) ≠ 0`; `positivity` finds it only if `hn : 1 ≤ n` is in the
  context (it is, as the theorem's hypothesis).
- `field_simp` uses only `≠ 0` facts it can see: add them with `have` before calling it.
- `Finset.sum_congr rfl` needs a function `fun j _ => …` of the index and its membership proof, not just an
  equation.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `#s = #t` by a bijection | `apply Finset.card_bij (fun a _ => f a)` | R1 |
| `a ∈ {x \| p x}` → `p a` | `simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h` (add ⊢ for the goal) | R2 |
| apply a product / a swap | `Equiv.Perm.mul_apply`, `Equiv.swap_apply_left/right` (or `simp [h]`) | R3–R5 |
| cancel `a * _` | `simpa using h` (`mul_right_inj`) | R6, R7 |
| give the witness of `∃ a ha, …` | `refine ⟨x, ?_, ?_⟩` | R8 |
| `swap * (swap * τ) = τ` | `simp [← mul_assoc]` | R9–R11 |
| split a card by the value of `f` | `have h := Finset.card_eq_sum_card_fiberwise (f := f) hf` | R12 |
| `univ.card` of perms / of `Fin n` | `Finset.card_univ, Fintype.card_perm, Fintype.card_fin` | R13–R15 |
| rewrite every summand | `rw [Finset.sum_congr rfl (fun x _ => e x)]` | R16 |
| sum of a constant | `Finset.sum_const`, then `smul_eq_mul` / `nsmul_eq_mul` | R17, R18, R30 |
| card → sum of indicators | `Finset.card_filter` | R20 |
| cast through `∑` and `if` | `Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero` | R21, R22 |
| swap a double sum | `exact Finset.sum_comm` | R23 |
| integral → sum | `rw [PMF.integral_eq_sum]` | R24 |
| uniform probability | `PMF.uniformOfFintype_apply` | R25 |
| factor out of a sum | `rw [← Finset.mul_sum]` | R26 |
| `a = b / c` → `a * c = b` | `rw [eq_div_iff (by positivity)]` | R27, R28 |
| ℕ fact → ℝ goal | `exact_mod_cast h` | R29 |
| `ENNReal` → `ℝ` | `ENNReal.toReal_inv, ENNReal.toReal_natCast` | R31, R32 |
| clear denominators | `field_simp` (with `≠ 0` facts in context) | R33 |
| see the state | infoview | |
