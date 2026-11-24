# H092 · Third law: a unique ground state: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `apply`, `rw`, `simp`, `have`, `ring`,
anonymous functions `fun x => …`, dot notation `h.foo`. **New here:** Mathlib's limits (`Filter.Tendsto`,
`atTop`, `atBot`, `𝓝`) and the squeeze theorem, the real exponential and `Real.negMulLog`, finite sums `∑`
with `Finset.univ` and `Finset.erase`, the tactics `linarith`, `calc`, `classical`, `by_cases`, `subst`,
`simp_rw`, `simpa`, and physlib's `CanonicalEnsemble` with its β-parameterised partition function and
Boltzmann probabilities.

**The physics, in symbols.** Units `k_B = 1`. A finite system has microstates `i ∈ ι` with energies
$E_i$ (`𝓒.energy i`). At inverse temperature $b = 1/T$:
$Z(b) = \sum_i e^{-b E_i}$ (partition function) and $p_b(i) = e^{-b E_i}/Z(b)$ (Boltzmann probability).
The ground state $i_0$ is non-degenerate: the gap $\Delta_j = E_j - E_{i_0} > 0$ for every $j \ne i_0$.
Since $Z(b) \ge e^{-b E_{i_0}}$ (one term of a sum of positives),
$$p_b(j) \le \frac{e^{-b E_j}}{e^{-b E_{i_0}}} = e^{-b \Delta_j} \xrightarrow[b\to\infty]{} 0 \quad (j \ne i_0),
\qquad p_b(i_0) = 1 - \sum_{j \ne i_0} p_b(j) \to 1.$$
With $\eta(x) = -x \log x$ (`Real.negMulLog x`), the Gibbs entropy is $S(b) = \sum_i \eta(p_b(i))$. Mathlib's
`η` is defined and continuous on all of `ℝ`, with $\eta(0) = \eta(1) = 0$, so
$S(b) \to \sum_i \eta(\delta_{i i_0}) = 0$: the entropy vanishes as $T \to 0^+$ (third law).

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
  When the new hypothesis itself contains a comma, it is written in a separate span next to the `⊢` cell.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves alone.
- Lemmas that produce a fact are shown as `have h := lemma args`, so the context gains `h` and you see its
  type. In the exercise you usually pass them as arguments instead (`div_pos (exp_pos _) hZ`).
- `{β : Type} (l : Filter β)` is any "way the variable moves"; in the exercise `β = ℝ` and `l = atTop`.
  Values are real (`ℝ`) here, as in the exercise; the lemmas hold far more generally.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `𝓒 : CanonicalEnsemble ι` | a physlib system with microstates of type `ι`; `𝓒.energy : ι → ℝ` is the energy `E` |
| `[Fintype ι]`, `[MeasurableSpace ι]` | finitely many microstates; the measurable structure is required by the type and plays no role here |
| `Nonempty ι`, `this : Nonempty ι` | "`ι` has an element"; `haveI` (R1) adds it as an instance named `this` |
| `𝓒.mathematicalPartitionFunctionBetaReal t` | `Z(t) = ∑ i, rexp (-t * 𝓒.energy i)`, a real number (unfolds by definition) |
| `𝓒.probabilityBetaReal t i` | `p_t(i) = rexp (-t * 𝓒.energy i) / Z(t)` (R7) |
| `rexp x` | `Real.exp x`, the real exponential |
| `negMulLog`, `x.negMulLog` | `Real.negMulLog x = -x * Real.log x` (printed short because of `open Real`; dot notation since `x : ℝ`) |
| `Filter β`, `l` | a "limit direction" for a variable of type `β` (formally a filter: a family of "eventually" sets) |
| `atTop`, `atBot` | the variable goes to `+∞`, to `-∞` (`Filter.atTop`, `Filter.atBot`) |
| `𝓝 a` | the neighbourhoods of `a`: "gets close to `a`" (`nhds a`, notation from `open Topology`) |
| `Tendsto f l l'` | `f x` moves as `l'` says when `x` moves as `l` says. `Tendsto f atTop (𝓝 L)` is $\lim_{x\to\infty} f(x) = L$; `Tendsto f atTop atBot` is $f(x) \to -\infty$ |
| `Tendsto (fun x => …) l l'` | the same for a function written inline; `fun x => c` is a constant function |
| `g ∘ f` | composition: `(g ∘ f) x` is `g (f x)` by definition |
| `g ≤ f` (functions `β → ℝ`) | pointwise: `∀ x, g x ≤ f x`, so `intro x` opens it (R21) |
| `(fun x => 0) b`, `(rexp ∘ fun b => …) b` | a function applied to `b`, not yet simplified: it *is* `0`, `rexp (…)` by definition, so `exact` accepts a proof of the simplified statement (`simp only [Function.comp]` shows it simplified; `beta_reduce` handles `fun` but not `∘`) |
| `∑ i, f i` | the sum of `f i` over all `i : ι` (over `Finset.univ`, the finite set of all elements) |
| `∑ x ∈ s, f x` | the sum over a finite set `s : Finset ι`; lemma statements use this form |
| `s.erase a`, `Finset.univ.erase a` | `s` without `a`; it needs `DecidableEq ι` (R22) |
| `∀ i ∈ s, …` | `∀ i, i ∈ s → …`; a proof is `fun i hi => …` |
| `if c then x else y` | needs a `Decidable c` instance; `if i = i₀ then 1 else 0` is the indicator of `i₀` |
| `inst✝ : DecidableEq ι` | an unnamed instance in the context (from a `[…]` binder or `classical`) |
| `case calc_1`, `case calc_2` | the step goals a `calc` with `?_` leaves (R9) |
| `case hgf`, `case hfh` | the two inequality goals the squeeze leaves (R20) |
| `case pos`, `case neg` | the two goals of `by_cases` (R32) |

---

## Part 1 · `prob_le` (milestone 1)

Statement: `p_b(j) ≤ rexp (-b * (E j - E i₀))`. Get `Z b > 0` (R1, R2) and `rexp (-b * E i₀) ≤ Z b` (R6,
the `i₀` term of a sum of positive terms, R3–R5). Unfold `p`, clear the denominator (R7, R8), then a two-step
`calc` (R9): rewrite `rexp (-b E j)` as a product of two exponentials (R10, R11) and multiply the bound by
the nonnegative first factor (R12).

**R1 · `haveI : Nonempty ι := ⟨i⟩`** changes the **context**: it adds the *instance* `this : Nonempty ι`,
built from an element `i`. Lemmas with an instance argument `[Nonempty ι]` (R2) then find it by themselves.
Placeholders: `(i : ι)`.

| Before | After |
|---|---|
| `⊢ G` | `this : Nonempty ι ⊢ G` |

**R2 · `𝓒.mathematicalPartitionFunctionBetaReal_pos t`** changes the **context**: it is the fact `0 < Z t`
(physlib; it needs `[Nonempty ι]`, since an empty sum is `0`). Placeholders: `(𝓒 : CanonicalEnsemble ι) (t : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hZ : 0 < 𝓒.mathematicalPartitionFunctionBetaReal t ⊢ G` |

**R3 · `Real.exp_pos x`** changes the **context**: the fact `0 < rexp x`. `exp_pos _` (after `open Real`)
lets Lean find `x`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 < rexp x` | `h : 0 < rexp x ⊢ 0 < rexp x` |

**R4 · `hab.le`** (`LT.lt.le`) changes the **context**: `a < b` becomes `a ≤ b`. So `(exp_pos _).le : 0 ≤ rexp _`.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `hab : a < b ⊢ a ≤ b` | `h : a ≤ b ⊢ a ≤ b` |

**R5 · `Finset.mem_univ i`** changes the **context**: the fact `i ∈ Finset.univ` (every element of a finite
type is in `univ`). Placeholders: `(i : ι)`.

| Before | After |
|---|---|
| `⊢ i ∈ Finset.univ` | `h : i ∈ Finset.univ ⊢ i ∈ Finset.univ` |

**R6 · `Finset.single_le_sum`** changes the **context**. The lemma is
`Finset.single_le_sum : (∀ i ∈ s, 0 ≤ f i) → a ∈ s → f a ≤ ∑ x ∈ s, f x`: one term of a sum of nonnegative
terms is at most the sum. Give the summand by name, `(f := fun i => …)`: from a proof `fun i _ => …` alone Lean
cannot tell which `f` you mean. With `f := fun i => rexp (-b * 𝓒.energy i)` the sum *is* `Z b` by definition, so
the result can be stated as `rexp (-b * 𝓒.energy i₀) ≤ Z b`. Placeholders: `(f : ι → ℝ) (a : ι)`.

| Before | After |
|---|---|
| `⊢ f a ≤ ∑ i, f i` | `⊢ f a ≤ ∑ i, f i`, context gains `h : f a ≤ ∑ x, f x` |

**R7 · `rw [probabilityBetaReal]`** changes the **goal**: the name `p` becomes its definition. Under a binder
(`∑ i, 𝓒.probabilityBetaReal t i`, Part 3) `rw` cannot reach it; write `simp only [probabilityBetaReal]`.
Placeholders: `(𝓒 : CanonicalEnsemble ι) (t : ℝ) (i : ι)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.probabilityBetaReal t i)` | `⊢ P (rexp (-t * 𝓒.energy i) / 𝓒.mathematicalPartitionFunctionBetaReal t)` |

**R8 · `rw [div_le_iff₀ hc]`** changes the **goal**. The lemma is `div_le_iff₀ : 0 < c → (a / c ≤ b ↔ a ≤ b * c)`
(the `₀` marks the version for fields such as `ℝ`). Placeholders: `(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ a / c ≤ b` | `⊢ a ≤ b * c` |

**R9 · `calc`** changes the **goal list**: a chain `a = b ≤ c` proves `a ≤ c`, one step per line. `_` on the
first line is the goal's left side, on later lines the previous right side. Each step's proof follows `:=`;
with `?_` it becomes a goal of its own. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ a = b`, `⊢ b ≤ c` |

**R10 · `rw [← Real.exp_add]`** changes the **goal**. The lemma is `Real.exp_add : rexp (x + y) = rexp x * rexp y`;
right to left it merges a product of two exponentials. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (rexp x * rexp y)` | `⊢ P (rexp (x + y))` |

**R11 · `ring_nf`** **closes** an equation `f u = f v` when `u` and `v` are equal as ring expressions: it puts
every subterm in a normal form, also the arguments of `rexp`, and the two sides become the same text. (`ring`
alone fails here: `rexp` is not a ring operation.) Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ rexp (-x * (y - x) + -x * x) = rexp (-x * y)` | no goals |

**R12 · `mul_le_mul_of_nonneg_left hbc ha`** changes the **context**:
`b ≤ c → 0 ≤ a → a * b ≤ a * c` (multiply an inequality on the left by `a ≥ 0`). Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `hbc : b ≤ c, ha : 0 ≤ a ⊢ a * b ≤ a * c` | `h : a * b ≤ a * c ⊢ a * b ≤ a * c` |

---

## Part 2 · `prob_tendsto_zero` (milestone 2)

Statement: `E i₀ < E j → Tendsto (fun b => p_b(j)) atTop (𝓝 0)`. The exponent `-b * Δ` goes to `-∞` (R13–R15),
so `rexp (-b * Δ) → 0` (R16, R17). Squeeze `p_b(j)` between the constant `0` (R18) and that bound (R20):
`0 ≤ p` by R19, and `p ≤ bound` is milestone 1.

**R13 · `linarith`** **closes** a goal `t ≤ u`, `t < u` or `t = u` that follows from the hypotheses by adding
them with nonnegative coefficients. Products such as `b * E j` count as single unknowns.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : a < b ⊢ 0 < b - a` | no goals |

**R14 · `tendsto_neg_atTop_atBot`** changes the **context**: the fact `Tendsto (fun x => -x) atTop atBot`
("`-x → -∞` as `x → ∞`"). Lean prints the function as `Neg.neg` when you do not give the type, so state it with
`have h : Tendsto (fun x : ℝ => -x) atTop atBot := …`, or use it directly as the receiver of R15.

| Before | After |
|---|---|
| `⊢ G` | `h : Tendsto (fun x => -x) atTop atBot ⊢ G` |

**R15 · `hf.atBot_mul_const hr`** (`Filter.Tendsto.atBot_mul_const`) changes the **context**:
`0 < r → Tendsto f l atBot → Tendsto (fun x => f x * r) l atBot`. With `f = fun b => -b` and `r = Δ` this is
`-b * Δ → -∞`. Placeholders: `{β : Type} (l : Filter β) (f : β → ℝ) (r : ℝ)`.

| Before | After |
|---|---|
| `hf : Tendsto f l atBot ⊢ Tendsto (fun x => f x * r) l atBot` | `h : Tendsto (fun x => f x * r) l atBot ⊢ Tendsto (fun x => f x * r) l atBot` |

**R16 · `Real.tendsto_exp_atBot`** changes the **context**: the fact `Tendsto rexp atBot (𝓝 0)`
($e^y \to 0$ as $y \to -\infty$).

| Before | After |
|---|---|
| `⊢ G` | `h : Tendsto rexp atBot (𝓝 0) ⊢ G` |

**R17 · `hg.comp hf`** (`Filter.Tendsto.comp`) changes the **context**:
`Tendsto g l' l'' → Tendsto f l l' → Tendsto (g ∘ f) l l''`. The middle direction `l'` must match: `rexp` wants
its argument going `atBot`, so `Real.tendsto_exp_atBot.comp hlin` needs `hlin : Tendsto (…) atTop atBot`.
`(g ∘ f) x` is `g (f x)` by definition, so `exact h` accepts it for `fun x => g (f x)`.
Placeholders: `{β : Type} (l : Filter β) (l' : Filter ℝ) (f : β → ℝ) (g : ℝ → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun x => g (f x)) l (𝓝 c)` | `h : Tendsto (g ∘ f) l (𝓝 c) ⊢ Tendsto (fun x => g (f x)) l (𝓝 c)` |

**R18 · `tendsto_const_nhds`** changes the **context**: a constant function tends to its value,
`Tendsto (fun _ => c) l (𝓝 c)`. Lean usually infers `c` and `l` from the goal; when it cannot, give them by name:
`tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))`. Placeholders: `{β : Type} (l : Filter β) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun x => c) l (𝓝 c)` | `h : Tendsto (fun x => c) l (𝓝 c) ⊢ Tendsto (fun x => c) l (𝓝 c)` |

**R19 · `div_pos ha hb`** changes the **context**: `0 < a → 0 < b → 0 < a / b`. For `0 < p_b(j)`:
`div_pos (exp_pos _) (𝓒.mathematicalPartitionFunctionBetaReal_pos b)` (R3, R2), then `.le` (R4).
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `ha : 0 < a, hb : 0 < b ⊢ 0 < a / b` | `h : 0 < a / b ⊢ 0 < a / b` |

**R20 · `tendsto_of_tendsto_of_tendsto_of_le_of_le hg hk`** (the squeeze theorem) changes the **goal list**:
`Tendsto g l (𝓝 a) → Tendsto k l (𝓝 a) → g ≤ f → f ≤ k → Tendsto f l (𝓝 a)`. With `apply` and the two limits
given, the two pointwise inequalities remain. In term mode give all four arguments; the inequalities as
`fun b => …` (R21). Placeholders: `{β : Type} (l : Filter β) (f g k : β → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto f l (𝓝 a)` | `⊢ g ≤ f`, `⊢ f ≤ k` |

**R21 · `intro x`** on `g ≤ f` between functions changes the **goal and the context**: `≤` on functions is
pointwise, `∀ x, g x ≤ f x`, so `intro` opens it. In term mode a proof of `g ≤ f` is `fun x => …`.
When `g`, `f` are written as `fun …` (as after R20 in milestone 2) the new goal shows them applied but not
simplified, e.g. `(fun x => 0) b ≤ (fun b => 𝓒.probabilityBetaReal b j) b`; `exact` with the simplified fact
still works, since both are the same by definition.
Placeholders: `{β : Type} (f g : β → ℝ)`.

| Before | After |
|---|---|
| `⊢ g ≤ f` | `x : β ⊢ g x ≤ f x` |

**W1** (guide) runs this whole part on `0 ≤ u x ≤ rexp (-x * c)` with `c > 0`: R14 → R15 gives `hlin`, then one
R20 with R18, R16 → R17 and the two bounds.

```lean-goal
⊢ Tendsto u atTop (𝓝 0)
```

---

## Part 3 · `prob_ground_tendsto_one` (milestone 3)

Statement: `Tendsto (fun b => p_b(i₀)) atTop (𝓝 1)`. The probabilities sum to 1, so
`p_b(i₀) = 1 - ∑ j ∈ univ.erase i₀, p_b(j)` (R22–R26, R13). Rewrite the goal with that under `fun b =>` (R27);
the limit is `1 - ∑ 0` by R18, R28 and R29 with milestone 2 (R30 gives `j ≠ i₀`), and `simpa` (R31) cleans it to `1`.

**R22 · `classical`** leaves the visible **goal and context** unchanged; afterwards every proposition counts as
decidable, so `if a = b then … else …` and `s.erase a` (which must decide `x = a`) typecheck for any `ι`.
Put it first in a proof that uses either. Placeholders: `(a : ι)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G` (and `Finset.univ.erase a` now typechecks) |

**R23 · `Finset.sum_div`** changes the **goal**. The lemma is
`Finset.sum_div : (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`; with `←` it pulls the common `/ a` out of the sum.
`simp only [probabilityBetaReal, ← Finset.sum_div]` unfolds `p` under `∑` (R7) and does this in one call.
Placeholders: `(f : ι → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i / a)` | `⊢ P ((∑ i, f i) / a)` |

**R24 · `hz.ne'`** (`LT.lt.ne'`) changes the **context**: from `hz : 0 < z` it makes `z ≠ 0`, the form `div_self`
wants. (`hz.ne` would give `0 ≠ z`.) Placeholders: `(z : ℝ)`.

| Before | After |
|---|---|
| `hz : 0 < z ⊢ z ≠ 0` | `h : z ≠ 0 ⊢ z ≠ 0` |

**R25 · `div_self ha`** changes the **context**: `div_self : a ≠ 0 → a / a = 1`. After R23 the goal is
`(∑ i, rexp (-b * E i)) / Z b = 1`, and `exact div_self …` is accepted because the numerator *is* `Z b` by
definition. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ a / a = 1` | `h : a / a = 1 ⊢ a / a = 1` |

**R26 · `rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h`** changes the **context**: it splits the term
`a` off a sum inside `h`. The lemma is `Finset.add_sum_erase s f : a ∈ s → f a + ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x`
(needs `DecidableEq ι`, R22); `R5` supplies `a ∈ univ`. Then `linarith` (R13) solves `h` for `f a`.
Placeholders: `[DecidableEq ι] (f : ι → ℝ) (a : ι) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ G`, with `h : ∑ i, f i = c` | `⊢ G`, with `h` now `f a + ∑ x ∈ Finset.univ.erase a, f x = c` |

**R27 · `simp_rw [e]`** with `e : ∀ x, f x = g x` changes the **goal**: it rewrites under binders such as
`fun x => …`. `rw [e]` fails there, because the `x` inside `fun x => f x * 2` is bound and `rw` cannot
instantiate `e` with it. Placeholders: `{β : Type} (l : Filter β) (f g : β → ℝ) (L : ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun x => f x * 2) l (𝓝 L)` | `⊢ Tendsto (fun x => g x * 2) l (𝓝 L)` |

**R28 · `hf.sub hg`** (`Filter.Tendsto.sub`) changes the **context**: limits of a difference,
`Tendsto f l (𝓝 a) → Tendsto g l (𝓝 b) → Tendsto (fun x => f x - g x) l (𝓝 (a - b))`.
Placeholders: `{β : Type} (l : Filter β) (f g : β → ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun x => f x - g x) l (𝓝 (a - b))` | `h : Tendsto (fun x => f x - g x) l (𝓝 (a - b)) ⊢ Tendsto (fun x => f x - g x) l (𝓝 (a - b))` |

**R29 · `tendsto_finsetSum s hF`** changes the **context**: termwise limits give the limit of a finite sum,
`(∀ i ∈ s, Tendsto (F i) l (𝓝 (a i))) → Tendsto (fun x => ∑ i ∈ s, F i x) l (𝓝 (∑ i ∈ s, a i))`.
Write `hF` as `fun i hi => …`; `hi : i ∈ s` is what R30 consumes. Placeholders:
`{β : Type} (l : Filter β) (s : Finset ι) (F : ι → β → ℝ) (a : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun x => ∑ i ∈ s, F i x) l (𝓝 (∑ i ∈ s, a i))` | same goal; context gains `h : Tendsto (fun b => ∑ c ∈ s, F c b) l (𝓝 (∑ c ∈ s, a c))` |

**R30 · `Finset.ne_of_mem_erase hb`** changes the **context**: `b ∈ s.erase a → b ≠ a`. With `hgap j (…)` it turns
the membership `hj : j ∈ univ.erase i₀` into the gap `E i₀ < E j`. Placeholders: `[DecidableEq ι] (s : Finset ι) (a b : ι)`.

| Before | After |
|---|---|
| `hb : b ∈ s.erase a ⊢ b ≠ a` | `h : b ≠ a ⊢ b ≠ a` |

**R31 · `simpa using h`** **closes** the goal: it runs `simp` on both `h` and the goal, then closes the goal with
the simplified `h`. Use it when `h` is the goal up to simp clean-up: here `0 * a i = 0`, `∑ i ∈ s, 0 = 0`,
`c - 0 = c`. `simpa [l₁, l₂] using h` adds simp lemmas. Placeholders:
`{β : Type} (l : Filter β) (s : Finset ι) (f : β → ℝ) (a : ι → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto f l (𝓝 c)` (with `h` about `𝓝 (c - ∑ i ∈ s, 0 * a i)`) | no goals |

**W2** (guide) combines R18, R28, R29 and R31 for a constant minus a finite sum of vanishing terms. Before the
`simpa`, `h` has limit `2 - ∑ c ∈ s, 0`:

```lean-goal
⊢ Tendsto (fun x => 2 - ∑ i ∈ s, F i x) atTop (𝓝 2)
```

---

## Part 4 · `third_law`

Statement: `Tendsto (fun b => ∑ i, negMulLog (p_b(i))) atTop (𝓝 0)`. First the indicator limit
`hlim : ∀ i, Tendsto (fun b => p_b(i)) atTop (𝓝 (if i = i₀ then 1 else 0))`, by cases on `i = i₀` (R32–R34) with
milestones 3 and 2. Then push it through the continuous `negMulLog` (R35, R17) and the sum (R29); `simpa` with
R36 and R37 turns the limit `∑ i, negMulLog (if i = i₀ then 1 else 0)` into `0`.

**R32 · `by_cases hi : a = b`** changes the **goal list**: two copies of the goal, one with `hi : a = b`
(`case pos`), one with `hi : ¬a = b` (`case neg`). Work on them with `·` bullets. Placeholders: `(a b : ι) (P : Prop)`.

| Before | After |
|---|---|
| `⊢ P` | `hi : a = b ⊢ P`, `hi : ¬a = b ⊢ P` |

**R33 · `subst hi`** with `hi : a = b`, where `b` is a local variable, changes the **context and the goal**:
`b` disappears and every `b` becomes `a`. After `subst hi` with `hi : i = i₀`, the hypothesis `hgap` speaks about
`i`, and the target's `if i = i then 1 else 0` simplifies to `1`. Placeholders: `(a b : ι) (P : ι → Prop)`.

| Before | After |
|---|---|
| `hi : a = b, hb : P b ⊢ P a` | `hb : P a ⊢ P a` |

**R34 · `simp [hi]`** on an `if` changes the **goal**: with `hi : ¬a = b` it rewrites `a = b` to `False` and
`if False then x else y` to `y` (`if_neg`). With `a = a` (after R33) the condition is `True` and the `if` becomes
`x` without any hint. In the exercise this happens inside `simpa [hi] using …`. Placeholders:
`[DecidableEq ι] (a b : ι) (x y : ℝ)`.

| Before | After |
|---|---|
| `hi : ¬a = b ⊢ P (if a = b then x else y)` | `⊢ P y` |

**R35 · `Real.continuous_negMulLog.tendsto a`** (`Continuous.tendsto`) changes the **context**: a continuous
function is continuous at each point, `Tendsto negMulLog (𝓝 a) (𝓝 (negMulLog a))`. Compose it with a limit
`hF : Tendsto F l (𝓝 a)` by R17: `(Real.continuous_negMulLog.tendsto _).comp hF`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `h : Tendsto negMulLog (𝓝 a) (𝓝 a.negMulLog) ⊢ G` |

**R36 · `rw [apply_ite f]`** changes the **goal**. The lemma is
`apply_ite f : f (if c then x else y) = if c then f x else f y`. In the exercise give it to `simp` as
`apply_ite Real.negMulLog`, so it fires under `∑`. Placeholders: `(c : Prop) [Decidable c] (f : ℝ → ℝ) (x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (f (if c then x else y))` | `⊢ P (if c then f x else f y)` |

**R37 · `Real.negMulLog_zero`, `Real.negMulLog_one`** change the **goal**: `negMulLog 0 = 0` and
`negMulLog 1 = 0`. Both are `simp` lemmas, so plain `simp` (and `simpa`) apply them by itself; then
`if c then 0 else 0` becomes `0` and `∑ i, 0` becomes `0`.

| Before | After |
|---|---|
| `⊢ P (negMulLog 0 + negMulLog 1)` | `⊢ P (0 + 0)` |

**W3** (guide) pushes termwise limits `F i x → 0` through `negMulLog` and `∑ i` (R35 → R17 inside R29), then R31
with R37. Before the `simpa`, `h` has the limit `∑ c, negMulLog 0`:

```lean-goal
⊢ Tendsto (fun x => ∑ i, (F i x).negMulLog) atTop (𝓝 0)
```

The exercise adds the indicator `if i = i₀ then 1 else 0` in the limit; R36 moves `negMulLog` inside the `if`.

---

## Traps

- Every lemma about `Z` (R2) needs the instance `[Nonempty ι]`, which the milestones do not have: add it with
  `haveI : Nonempty ι := ⟨i₀⟩` (R1) first.
- `Finset.univ.erase i₀` and `if i = i₀ …` need `DecidableEq ι`; without `classical` (R22) at the start you get
  "failed to synthesize Decidable". Put `classical` before any `have` that mentions them.
- `rw` cannot rewrite under `fun b => …` or `∑ i, …` when the pattern mentions the bound variable: use `simp_rw`
  (R27) or `simp only [...]` (R7, R23).
- `Finset.single_le_sum` with a proof `fun i _ => …` cannot guess `f`: pass `(f := fun i => rexp (-b * 𝓒.energy i))`.
- `Tendsto.comp` composes left to right as `outer.comp inner`, and the middle filters must agree:
  `Real.tendsto_exp_atBot` wants an `atBot` limit, not `𝓝 _`.
- `ring` fails on `rexp u = rexp v`; `ring_nf` (R11) normalises inside `rexp` and closes it.
- `hz.ne'` (`z ≠ 0`) versus `hz.ne` (`0 ≠ z`): `div_self` wants `z ≠ 0`.
- `linarith` does not use `∀` facts or unfold definitions: specialise them first (`have := hsum b`).
- `t1 ; t2` runs `t2` on the first goal only (TACTIC_STATES, "Structure"). After R9, R20 or R32 use `·` bullets.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| instance `Nonempty ι` | `haveI : Nonempty ι := ⟨i₀⟩` | R1 |
| `0 < Z b`, `Z b ≠ 0` | `𝓒.mathematicalPartitionFunctionBetaReal_pos b`, `.ne'` | R2, R24 |
| `0 < exp x`, `0 ≤ exp x` | `exp_pos _`, `(exp_pos _).le` | R3, R4 |
| one term ≤ sum of nonnegatives | `Finset.single_le_sum (f := …) (fun i _ => …) (Finset.mem_univ a)` | R5, R6 |
| see `p b i` as `exp / Z` | `rw [probabilityBetaReal]`, under `∑`: `simp only [probabilityBetaReal]` | R7 |
| `a / c ≤ b` → `a ≤ b * c` | `rw [div_le_iff₀ hc]` | R8 |
| chain of `=` / `≤` | `calc _ = b := … \n _ ≤ c := …` | R9 |
| `exp x * exp y` → `exp (x + y)` | `rw [← Real.exp_add]` | R10 |
| `exp u = exp v`, `u`, `v` ring-equal | `ring_nf` | R11 |
| multiply `b ≤ c` by `a ≥ 0` | `mul_le_mul_of_nonneg_left hbc ha` | R12 |
| linear consequence | `linarith` | R13 |
| `-b * Δ → -∞` | `tendsto_neg_atTop_atBot.atBot_mul_const hΔ` | R14, R15 |
| `exp (…) → 0` | `Real.tendsto_exp_atBot.comp hlin` | R16, R17 |
| constant limit | `tendsto_const_nhds` | R18 |
| `0 < a / b` | `div_pos ha hb` | R19 |
| squeeze | `tendsto_of_tendsto_of_tendsto_of_le_of_le hg hk (fun b => …) (fun b => …)` | R20, R21 |
| `if`, `erase` typecheck | `classical` | R22 |
| `∑ f / a` → `(∑ f) / a` | `rw [← Finset.sum_div]` (under `simp only`) | R23 |
| `a / a = 1` | `div_self ha` | R25 |
| split one term off `∑` | `rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h` | R26 |
| rewrite under `fun b =>` | `simp_rw [e]` | R27 |
| limit of `f - g`, of a finite sum | `hf.sub hg`, `tendsto_finsetSum s fun i hi => …` | R28, R29 |
| `j ∈ s.erase a` → `j ≠ a` | `Finset.ne_of_mem_erase hj` | R30 |
| close up to simp clean-up | `simpa using h`, `simpa [hi] using h` | R31, R34 |
| case split on `i = i₀` | `by_cases hi : i = i₀`, then `subst hi` | R32, R33 |
| limit through `negMulLog` | `(Real.continuous_negMulLog.tendsto _).comp h` | R35, R17 |
| `f (if …)` → `if … f …` | `apply_ite f` (in a `simp` set) | R36 |
| `negMulLog 0`, `negMulLog 1` | `Real.negMulLog_zero`, `Real.negMulLog_one` (simp does it) | R37 |
| see the state | infoview | |
