# H064 · Heron's method converges: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`have`, `exact`, `exacts`, `constructor`, `rw [h]`, `rw [← h]`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `by`, `rw`, `simp`, `exact`, `have`,
`apply`, `∧`/`∨`/`∃`/`↔` (and `.mpr` for the right-to-left half of an `↔`), recursive `def` on `ℕ`,
induction on paper. Milestones 1–3 are the specs of M109 (the same step map), so a proof from there
can be pasted.
**New here:** Mathlib's real numbers `ℝ` and `Real.sqrt`; the tactics `unfold`, `field_simp`,
`linarith`, `nlinarith`, `positivity`, `set`, `rintro`, `fun_prop`; order notions (`Antitone`,
`BddBelow`, `Set.range`, `lowerBounds`, the infimum `⨅`); limits of sequences as
`Filter.Tendsto … atTop (𝓝 a)` and `ContinuousAt`.

**The mathematics.** Fix `a > 0`, `x₀ > 0`, and the step `b(x) = (x + a/x)/2` (`babylon a x`), with
`x_{n+1} = b(x_n)` (`heron a x₀ n = x_n`).

- Error identity (for `x > 0`): `b(x) − √a = (x − √a)² / (2x) ≥ 0`. So every iterate from step 1 on is
  `≥ √a` (`heron_ge`), in particular `> 0`.
- If `x ≥ √a` then `a/x ≤ x` (because `a ≤ x²`), so `b(x) ≤ x`: from step 1 on the sequence decreases.
- Monotone convergence: `g n = x_{n+1}` is decreasing and bounded below by `√a`, so `g n → L = inf g`,
  and `L ≥ √a > 0`.
- Limit identification: `g(n+1) = b(g n)`. The left side tends to `L` (a tail of `g`); the right side
  to `b(L)`, because `b` is continuous at `L ≠ 0`. Limits are unique, so `b(L) = L`, i.e.
  `L + a/L = 2L`, so `L² = a` and `L = √a` (`L > 0`).
- Finally `x_n → √a` because its shift `g` does.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. `G : Prop` is an arbitrary goal that the example finishes with
  `hG`; it only exists so the new hypothesis can be shown.
- Placeholders are written as Lean binders: `(x : ℝ)` a real number, `(u : ℕ → ℝ)` a real sequence,
  `(l : Filter ℝ)` a "limit target" (see `Tendsto` below).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ`, `ℕ` | the real numbers; the natural numbers `0, 1, 2, …` |
| `√x` | `Real.sqrt x`; for `x < 0` Lean defines `√x = 0` |
| `√x ^ 2`, `√(x ^ 2)` | `(√x) ^ 2` (`√` binds tighter than `^`), versus the root of `x ^ 2`: different lemmas (R2, R16) |
| `x ^ 2` | `x * x`; `^` takes a natural-number exponent |
| `a / x` | division; Lean defines `a / 0 = 0`, so lemmas about `/` need `x ≠ 0` or `0 < x` |
| `heron a x₀ n` | the iterate `xₙ`; `heron a x₀ (n + 1)` is *by definition* `babylon a (heron a x₀ n)` (R10) |
| `heron a x₀ (0 + 1)` | the base case of `induction` on `heron_ge`: Lean prints `0 + 1` unsimplified; it is `babylon a x₀` by definition (R10) |
| `Antitone f` | `f` is decreasing: `∀ m n, m ≤ n → f n ≤ f m` |
| `Set.range f` | the set of values `{f n \| n : ℕ}` |
| `lowerBounds s` | the set of `c` with `c ≤ y` for every `y ∈ s` |
| `BddBelow s` | `s` has some lower bound: `∃ c, c ∈ lowerBounds s` |
| `⨅ i, f i` | `iInf f`, the infimum (greatest lower bound) of the values `f i`. On `ℝ` it is only meaningful when the values are bounded below; lemmas about it (`…ciInf`, "conditionally complete") ask for that |
| `Tendsto u atTop (𝓝 L)` | `Filter.Tendsto`: `u n → L` as `n → ∞` (`open Filter Topology` gives the short names) |
| `atTop` | `Filter.atTop`, "all sufficiently large `n`" |
| `𝓝 L` | `nhds L`, "all points close enough to `L`"; `Tendsto f (𝓝 x) (𝓝 y)` says `f z → y` as `z → x` |
| `Tendsto (fun n => n + 1) atTop atTop` | `n + 1 → ∞` as `n → ∞` |
| `ContinuousAt f x` | `f` is continuous at the point `x` |
| `g ∘ u` | composition: `(g ∘ u) n = g (u n)` by definition |
| `g : ℕ → ℝ := fun n => …` | a local definition made by `set` (R17): `g` *is* that function |
| `fun n => u (n + 1)` | the shifted sequence `n ↦ u (n + 1)` |
| `hab.le`, `hx.ne'` | dot notation: `LT.lt.le hab : a ≤ b` (R11), `LT.lt.ne' hx : x ≠ 0` (R23) |
| `case zero`, `case succ` | the base case and the step after `induction` |

---

## Part 1 · `babylon_error` (milestone)

Statement: for `0 ≤ a`, `0 < x`: `babylon a x - √a = (x - √a) ^ 2 / (2 * x)`. On paper: multiply out
by `2x`; both sides become `x² + a − 2x√a`, using `√a² = a`.

**R1 · `unfold f`** changes the **goal**: the defined name `f` is replaced by its body. Placeholders:
`step` defined by `def step (x : ℝ) : ℝ := x / 2 + 1 / x`, `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (step x)` | `⊢ P (x / 2 + 1 / x)` |

**R2 · `have hs := Real.sq_sqrt hx`** changes the **context**. The lemma is
`Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x`. Placeholders: `(x : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `⊢ G` | `hs : √x ^ 2 = x ⊢ G` |

**R3 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero
(it finds `x ≠ 0` from a hypothesis `hx : 0 < x` or `hx : x ≠ 0`) and puts both sides over one line.
The exact normal form is Lean's choice (`c * x` may come out as `x * c`); read it in the infoview.
Placeholders: `(a b c x : ℝ) (hx : 0 < x)`.

| Before | After |
|---|---|
| `⊢ a / x + b = c` | `⊢ a + x * b = x * c` |

In `babylon_error`, after `unfold babylon` (R1) and `field_simp` the goal is a polynomial identity
in `x`, `a`, `√a`.

**R4 · `nlinarith [t₁, t₂]`** **closes** a goal `=`, `≤`, `<` between polynomial expressions. Like
`linarith` (R6) it adds up hypotheses with nonnegative coefficients; in addition it multiplies pairs of
hypotheses and hint terms `tᵢ` (any proofs, e.g. `Real.sqrt_nonneg a`), which is what a nonlinear
inequality such as `s ≤ x → s * s ≤ x * x` needs. Placeholders: `(s x : ℝ) (hs : 0 ≤ s) (h : s ≤ x)`.

| Before | After |
|---|---|
| `hs : 0 ≤ s, h : s ≤ x ⊢ s * s ≤ x * x` | closed |

---

## Part 2 · `sqrt_le_babylon` (milestone)

Statement: for `0 ≤ a`, `0 < x`: `√a ≤ babylon a x`. On paper: the error identity (Part 1) says
`babylon a x − √a` is a square over `2x > 0`.

**R5 · `positivity`** **closes** a goal `0 ≤ e` or `0 < e` where `e` is built from squares, `+`, `*`,
`/`, numerals, and atoms whose sign is a hypothesis (`hy : 0 < y`). Placeholders: `(x y : ℝ) (hy : 0 < y)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ (x - 1) ^ 2 / (3 * y)` | closed |

**R6 · `linarith`** **closes** a linear (in)equality that follows from the hypotheses by adding them up
with nonnegative coefficients. Any nonlinear piece (`x * y`, `L ^ 2`, `(x - √a) ^ 2 / (2 * x)`) is one
unknown. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `h₁ : a - b = c, h₂ : 0 ≤ c ⊢ b ≤ a` | closed |

---

## Part 3 · `babylon_le` (milestone)

Statement: for `0 ≤ a`, `0 < x`, `√a ≤ x`: `babylon a x ≤ x`. On paper: `a = √a² ≤ x²`, so
`a / x ≤ x`, so `(x + a/x)/2 ≤ x`.

**R7 · `rw [div_le_iff₀ hc]`** changes the **goal**. The lemma is
`div_le_iff₀ (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c`. Placeholders: `(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ a / c ≤ b` | `⊢ a ≤ b * c` |

**R8 · `have h := Real.sqrt_nonneg x`** changes the **context**: `Real.sqrt_nonneg x : 0 ≤ √x`, for
every real `x`. Its main use here is as a hint term: `nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt ha]`
(R4 with R8 and R2). Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `h : 0 ≤ √x ⊢ G` |

---

## Part 4 · `heron_ge` (milestone)

Statement: for `0 < a`, `0 < x₀`, every `n`: `√a ≤ heron a x₀ (n + 1)`. On paper: induction on `n`;
each case is `sqrt_le_babylon` applied to the previous iterate, which is positive (`x₀ > 0`, or
`≥ √a > 0` by the induction hypothesis).

**R9 · `induction n with | zero => ?_ | succ n ih => ?_`** changes the **goal list**: the goal for
`n` becomes a base case for `0` and a step for `n + 1` that has the induction hypothesis `ih`.
Placeholders: `(P : ℕ → Prop) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P n` | `⊢ P 0`, `n : ℕ, ih : P n ⊢ P (n + 1)` |

**R10 · a recursive `def` computes by definition.** `seq x₀ (n + 1)` *is* `step (seq x₀ n)`: Lean
unfolds it on its own when it compares types, so `exact` accepts a proof about the body, and `show`
changes the goal to the body. In the exercise, `heron a x₀ (n + 1 + 1)` is `babylon a (heron a x₀ (n + 1))`,
and `g (n + 1)` is `babylon a (g n)` for `g n = heron a x₀ (n + 1)`. Placeholders: `seq` defined by
`| 0 => x₀ | n + 1 => step (seq x₀ n)`, `(x₀ : ℝ) (n : ℕ)`.

| Before | After `show P (step (seq x₀ n))` |
|---|---|
| `⊢ P (seq x₀ (n + 1))` | `⊢ P (step (seq x₀ n))` |

**R11 · `hab.le`** changes the **context** (with `have`): `LT.lt.le : a < b → a ≤ b`. Use it inline
(`ha.le : 0 ≤ a`) to feed a lemma that wants `≤`. Placeholders: `(a b : ℝ) (hab : a < b)`.

| Before | After |
|---|---|
| `⊢ G` | `h : a ≤ b ⊢ G` |

**R12 · `apply lt_of_lt_of_le hab`** changes the **goal**. The lemma is
`lt_of_lt_of_le : a < b → b ≤ c → a < c`; as a term, `lt_of_lt_of_le hs ih : 0 < y` from `hs : 0 < √a`
and `ih : √a ≤ y`. Placeholders: `(a b c : ℝ) (hab : a < b)`.

| Before | After |
|---|---|
| `⊢ a < c` | `⊢ b ≤ c` |

**R13 · `rw [Real.sqrt_pos]`** changes the **goal**. The lemma is `Real.sqrt_pos : 0 < √x ↔ 0 < x`; as
a term, `Real.sqrt_pos.mpr hx : 0 < √x` from `hx : 0 < x`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 < √x` | `⊢ 0 < x` |

---

## Part 5 · `fixed_point_eq_sqrt` (milestone)

Statement: for `0 < L`, `babylon a L = L` implies `L = √a`. On paper: `(L + a/L)/2 = L` gives
`L² + a = 2L²`, so `L² = a`, and `√(L²) = L` because `L ≥ 0`.

**R14 · `unfold f at h`** changes the **context**: the name `f` inside the hypothesis `h` is replaced by
its body. Placeholders: `step` as in R1, `(x : ℝ)`.

| Before | After |
|---|---|
| `h : step x = x ⊢ G` | `h : x / 2 + 1 / x = x ⊢ G` |

**R15 · `field_simp at h`** changes the **context**: R3 applied to the hypothesis `h`. Placeholders:
`(x : ℝ) (hx : 0 < x)`.

| Before | After |
|---|---|
| `h : (x + 3 / x) / 4 = x ⊢ G` | `h : x ^ 2 + 3 = x ^ 2 * 4 ⊢ G` |

From such an `h`, `L ^ 2 = a` follows by R4 (R6 also works: `L ^ 2` counts as one unknown).

**R16 · `rw [Real.sqrt_sq hx]`** changes the **goal**. The lemma is `Real.sqrt_sq : 0 ≤ x → √(x ^ 2) = x`
(compare R2, which is `√x ^ 2 = x`). Placeholders: `(x : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `⊢ P √(x ^ 2)` | `⊢ P x` |

To use it on the goal `L = √a`, first `rw [← hsq]` with `hsq : L ^ 2 = a`, which turns `√a` into
`√(L ^ 2)`; after R16 the goal `L = L` closes by itself.

---

## Part 6 · `heron_tendsto`

Statement: for `0 < a`, `0 < x₀`: `Tendsto (heron a x₀) atTop (𝓝 √a)`, i.e. `xₙ → √a`. Prove the five
milestones first; this proof combines them with the limit lemmas below.

### Monotone convergence

**R17 · `set g := e with hg`** changes the **context and the goal**: it adds a local definition
`g := e` and the equation `hg : g = e`, and replaces `e` by `g` in the goal and in every hypothesis.
Placeholders: `(u : ℕ → ℝ)`, `e` here is `fun n => u (n + 1)`.

| Before | After |
|---|---|
| `h : P fun n => u (n + 1) ⊢ P fun n => u (n + 1)` | `g : ℕ → ℝ := fun n => u (n + 1), hg : g = fun n => u (n + 1), h : P g ⊢ P g` |

`set L := ⨅ n, g n` works the same way, so later hypotheses print `L` instead of the infimum.

**R18 · `apply antitone_nat_of_succ_le`** changes the **goal**. The lemma is
`antitone_nat_of_succ_le : (∀ n, f (n + 1) ≤ f n) → Antitone f`: for a sequence on `ℕ`, one-step
decrease is enough. Placeholders: `(f : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Antitone f` | `⊢ ∀ (n : ℕ), f (n + 1) ≤ f n` |

**R19 · `refine ⟨c, ?_⟩`** on `BddBelow s` changes the **goal**: `BddBelow s` is `∃ c, c ∈ lowerBounds s`,
so you give the bound `c` and prove it is one. Placeholders: `(f : ℕ → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ BddBelow (Set.range f)` | `⊢ c ∈ lowerBounds (Set.range f)` |

**R20 · `rintro _ ⟨n, rfl⟩`** changes the **goal and the context**. `c ∈ lowerBounds (Set.range f)`
unfolds to `∀ y, y ∈ Set.range f → c ≤ y`, and `y ∈ Set.range f` is `∃ n, f n = y`. `rintro` introduces
`y` (as `_`), takes the `∃` apart into `n`, and `rfl` replaces `y` by `f n`. Placeholders:
`(f : ℕ → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ c ∈ lowerBounds (Set.range f)` | `n : ℕ ⊢ c ≤ f n` |

Inline, as in the solution: `⟨c, by rintro _ ⟨n, rfl⟩; exact hc n⟩ : BddBelow (Set.range f)`.

**R21 · `apply tendsto_atTop_ciInf`** changes the **goal list**: monotone convergence. The lemma is
`tendsto_atTop_ciInf : Antitone f → BddBelow (Set.range f) → Tendsto f atTop (𝓝 (⨅ i, f i))`.
Placeholders: `(f : ℕ → ℝ)`; as a term, `tendsto_atTop_ciInf anti bdd`.

| Before | After |
|---|---|
| `⊢ Tendsto f atTop (𝓝 (⨅ i, f i))` | `⊢ Antitone f`, `⊢ BddBelow (Set.range f)` |

**R22 · `apply le_ciInf`** changes the **goal**. The lemma is `le_ciInf : (∀ i, c ≤ f i) → c ≤ ⨅ i, f i`:
a lower bound of all values is below the infimum. Placeholders: `(f : ℕ → ℝ) (c : ℝ)`; as a term,
`le_ciInf hge : √a ≤ ⨅ n, g n` from `hge : ∀ n, √a ≤ g n`.

| Before | After |
|---|---|
| `⊢ c ≤ ⨅ i, f i` | `⊢ ∀ (x : ℕ), c ≤ f x` |

### Identifying the limit

**R23 · `hx.ne'`** changes the **context** (with `have`): `LT.lt.ne' : 0 < x → x ≠ 0` (`ne'` is the
flipped `x ≠ 0`; `hx.ne` would be `0 ≠ x`). Placeholders: `(x : ℝ) (hx : 0 < x)`.

| Before | After |
|---|---|
| `⊢ G` | `h : x ≠ 0 ⊢ G` |

**R24 · `fun_prop (disch := exact h)`** **closes** a goal `ContinuousAt (fun x => …) L` by combining
continuity of `+`, `*`, `/`, constants and `x`. Division by `x` is continuous only where `x ≠ 0`; that
side goal is proved by the tactic after `disch :=`. `fun_prop` does not look inside a named `def`:
`unfold` it first (R1, W1). Placeholders: `(L : ℝ) (hL : L ≠ 0)`.

| Before | After |
|---|---|
| `hL : L ≠ 0 ⊢ ContinuousAt (fun x => x / 2 + 1 / x) L` | closed |

**R25 · `have t := hf.tendsto`** changes the **context**. The lemma is
`ContinuousAt.tendsto : ContinuousAt f x → Tendsto f (𝓝 x) (𝓝 (f x))`. Placeholders:
`(f : ℝ → ℝ) (x : ℝ) (hf : ContinuousAt f x)`.

| Before | After |
|---|---|
| `⊢ G` | `t : Tendsto f (𝓝 x) (𝓝 (f x)) ⊢ G` |

**R26 · `have t := hg.comp hu`** changes the **context**. The lemma is
`Tendsto.comp : Tendsto g l₂ l₃ → Tendsto u l₁ l₂ → Tendsto (g ∘ u) l₁ l₃`: if `u n → L` and `g z → g L`
as `z → L`, then `g (u n) → g L`. Because `(g ∘ u) n` is `g (u n)` by definition, you may state the
`have` as `Tendsto (fun n => g (u n)) atTop (𝓝 (g L))`. Placeholders: `(g : ℝ → ℝ) (u : ℕ → ℝ) (L : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `t : Tendsto (g ∘ u) atTop (𝓝 (g L)) ⊢ G` |

**R27 · `have t := tendsto_add_atTop_nat 1`** changes the **context**:
`tendsto_add_atTop_nat k : Tendsto (fun n => n + k) atTop atTop`. Composed with it (R26),
`hu.comp (tendsto_add_atTop_nat 1)` says `u (n + 1) → L`.

| Before | After |
|---|---|
| `⊢ G` | `t : Tendsto (fun a => a + 1) atTop atTop ⊢ G` |

**R28 · `have e := tendsto_nhds_unique h₁ h₂`** changes the **context**. The lemma is
`tendsto_nhds_unique : Tendsto u l (𝓝 a) → Tendsto u l (𝓝 b) → a = b` (limits in `ℝ` are unique). Both
hypotheses must be about the **same** sequence, up to definition (R10): `fun n => babylon a (g n)` and
`fun n => g (n + 1)` qualify. Placeholders: `(u : ℕ → ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `h₁ : Tendsto u atTop (𝓝 a), h₂ : Tendsto u atTop (𝓝 b) ⊢ G` | `e : a = b ⊢ G` |

**R29 · `rw [← tendsto_add_atTop_iff_nat 1]`** changes the **goal**. The lemma is
`tendsto_add_atTop_iff_nat (k : ℕ) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f atTop l`: a
sequence converges iff its shift does. Right to left it replaces the goal by the shifted one.
Placeholders: `(f : ℕ → ℝ) (l : Filter ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto f atTop l` | `⊢ Tendsto (fun n => f (n + 1)) atTop l` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a named map is continuous.** `fun_prop` cannot see inside `step`, so unfold it (R1), then R24
with `hL.ne'` (R23):

```lean-goal
⊢ ContinuousAt step L
⊢ ContinuousAt (fun x => x / 2 + 1 / x) L
```

**W2: monotone convergence for a decreasing `u ≥ 0`.** `apply tendsto_atTop_ciInf` (R21), then
`antitone_nat_of_succ_le hdec` (R18) and `refine ⟨0, ?_⟩; rintro _ ⟨n, rfl⟩; exact hlow n` (R19, R20).
The bound on the limit is `le_ciInf hlow` (R22):

```lean-goal
⊢ Tendsto u atTop (𝓝 (⨅ n, u n)) ∧ 0 ≤ ⨅ n, u n
⊢ 0 ≤ ⨅ n, u n
```

**W3: identifying the limit of `w (n + 1) = w n / 2 + 1`.** With `h : Tendsto (half x₀) atTop (𝓝 L)`:
`hc` by `fun_prop` (R24); `t₁ := hc.tendsto.comp h` (R25, R26) and `t₂ := h.comp (tendsto_add_atTop_nat 1)`
(R26, R27) are limits of the same sequence (R10), so `tendsto_nhds_unique t₁ t₂ : L / 2 + 1 = L` (R28),
and `linarith` (R6) gives `L = 2`. The states along the way:

```lean-goal
⊢ L = 2
```

| Hypothesis added | |
|---|---|
| `hc : ContinuousAt (fun x => x / 2 + 1) L ⊢ L = 2` | R24 |
| `t₁ : Tendsto (fun n => half x₀ n / 2 + 1) atTop (𝓝 (L / 2 + 1)) ⊢ L = 2` | R25, R26 |
| `t₂ : Tendsto (fun n => half x₀ (n + 1)) atTop (𝓝 L) ⊢ L = 2` | R26, R27 |
| `e : L / 2 + 1 = L ⊢ L = 2` | R28 |

---

## Traps

- `fun_prop` treats a named `def` (`babylon a`) as a black box: `unfold babylon` first, then
  `fun_prop (disch := exact hL0.ne')` (W1).
- `field_simp` needs to know each denominator is nonzero. Have `0 < x` (or `x ≠ 0`) in the context
  before calling it; otherwise it leaves the `/` in place.
- `√a ^ 2 = a` is `Real.sq_sqrt` (R2); `√(a ^ 2) = a` is `Real.sqrt_sq` (R16). Both need `0 ≤ a`.
- `linarith` does not multiply hypotheses. `a ≤ x * x` from `√a ≤ x` needs `nlinarith` with the hints
  `Real.sqrt_nonneg a` and `Real.sq_sqrt ha` (R4).
- `heron_ge` is about `heron a x₀ (n + 1)`, not `n`: `x₀` itself may be below `√a`. That is why the
  limit proof works with the shifted sequence `g` and shifts back at the end (R29).
- `set` only rewrites what exists when it runs. After `rw [← tendsto_add_atTop_iff_nat 1]` the goal
  prints `fun n => heron a x₀ (n + 1)` rather than `g`; `exact tg` still works, because `g` is that
  function by definition.
- `rw [← fixed_point_eq_sqrt a L hL0 hfix]` rewrites `√a` into `L` in the goal (the lemma's right side
  is `√a`).
- `tendsto_nhds_unique` needs both limits for literally the same sequence up to unfolding: compose
  `tg` with the shift (R27) for `fun n => g (n + 1)`, and `hc.tendsto` with `tg` for
  `fun n => babylon a (g n)`; these agree by definition (R10).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold a definition in the goal / in `h` | `unfold babylon` / `unfold babylon at h` | R1, R14 |
| `√a ^ 2 = a` | `Real.sq_sqrt ha` | R2 |
| clear denominators in the goal / in `h` | `field_simp` / `field_simp at h` | R3, R15 |
| nonlinear (in)equality | `nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt ha]` | R4, R8 |
| `0 ≤ square / positive` | `positivity` | R5 |
| linear consequence | `linarith` | R6 |
| `a / c ≤ b` → `a ≤ b * c` | `rw [div_le_iff₀ hc]` | R7 |
| induction | `induction n with \| zero => … \| succ n ih => …` | R9 |
| `heron a x₀ (n + 1)` as a step | nothing: it is `babylon a (heron a x₀ n)` by definition | R10 |
| `<` → `≤`, `0 <` → `≠ 0` | `h.le`, `h.ne'` | R11, R23 |
| chain `<` and `≤` | `lt_of_lt_of_le h₁ h₂` | R12 |
| `0 < √a` | `Real.sqrt_pos.mpr ha` | R13 |
| `√(L ^ 2) = L` | `rw [Real.sqrt_sq hL.le]` | R16 |
| name a subterm | `set g := fun n => heron a x₀ (n + 1) with hg` | R17 |
| decreasing sequence | `antitone_nat_of_succ_le fun n => …` | R18 |
| bounded below | `⟨c, by rintro _ ⟨n, rfl⟩; exact h n⟩` | R19, R20 |
| monotone convergence | `tendsto_atTop_ciInf anti bdd` | R21 |
| bound on the infimum | `le_ciInf h` | R22 |
| continuity at `L ≠ 0` | `unfold babylon; fun_prop (disch := exact hL0.ne')` | R1, R24 |
| push a limit through `f` | `hc.tendsto.comp tg` | R25, R26 |
| limit of the shifted sequence | `tg.comp (tendsto_add_atTop_nat 1)` | R26, R27 |
| two limits of one sequence are equal | `tendsto_nhds_unique t₁ t₂` | R28 |
| prove the limit of a shift instead | `rw [← tendsto_add_atTop_iff_nat 1]` | R29 |
