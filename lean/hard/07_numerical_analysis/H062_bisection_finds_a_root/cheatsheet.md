# H062 · Bisection finds a root: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). Milestones 1–2 are the two theorems of
M106 (Bisection invariants); if you solved it, paste your proofs. **New here:** Mathlib's real numbers `ℝ`
as an ordered field, monotone sequences, the supremum `⨆` of a bounded sequence, and limits written with
`Filter.Tendsto`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal, and `k : … → G` only consumes a new hypothesis.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid M]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it; `ℝ` meets all of them.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

Throughout, write `lo n` for `(bisect f a b n).1` and `hi n` for `(bisect f a b n).2`: the left and right
end of the interval after `n` bisection steps.

| You see | It means |
|---|---|
| `ℝ × ℝ`, `(x, y)` | pairs of reals; `p.1`, `p.2` are the first and second component |
| `(x, y).1` | the projection of a literal pair; `simp only` reduces it to `x` (R5) |
| `if c then x else y` | `x` when the proposition `c` holds, else `y`; Lean needs `c` decidable |
| `inst✝ : Decidable c` | an anonymous instance: Lean can decide `c` (for `f m ≤ 0` on reals, classically) |
| `case pos`, `case neg` | after `split_ifs`: the branch where the condition holds / fails |
| `case refine_1`, `case refine_2`, … | after `refine ⟨…, ?_, …⟩`: the goals left by the `?_`s, in order |
| `case zero`, `case succ` | after `induction n`: the base case `0` and the step `k + 1` |
| `2 ^ n` with `n : ℕ` | the power with a natural exponent (repeated multiplication), not `Real.rpow` |
| `x⁻¹` | `1 / x`; on `ℝ`, `0⁻¹ = 0` by convention |
| `\|x\|` | absolute value |
| `max m n` | the larger of `m` and `n` |
| `Monotone u` | `∀ ⦃a b⦄, a ≤ b → u a ≤ u b` (nondecreasing); the `⦃⦄` binders are implicit, so `hu hab : u a ≤ u b` |
| `Antitone v` | `∀ ⦃a b⦄, a ≤ b → v b ≤ v a` (nonincreasing) |
| `Set.range u` | the set `{u n \| n : ℕ}` of values of the sequence `u` |
| `upperBounds S` | the set of `x` with `s ≤ x` for every `s ∈ S` |
| `BddAbove S` | `S` has some upper bound: `∃ x, x ∈ upperBounds S` |
| `⨆ i, u i`, `iSup u` | the supremum of the values of `u` (both print; `iSup u` is the same term with the `fun` dropped). On `ℝ` it is the true sup only when `Set.range u` is bounded above (Traps) |
| `s : ℝ := e` | a local definition made by `set` (R22): `s` abbreviates `e` |
| `atTop` | the filter "`n → ∞`" on `ℕ` |
| `𝓝 L` | the filter of neighbourhoods of `L` ("close to `L`"); needs `open Topology` |
| `Tendsto u atTop (𝓝 L)` | `u n → L` as `n → ∞` (`Filter.Tendsto`; needs `open Filter`) |
| `Tendsto g (𝓝 x) (𝓝 (g x))` | `g y → g x` as `y → x`: continuity of `g` at `x` |
| `Continuous g` | `g : ℝ → ℝ` is continuous everywhere |
| `g ∘ u` | composition: `(g ∘ u) n = g (u n)` by definition |
| `fun n => c * u n` | the sequence `n ↦ c · u n`; Lean may rename the bound variable (`fun x => …`) |

---

## Part 1 · `bisect_invariant` (milestone, from M106)

Statement: for every `n`, `f (lo n) ≤ 0`, `0 ≤ f (hi n)`, and `hi n - lo n = (b - a) / 2 ^ n`. The loop
invariant of bisection, by induction on `n`.

**R1 · `induction n with | zero => ?_ | succ k ih => ?_`** changes the **goal list**: one goal per
constructor of `ℕ`. In the step goal, `ih` is the statement for `k`. Placeholders: `(P : ℕ → Prop) (n : ℕ)`.
Writing `?_` after `=>` leaves the case open as a goal; usually you write the case's proof there instead.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `k : ℕ, ih : P k ⊢ P (k + 1)` |

**R2 · `obtain ⟨h1, h2, h3⟩ := h`** changes the **context**: a conjunction `h : A ∧ B ∧ C` is replaced by
its parts. Placeholders: `(A B C : Prop)`. Use it on `ih`.

| Before | After |
|---|---|
| `h : A ∧ B ∧ C ⊢ G` | `h1 : A, h2 : B, h3 : C ⊢ G` |

**R3 · `simp only [iter]`** changes the **goal**: it unfolds a definition by recursion at `n + 1` into the
body of its `n + 1` case. `iter g x n` (defined in the guide) applies `g : α → α` to `x : α` `n` times, as
`bisect f a b n` applies `step f`. In the exercise, `simp only [bisect, step]` unfolds one step of `bisect`
and then the `step`, which is an `if`.

| Before | After |
|---|---|
| `⊢ P (iter g x (n + 1))` | `⊢ P (g (iter g x n))` |

**R4 · `split_ifs with hm`** changes the **goal list and the context**: one goal per branch of the `if`, with
the condition (or its negation) as `hm`. Placeholders: `(c : Prop) [Decidable c] (x y : ℝ × ℝ)`.

| Before | After |
|---|---|
| `⊢ P (if c then x else y)` | `hm : c ⊢ P x`, `hm : ¬c ⊢ P y` |

**R5 · `simp only`** (no lemma list) changes the **goal**: it reduces projections of a literal pair. After
`split_ifs` the goal contains `((lo + hi) / 2, hi).1` and the like.

| Before | After |
|---|---|
| `⊢ P (x, y).1 (x, y).2` | `⊢ P x y` |

**R6 · `rw [pow_succ]`** changes the **goal**. The lemma is `pow_succ : a ^ (n + 1) = a ^ n * a`.
Placeholders: `{M : Type} [Monoid M] (a : M) (n : ℕ)` (a type with an associative `*` and `1`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

**R7 · `rw [← div_div]`** changes the **goal**. The lemma is `div_div : a / b / c = a / (b * c)`; `←` uses it
right to left. Placeholders: `{α : Type} [DivisionCommMonoid α] (a b c : α)` (commutative `*` with `⁻¹`;
`ℝ` qualifies). With R6 it turns `(b - a) / 2 ^ (n + 1)` into `(b - a) / 2 ^ n / 2`, which contains the
invariant's `(b - a) / 2 ^ n`, so `rw [← h3]` can replace it by `hi - lo`.

| Before | After |
|---|---|
| `⊢ P (a / (b * c))` | `⊢ P (a / b / c)` |

**R8 · `linarith`** **closes** a goal that is a linear combination of the hypotheses (`≤`, `<`, `=` over an
ordered field such as `ℝ`). It reads a negated hypothesis `¬x ≤ 0` as `0 < x`, so the `neg` branch of
`split_ifs` gives the sign of `f` at the midpoint directly. It treats non-linear pieces (`f m`, `2 ^ n`,
`lo n`) as unknowns.

| Before | After |
|---|---|
| `hm : ¬x ≤ 0, hy : y ≤ x ⊢ y ≤ 2 * x` | no goals |

**R9 · `ring`** **closes** an identity of commutative rings; division by a numeral such as `/ 2` is fine. It
closes the width goal once `hi - lo` has been substituted.

| Before | After |
|---|---|
| `⊢ y - (x + y) / 2 = (y - x) / 2` | no goals |

## Part 2 · `bisect_nested` (milestone, from M106)

Statement: `a ≤ lo n`, `lo n ≤ lo (n + 1)`, `hi (n + 1) ≤ hi n`, `hi n ≤ b`. No new entries: R1–R5 and R8.
The statement mentions step `n + 1`, so induction on it directly does not go through. First prove the
inductive fact `∀ n, lo n ≤ hi n ∧ a ≤ lo n ∧ hi n ≤ b` with R1, R2, R3, R4, R5, R8, then derive the four
parts: `lo (n + 1)` and `hi (n + 1)` unfold (R3) to an `if` (R4) whose branches `linarith` closes.

## Part 3 · `lo_le_hi` (milestone)

Statement: `lo m ≤ hi n` for all `m, n`. Go through the index `max m n`:
`lo m ≤ lo (max m n) ≤ hi (max m n) ≤ hi n` (monotone, width ≥ 0, antitone).

**R10 · `monotone_nat_of_le_succ`** changes the **goal**: to show a sequence on `ℕ` is monotone it suffices to
compare neighbours. Lemma: `(∀ n, u n ≤ u (n + 1)) → Monotone u`. Placeholders: `(u : ℕ → ℝ)`. In the
exercise, write it as a term: `monotone_nat_of_le_succ fun n => …`.

| Before | After `apply monotone_nat_of_le_succ` |
|---|---|
| `⊢ Monotone u` | `⊢ ∀ (n : ℕ), u n ≤ u (n + 1)` |

**R11 · `antitone_nat_of_succ_le`** changes the **goal**, the mirror image of R10. Lemma:
`(∀ n, v (n + 1) ≤ v n) → Antitone v`. Placeholders: `(v : ℕ → ℝ)`.

| Before | After `apply antitone_nat_of_succ_le` |
|---|---|
| `⊢ Antitone v` | `⊢ ∀ (n : ℕ), v (n + 1) ≤ v n` |

**R12 · `apply div_nonneg`** changes the **goal list**. Lemma: `0 ≤ a → 0 ≤ b → 0 ≤ a / b`. Placeholders:
`(a b : ℝ)`. As a term: `div_nonneg (by linarith) (by positivity)` proves `0 ≤ (b - a) / 2 ^ k` from `a ≤ b`.

| Before | After |
|---|---|
| `⊢ 0 ≤ a / b` | `⊢ 0 ≤ a`, `⊢ 0 ≤ b` |

**R13 · `positivity`** **closes** a goal `0 ≤ e` or `0 < e` (also `e ≠ 0`) when `e` is built from positive
pieces: numerals, powers, squares, sums of those. It does not use hypotheses.

| Before | After |
|---|---|
| `k : ℕ ⊢ 0 < 2 ^ k` | no goals |

**R14 · `calc`** **closes** `x ≤ z` by a chain of steps, each `_ ≤ … := proof`; `_` stands for the previous
right-hand side. Mixed `≤`/`<`/`=` links are allowed. Placeholders: `(x y z : ℝ)`.

| Before | After `calc x ≤ y := h1` / `_ ≤ z := h2` |
|---|---|
| `h1 : x ≤ y, h2 : y ≤ z ⊢ x ≤ z` | no goals |

**R15 · applying `hu : Monotone u` or `hv : Antitone v`** changes the **context**: a proof `hmn : m ≤ n`
gives the inequality between the terms. Placeholders: `(u v : ℕ → ℝ) (m n : ℕ)`.

| Before | After `have h1 := hu hmn` | After `have h2 := hv hmn` |
|---|---|---|
| `hmn : m ≤ n ⊢ G` | `h1 : u m ≤ u n ⊢ G` | `h2 : v n ≤ v m ⊢ G` |

**R16 · `le_max_left`, `le_max_right`** change the **context**: `le_max_left m n : m ≤ max m n` and
`le_max_right m n : n ≤ max m n`. Placeholders: `(m n : ℕ)`. Feed them to R15: `hmono (le_max_left m n)`.

| Before | After `have h1 := le_max_left m n` | After `have h2 := le_max_right m n` |
|---|---|---|
| `m n : ℕ ⊢ G` | `h1 : m ≤ max m n ⊢ G` | `h2 : n ≤ max m n ⊢ G` |

## Part 4 · `gap_tendsto` (milestone)

Statement: `(b - a) / 2 ^ n → 0`. Write the term as `(b - a) * (2⁻¹) ^ n`, use `rⁿ → 0` for `0 ≤ r < 1`,
multiply the limit by `b - a`.

**R17 · `simp_rw [div_eq_mul_inv]`** changes the **goal**. Lemma: `div_eq_mul_inv : a / b = a * b⁻¹`.
`simp_rw` rewrites under `fun n =>`, where `rw` fails (the term mentions the bound `n`). Placeholders:
`(c : ℝ) (u : ℕ → ℝ) (P : (ℕ → ℝ) → Prop)`.

| Before | After |
|---|---|
| `⊢ P fun n => c / u n` | `⊢ P fun n => c * (u n)⁻¹` |

**R18 · `simp_rw [← inv_pow]`** changes the **goal**. Lemma: `inv_pow : a⁻¹ ^ n = (a ^ n)⁻¹`; right to left.
Placeholders: `(c x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P fun n => c * (x ^ n)⁻¹` | `⊢ P fun n => c * x⁻¹ ^ n` |

**R19 · `tendsto_pow_atTop_nhds_zero_of_lt_one`** changes the **context**. Lemma:
`0 ≤ r → r < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)`. Placeholders: `(r : ℝ)`. Prove the two side
conditions for `r = 2⁻¹` with `(by norm_num : (0 : ℝ) ≤ 2⁻¹)` and `(by norm_num)`; the type ascription
tells Lean which `r`.

| Before | After `have h := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1` |
|---|---|
| `h0 : 0 ≤ r, h1 : r < 1 ⊢ G` | `h : Tendsto (fun n => r ^ n) atTop (𝓝 0) ⊢ G` |

**R20 · `Tendsto.const_mul`** changes the **context**. Lemma: `(c : ℝ) → Tendsto u l (𝓝 L) →
Tendsto (fun n => c * u n) l (𝓝 (c * L))`; dot notation `hu.const_mul c`. Placeholders: `(u : ℕ → ℝ) (L c : ℝ)`.

| Before | After `have h := hu.const_mul c` |
|---|---|
| `hu : Tendsto u atTop (𝓝 L) ⊢ G` | `h : Tendsto (fun x => c * u x) atTop (𝓝 (c * L)) ⊢ G` |

**R21 · `simpa using e`** **closes** the goal when `simp` brings the type of `e` and the goal to the same
form. Here it turns `c * 0` into `0`. `simpa [names] using e` also unfolds `names` (as in `simpa [lo, bisect]
using hlo_r 0`, which turns `lo 0` into `a`).

| Before | After |
|---|---|
| `h : Tendsto (fun n => c * u n) atTop (𝓝 (c * 0)) ⊢ Tendsto (fun n => c * u n) atTop (𝓝 0)` | no goals |

## Part 5 · `bisection_finds_root`

Statement: there is `r` with `f r = 0`, `a ≤ r ≤ b`, and `|r - (lo n + hi n) / 2| ≤ (b - a) / 2 ^ (n + 1)` for
every `n`. Take `r := ⨆ n, lo n`. The milestones give `lo m ≤ hi n` (so `lo` is bounded and `r ≤ hi n`),
`lo n → r` (monotone and bounded), `hi n = lo n + (b - a) / 2 ^ n → r + 0`. Continuity of `f` passes the signs
`f (lo n) ≤ 0 ≤ f (hi n)` to `f r ≤ 0 ≤ f r`. The bound is the squeeze `lo n ≤ r ≤ hi n` with
`hi n - lo n = (b - a) / 2 ^ n`.

**R22 · `set s := e with hs`** changes the **context and the goal**: it adds a local definition
`s : ℝ := ⨆ n, u n` and `hs : s = ⨆ n, u n`, and replaces `e` by `s` in the goal and in every hypothesis.
Placeholders: `(u : ℕ → ℝ) (P : ℝ → Prop)`. It replaces only literal copies of `e`: after
`set lo := fun n => (bisect f a b n).1` the goal still shows `(bisect f a b n).1` (no `fun` appears in it),
and only the hypotheses you state afterwards in terms of `lo` are shorter.

| Before | After | New in the context |
|---|---|---|
| `⊢ P (⨆ n, u n)` | `h : P s ⊢ P s` | `s : ℝ := ⨆ n, u n` and `hs : s = ⨆ n, u n` |

**R23 · `refine ⟨b, ?_⟩`** on `BddAbove S` changes the **goal**: `BddAbove S` is an existential, so give
the bound `b`. Placeholders: `(u : ℕ → ℝ) (b : ℝ)`. In the exercise `b` itself works, since `lo m ≤ hi 0 = b`.

| Before | After |
|---|---|
| `⊢ BddAbove (Set.range u)` | `⊢ b ∈ upperBounds (Set.range u)` |

**R24 · `rintro _ ⟨m, rfl⟩`** changes the **goal and the context**: an element of `Set.range u` is `u m` for
some `m`; `rfl` substitutes it. Placeholders: as in R23.

| Before | After |
|---|---|
| `⊢ b ∈ upperBounds (Set.range u)` | `m : ℕ ⊢ u m ≤ b` |

**R25 · `le_ciSup`** changes the **context**. Lemma: `BddAbove (Set.range u) → ∀ n, u n ≤ ⨆ i, u i`
(the `c` is for *conditionally* complete: the sup needs a bound). Placeholders: `(u : ℕ → ℝ) (n : ℕ)`.
Lean prints the result with `iSup u`, the same term as `⨆ i, u i`.

| Before | After `have h := le_ciSup hb n` |
|---|---|
| `hb : BddAbove (Set.range u) ⊢ G` | `h : u n ≤ iSup u ⊢ G` |

**R26 · `apply ciSup_le`** changes the **goal**. Lemma: `(∀ i, u i ≤ c) → ⨆ i, u i ≤ c` (index type
nonempty, as `ℕ` is). Placeholders: `(u : ℕ → ℝ) (c : ℝ)`. In the exercise, for `r ≤ hi n`:
`ciSup_le fun m => lo_le_hi … m n`.

| Before | After |
|---|---|
| `⊢ ⨆ i, u i ≤ c` | `⊢ ∀ (x : ℕ), u x ≤ c` |

**R27 · `tendsto_atTop_ciSup`** **closes** a limit goal: monotone convergence. Lemma:
`Monotone u → BddAbove (Set.range u) → Tendsto u atTop (𝓝 (⨆ i, u i))`. Placeholders: `(u : ℕ → ℝ)`.

| Before | After `exact tendsto_atTop_ciSup hm hb` |
|---|---|
| `hm : Monotone u, hb : BddAbove (Set.range u) ⊢ Tendsto u atTop (𝓝 (⨆ i, u i))` | no goals |

**R28 · `funext n`** changes the **goal and the context**: two functions are equal when they agree at every
point. Placeholders: `(u v : ℕ → ℝ)`. Use it to prove `hi = fun n => lo n + (b - a) / 2 ^ n`, then
`rw` with that equation to turn a limit of `hi` into a limit of a sum.

| Before | After |
|---|---|
| `⊢ u = fun n => v n + 0` | `n : ℕ ⊢ u n = v n + 0` |

**R29 · `simp only [v] at h`** changes the **context**: it unfolds the `set` name `v` (and beta-reduces) inside
`h`. Without `at h` it acts on the goal. `lo n` and `(bisect f a b n).1` are equal by definition, so
`exact` and `linarith` accept either form; `rw` and `simp` lemmas match the literal text, and there the
unfolded form is the one the goal uses. In this exercise R29 is optional (readability). Placeholders: `(u : ℕ → ℝ) (c : ℝ)`, `v := fun n => u n + 1` made by `set`.

| Before | After |
|---|---|
| `h : v 0 ≤ c ⊢ u 0 + 1 ≤ c` | `h : u 0 + 1 ≤ c ⊢ u 0 + 1 ≤ c` |

**R30 · `Tendsto.add`** changes the **context**: limits add. Lemma: `Tendsto u l (𝓝 L) → Tendsto v l (𝓝 M)
→ Tendsto (fun n => u n + v n) l (𝓝 (L + M))`. Placeholders: `(u v : ℕ → ℝ) (L M : ℝ)`. With
`gap_tendsto` the limit is `r + 0`; `simpa using …` (R21) turns it into `r`.

| Before | After `have h := hu.add hv` |
|---|---|
| `hu : Tendsto u atTop (𝓝 L), hv : Tendsto v atTop (𝓝 M) ⊢ G` | `h : Tendsto (fun x => u x + v x) atTop (𝓝 (L + M)) ⊢ G` |

**R31 · `Continuous.tendsto`** changes the **context**: a continuous `g` is continuous at each point. Lemma:
`Continuous g → ∀ x, Tendsto g (𝓝 x) (𝓝 (g x))`. Placeholders: `(g : ℝ → ℝ) (x : ℝ)`.

| Before | After `have h := hg.tendsto x` |
|---|---|
| `hg : Continuous g ⊢ G` | `h : Tendsto g (𝓝 x) (𝓝 (g x)) ⊢ G` |

**R32 · `Tendsto.comp`** changes the **context**: limits compose. Lemma: `Tendsto g y z → Tendsto u x y →
Tendsto (g ∘ u) x z`. Placeholders: `(g : ℝ → ℝ) (u : ℕ → ℝ) (L : ℝ)`. So `(hf.tendsto r).comp tlo` says
`f (lo n) → f r`.

| Before | After `have h := hg.comp hu` |
|---|---|
| `hg : Tendsto g (𝓝 L) (𝓝 (g L)), hu : Tendsto u atTop (𝓝 L) ⊢ G` | `h : Tendsto (g ∘ u) atTop (𝓝 (g L)) ⊢ G` |

**R33 · `le_of_tendsto'`** changes the **goal**: a bound on every term passes to the limit. Lemma:
`Tendsto u l (𝓝 L) → (∀ n, u n ≤ b) → L ≤ b` (Mathlib requires the filter `l` to be `NeBot`, not the trivial filter `⊥`; `atTop` on `ℕ` is).
Placeholders: `(u : ℕ → ℝ) (L b : ℝ)`. For `u = f ∘ lo` the bound may be given as `∀ n, f (lo n) ≤ 0`, which is
the same by definition.

| Before | After `apply le_of_tendsto' hu` |
|---|---|
| `hu : Tendsto u atTop (𝓝 L) ⊢ L ≤ b` | `⊢ ∀ (c : ℕ), u c ≤ b` |

**R34 · `ge_of_tendsto'`** changes the **goal**, the mirror of R33. Lemma:
`Tendsto u l (𝓝 L) → (∀ n, b ≤ u n) → b ≤ L`.

| Before | After `apply ge_of_tendsto' hu` |
|---|---|
| `hu : Tendsto u atTop (𝓝 L) ⊢ b ≤ L` | `⊢ ∀ (c : ℕ), b ≤ u c` |

**R35 · `le_antisymm`** changes the **goal list**. Lemma: `x ≤ y → y ≤ x → x = y`. Placeholders: `(x y : ℝ)`.
As a term: `le_antisymm h1 h2 : f r = 0` from `h1 : f r ≤ 0`, `h2 : 0 ≤ f r`.

| Before | After |
|---|---|
| `⊢ x = y` | `⊢ x ≤ y`, `⊢ y ≤ x` |

**R36 · `rw [abs_le]`** changes the **goal**. Lemma: `abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b`. Placeholders:
`(x c d : ℝ)`. Then `constructor` splits the `∧` and `linarith` closes each side.

Before and after:

```lean-goal
⊢ |x - c| ≤ d
⊢ -d ≤ x - c ∧ x - c ≤ d
```

### Worked combinations (W1–W5, on objects that are not the exercise's)

**W1: an invariant of an iteration (R1, R3, R4, R5, R8).** `shrink I` halves one end of `I`. After R1 and
`simp only [iter, shrink]` (R3) the step goal is an `if`:

```lean-goal
⊢ 0 ≤ (if (iter shrink I k).1 ≤ 0 then ((iter shrink I k).1 / 2, (iter shrink I k).2) else ((iter shrink I k).1, (iter shrink I k).2 / 2)).2
```

`split_ifs with hm` (R4) gives one goal per branch, still with the pair visible; `simp only` (R5) and
`linarith` (R8) finish each:

```lean-goal
⊢ 0 ≤ ((iter shrink I k).1 / 2, (iter shrink I k).2).2
⊢ 0 ≤ ((iter shrink I k).1, (iter shrink I k).2 / 2).2
```

**W2: monotone and bounded.** `⟨1, by rintro _ ⟨m, rfl⟩; exact hb m⟩` proves `BddAbove (Set.range u)`
(R23, R24); then `tendsto_atTop_ciSup (monotone_nat_of_le_succ hu) hbdd` (R10, R27) and `le_ciSup hbdd n` (R25).

**W3: a sign passes to the limit.** `le_of_tendsto' ((hg.tendsto L).comp hu) hneg` proves `g L ≤ 0` from
`u n → L` and `∀ n, g (u n) ≤ 0` (R31 → R32 → R33).

**W4: `c / 3 ^ n → 0`.** R17, then R18, then R19 → R20 → R21:

```lean-goal
⊢ Tendsto (fun n => c / 3 ^ n) atTop (𝓝 0)
⊢ Tendsto (fun n => c * (3 ^ n)⁻¹) atTop (𝓝 0)
⊢ Tendsto (fun n => c * 3⁻¹ ^ n) atTop (𝓝 0)
```

**W5: squeezed means close.** From `l ≤ x ≤ h`, `|x - l| ≤ h - l`: R36, `constructor`, R8 on each side:

```lean-goal
⊢ |x - l| ≤ h - l
⊢ -(h - l) ≤ x - l ∧ x - l ≤ h - l
⊢ -(h - l) ≤ x - l
⊢ x - l ≤ h - l
```

---

## Traps

- The intermediate value theorem gives *a* root, not one within `(b - a) / 2 ^ (n + 1)` of every midpoint.
  The root must be the limit of the bisection: `r := ⨆ n, lo n`.
- On `ℝ`, `⨆ n, u n` is defined for every `u`, but it is the supremum only when `Set.range u` is bounded
  above (otherwise it is a junk value). That is why `le_ciSup` and `tendsto_atTop_ciSup` take a
  `BddAbove` argument: prove `hbdd` first.
- `bisect_nested` mentions step `n + 1`; induction on it directly gets stuck. Prove a stronger statement
  about step `n` alone for all `n` first (Part 2).
- `rw` fails under `fun n =>` when the rewritten term mentions `n` ("motive is not type correct" or "did
  not find instance of the pattern"). Use `simp_rw` (R17).
- After `set lo := … with hlo`, the goal still mentions `(bisect f a b n).1`, not `lo n` (R22). `rw [h]`
  with an `h` about `lo n` will not find it; unfold `h` with `simp only [lo, hi] at h` (R29) first.
  `linarith` and `exact` do not care: `lo n` is `(bisect f a b n).1` by definition.
- In `refine ⟨h2, ?_, ?_, h3⟩` every part is a proof or `?_`; a bare `_` is an error ("don't know how
  to synthesize placeholder").
- `rw [h]` needs the left side of `h` literally: `2 ^ (n + 1)` must first become `2 ^ n * 2` (R6), and
  `x / (y * z)` must become `x / y / z` (R7), before `rw [← h3]` sees `(b - a) / 2 ^ n`.
- `t1 ; t2` runs `t2` on the first goal only. After `split_ifs` or `refine ⟨?_, ?_⟩`, use `<;>` or `·`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on `n : ℕ` | `induction n with \| zero => … \| succ k ih => …` | R1 |
| split a conjunction hypothesis | `obtain ⟨h1, h2, h3⟩ := ih` | R2 |
| unfold one step of `bisect` | `simp only [bisect, step]` | R3 |
| one goal per `if` branch | `split_ifs with hm` | R4 |
| `(x, y).1 → x` | `simp only` | R5 |
| `2 ^ (n + 1) → 2 ^ n * 2` | `rw [pow_succ]` | R6 |
| `w / (p * 2) → w / p / 2` | `rw [← div_div]` | R7 |
| linear arithmetic from hypotheses | `linarith` | R8 |
| ring identity with `/ 2` | `ring` | R9 |
| monotone / antitone from one step | `monotone_nat_of_le_succ fun n => …` / `antitone_nat_of_succ_le …` | R10, R11 |
| `0 ≤ w / 2 ^ k` | `div_nonneg (by linarith) (by positivity)` | R12, R13 |
| chain of inequalities | `calc x ≤ y := … ` / `_ ≤ z := …` | R14 |
| use `Monotone`, `Antitone` | `hmono hmn`, `hanti hmn` | R15 |
| `m ≤ max m n`, `n ≤ max m n` | `le_max_left m n`, `le_max_right m n` | R16 |
| rewrite under `fun` | `simp_rw [div_eq_mul_inv, ← inv_pow]` | R17, R18 |
| `rⁿ → 0` | `tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1` | R19 |
| `c * uₙ → c * L` | `hu.const_mul c` | R20 |
| close up to `simp` | `simpa using e` | R21 |
| name a term | `set r := ⨆ n, lo n with hr` | R22 |
| `BddAbove (Set.range u)` | `⟨b, by rintro _ ⟨m, rfl⟩; exact …⟩` | R23, R24 |
| `u n ≤ ⨆ i, u i` | `le_ciSup hbdd n` | R25 |
| `⨆ i, u i ≤ c` | `ciSup_le fun m => …` | R26 |
| monotone convergence | `tendsto_atTop_ciSup hmono hbdd` | R27 |
| equality of sequences | `funext n` | R28 |
| unfold a `set` name | `simp only [lo, hi] at h` | R29 |
| `uₙ + vₙ → L + M` | `hu.add hv` | R30 |
| `f (uₙ) → f L` | `(hf.tendsto L).comp hu` | R31, R32 |
| bound passes to the limit | `le_of_tendsto' t (fun n => …)` / `ge_of_tendsto' t …` | R33, R34 |
| `x = y` from both `≤` | `le_antisymm h1 h2` | R35 |
| `\|a\| ≤ b` | `rw [abs_le]; constructor <;> linarith` | R36 |
| see the state | infoview | |
