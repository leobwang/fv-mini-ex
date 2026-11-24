# M158 · Maximum entropy: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's finite sums `∑`, finite types
(`Fintype`, `Fintype.card`), the casts `ℕ → ℝ`, `Real.log` and `Real.negMulLog`, concavity
(`ConcaveOn`) and Jensen's inequality (`ConcaveOn.le_map_sum`), and rewriting inequalities in `ℝ`.

The math. With `Ω = Fintype.card ι` states and weights `wᵢ = 1/Ω`, Jensen for the concave function
`φ(x) = -x log x` gives `(1/Ω) ∑ᵢ φ(pᵢ) ≤ φ((1/Ω) ∑ᵢ pᵢ) = φ(1/Ω) = (log Ω)/Ω`; multiply by `Ω`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is a whole goal the step does not touch; `g : … → G` is only there
  to finish the example once the context has gained the new fact.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Fintype α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `[Fintype ι]` | `ι` is a finite type; `Finset.univ : Finset ι` is the set of all its elements |
| `[Nonempty ι]` | `ι` has at least one element (so `Fintype.card ι ≥ 1`) |
| `inst✝ : Fintype α`, `a✝ : i ∈ Finset.univ` | a hypothesis without a usable name (an instance, or one introduced as `_`); you never refer to it |
| `Fintype.card ι` | the number of elements of `ι`, a natural number (the `Ω` of the problem) |
| `Finset ι` | a finite set of elements of `ι`; `t.card` is its number of elements |
| `∑ i, f i` | `∑ i ∈ Finset.univ, f i`: the sum over all of `ι` |
| `∑ i ∈ t, f i` | the sum of `f i` over `i` in the finite set `t` |
| `∑ _i, b` | a sum whose summand does not depend on the index |
| `∀ i ∈ t, Q i` | `∀ i, i ∈ t → Q i`: a proof takes two arguments, `fun i hi => …` (R5's side goals) |
| `↑k` | the natural number `k` cast to `ℝ` (`Real.log (Fintype.card ι)` hides one: it is `log ↑(Fintype.card ι)`) |
| `log x` | `Real.log x`, the natural log; Mathlib sets `log 0 = 0` and `log x = log (abs x)` for `x < 0` |
| `x.negMulLog` | `Real.negMulLog x = -x * log x` (so `negMulLog 0 = 0`), printed with dot notation |
| `x⁻¹`, `a / b` | inverse and division in `ℝ`; Mathlib sets `0⁻¹ = 0`, `a / 0 = 0` |
| `a • b` | scalar multiplication; for `a b : ℝ` it is `a * b` (R11); for `k : ℕ` it is `k`-fold addition (R9) |
| `Set.Ici a` | the interval `[a, ∞)`, as a `Set ℝ` |
| `ConcaveOn ℝ s f` | `s` is convex and `f (a • x + b • y) ≥ a • f x + b • f y` for `x y ∈ s`, `a b ≥ 0`, `a + b = 1` |
| `x : ℝ := ↑k` | a local definition made by `set` (R1): `x` is a name for `↑k` |
| `![x, y]` | the vector `Fin 2 → ℝ` with entries `x`, `y` (W1) |
| `case refine_1` | the goal created by the first `?_`; after `have hJ := f ?_ ?_ ?_` the main goal comes first, as `case refine_4` |

---

## Part 1 · `max_entropy`

Statement: for `p : ι → ℝ` with `0 ≤ p i` and `∑ i, p i = 1`, `∑ i, negMulLog (p i) ≤ log Ω`.

### Naming `Ω` and proving it is positive

**R1 · `set x : T := e with hx`** changes the **context and the goal**: it adds the local definition
`x : T := e` and the equation `hx : x = e`, and replaces every `e` in the goal by `x`. Placeholders:
`(k : ℕ)`, with `e = (k : ℝ)`. Use it so that `↑(Fintype.card ι)` gets the short name `n`.

| Before | After |
|---|---|
| `⊢ P ↑k` | `x : ℝ := ↑k, hx : x = ↑k ⊢ P x` |

**R2 · `Fintype.card_pos`** **closes** `0 < Fintype.card α`. The statement is
`[Fintype α] [Nonempty α] : 0 < Fintype.card α`; Lean finds both instances itself. Placeholders:
`{α : Type} [Fintype α] [Nonempty α]`.

| Before | After |
|---|---|
| `⊢ 0 < Fintype.card α` | closed |

**R3 · `exact_mod_cast h`** **closes** a goal that is `h` once casts are moved out of the way. Here
`h : 0 < k` lives in `ℕ` and the goal `0 < ↑k` in `ℝ`. Placeholders: `(k : ℕ) (h : 0 < k)`. In the problem,
`h` is R2: `exact_mod_cast Fintype.card_pos`.

| Before | After |
|---|---|
| `h : 0 < k ⊢ 0 < ↑k` | closed |

### Jensen's inequality

**R4 · `Real.concaveOn_negMulLog`** changes the **context** when you `have` it. The statement is
`ConcaveOn ℝ (Set.Ici 0) negMulLog`: `x ↦ -x log x` is concave on `[0, ∞)`. You will not `have` it in the
problem: you use it with dot notation, `Real.concaveOn_negMulLog.le_map_sum` (R5).

| Before | After |
|---|---|
| `⊢ G` | `hc : ConcaveOn ℝ (Set.Ici 0) negMulLog ⊢ G` |

**R5 · `ConcaveOn.le_map_sum`** (Jensen) changes the **context and the goal list**. The statement is

    hf : ConcaveOn ℝ s f →  (∀ i ∈ t, 0 ≤ w i) → ∑ i ∈ t, w i = 1 → (∀ i ∈ t, p i ∈ s) →
      ∑ i ∈ t, w i • f (p i) ≤ f (∑ i ∈ t, w i • p i)

Placeholders: `(s : Set ℝ) (f : ℝ → ℝ) (hf : ConcaveOn ℝ s f)`, an index type `{ι : Type}`, a finite set
`(t : Finset ι)`, weights and points `(w p : ι → ℝ)`. `t`, `w`, `p` are *implicit* arguments: Lean
infers them from the three hypotheses. When you write `?_` for the hypotheses, nothing fixes them, so name
them: `(t := Finset.univ) (w := fun _ => 1 / n) (p := p)`. With
`have hJ := hf.le_map_sum (t := t) (w := w) (p := p) ?_ ?_ ?_`, the context gains
`hJ : ∑ i ∈ t, w i • f (p i) ≤ f (∑ i ∈ t, w i • p i)`, and each `?_` becomes a goal *after* the main one.
You can also prove the three hypotheses inline, as `(fun _ _ => by …) (by …) (fun i _ => …)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, `⊢ ∀ i ∈ t, 0 ≤ w i`, `⊢ ∑ i ∈ t, w i = 1`, `⊢ ∀ i ∈ t, p i ∈ s` |

`∀ i ∈ t, Q i` means `∀ i, i ∈ t → Q i`, so an inline proof takes two arguments: `fun i _ => …`.

**R6 · `positivity`** **closes** a goal `0 ≤ e` or `0 < e` when `e` is built from positive pieces (numerals,
casts of naturals, `/`, `*`, squares, …). Placeholders: `(k : ℕ)`. It proves the weight condition once you are inside `fun _ _ => by positivity`: on
the side goal `∀ i ∈ Finset.univ, 0 ≤ 1 / n` itself it fails with "not a positivity goal". It sees through
the `set` name `n := ↑(Fintype.card ι)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ 1 / ↑k` | closed |

**R7 · `Finset.sum_const`** changes the **goal**. The lemma is `∑ _x ∈ s, b = s.card • b`: a sum of a constant
is the number of terms times the constant. Placeholders: `{ι : Type} (t : Finset ι) (b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ _i ∈ t, b)` | `⊢ P (t.card • b)` |

**R8 · `Finset.card_univ`** changes the **goal**. The lemma is `Finset.univ.card = Fintype.card α`.
Placeholders: `{α : Type} [Fintype α]`, with `P : ℕ → Prop`.

| Before | After |
|---|---|
| `⊢ P Finset.univ.card` | `⊢ P (Fintype.card α)` |

**R9 · `nsmul_eq_mul`** changes the **goal**. The lemma is `k • a = ↑k * a` for `k : ℕ` in a ring such as
`ℝ`: `k`-fold addition becomes multiplication by the cast `↑k`. Placeholders: `(k : ℕ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (k • a)` | `⊢ P (↑k * a)` |

For the side goal `∑ i, 1 / n = 1`, `simp [Finset.card_univ, ← hn]` applies R14, R7, R8, R9, turns
`↑(Fintype.card ι)` back into `n` with `← hn`, and closes `n * n⁻¹ = 1` (W2 shows R7–R9 together).

**R10 · `Set.mem_Ici`** changes the **goal**. The lemma is `x ∈ Set.Ici a ↔ a ≤ x`. Placeholders: `(a x : ℝ)`.
Both sides are the same by definition, so `hp i : 0 ≤ p i` proves `p i ∈ Set.Ici 0` directly, without
the `rw`.

| Before | After |
|---|---|
| `⊢ x ∈ Set.Ici a` | `⊢ a ≤ x` |

### Simplifying Jensen's inequality

`rw` cannot rewrite under the bound variable of `∑`; `simp only [lemma]` can. Add `at h` to act on a
hypothesis `h` instead of the goal: the same change then happens to `h`.

**R11 · `smul_eq_mul`** changes the **goal**. The lemma is `a • b = a * b` (in `ℝ`, `•` with a real scalar
is `*`). Placeholders: `{ι : Type} (t : Finset ι) (a : ℝ) (f : ι → ℝ)`. `simp` renames the bound variable
to `x`; that is the same sum.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ t, a • f i)` | `⊢ P (∑ x ∈ t, a * f x)` |

**R12 · `← Finset.mul_sum`** changes the **goal**. The lemma is `Finset.mul_sum : a * ∑ i ∈ s, f i =
∑ i ∈ s, a * f i`; right to left, it pulls a constant factor out of a sum. Placeholders as in R11.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ t, a * f i)` | `⊢ P (a * ∑ i ∈ t, f i)` |

After R11, R12 and `hs` (which turns `∑ i, p i` into `1`), the problem's `hJ` reads
`1 / n * ∑ i, (p i).negMulLog ≤ (1 / n * 1).negMulLog`.

### Evaluating `negMulLog (1 / n * 1)`

**R13 · `Real.negMulLog`** changes the **goal**: `simp only [Real.negMulLog]` unfolds the definition
`negMulLog x = -x * log x`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P x.negMulLog` | `⊢ P (-x * log x)` |

**R14 · `one_div`** changes the **goal**. The lemma is `1 / a = a⁻¹`. Placeholders: `(a : ℝ)`. `simp` uses it
by itself, so after `simp` you see `n⁻¹`, not `1 / n`.

| Before | After |
|---|---|
| `⊢ P (1 / a)` | `⊢ P a⁻¹` |

**R15 · `Real.log_inv`** changes the **goal**. The lemma is `log x⁻¹ = -log x`, true for every real `x`
(both sides are `0` at `x = 0`). Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (log x⁻¹)` | `⊢ P (-log x)` |

**R16 · `field_simp`** **closes** (or simplifies) an equation of fractions by clearing denominators. It needs
to know the denominators are nonzero: keep `ha : a ≠ 0` (or `0 < a`) in the context. Placeholders:
`(a b : ℝ) (ha : a ≠ 0)`. In the problem, `simp [Real.negMulLog, Real.log_inv]` leaves the shape below
(W3), and `field_simp` closes it.

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ a⁻¹ * b = b / a` | closed |

### Multiplying by `n` and cancelling

**R17 · `ha.le`** changes the **context** when you `have` it. `ha.le` is `LT.lt.le ha : 0 ≤ a` for
`ha : 0 < a` (dot notation: `ha` has type `0 < a`, an `LT.lt`). Placeholders: `(a : ℝ) (ha : 0 < a)`.

| Before | After |
|---|---|
| `ha : 0 < a ⊢ G` | `ha' : 0 ≤ a ⊢ G` |

**R18 · `mul_le_mul_of_nonneg_left`** changes the **context**. The lemma is `b ≤ c → 0 ≤ a → a * b ≤ a * c`.
Placeholders: `(a b c : ℝ) (h : b ≤ c) (ha : 0 ≤ a)`. In the problem, `a` is `n`, `h` is `hJ`, and the
`0 ≤ n` comes from R17.

| Before | After |
|---|---|
| `h : b ≤ c, ha : 0 ≤ a ⊢ G` | `h2 : a * b ≤ a * c ⊢ G` |

**R19 · `ha.ne'`** changes the **context** when you `have` it. `ha.ne'` is `LT.lt.ne' ha : a ≠ 0` for
`ha : 0 < a` (`ne` without the prime gives `0 ≠ a`). Placeholders: `(a : ℝ) (ha : 0 < a)`. R21 and R23 need it.

| Before | After |
|---|---|
| `ha : 0 < a ⊢ G` | `ha' : a ≠ 0 ⊢ G` |

**R20 · `← mul_assoc`** changes the **goal**. The lemma is `mul_assoc : a * b * c = a * (b * c)`; right to left
it regroups to the left. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a * (b * c))` | `⊢ P (a * b * c)` |

**R21 · `mul_one_div_cancel ha`** changes the **goal**. The lemma is `a ≠ 0 → a * (1 / a) = 1`.
Placeholders: `(a : ℝ) (ha : a ≠ 0)`.

| Before | After |
|---|---|
| `⊢ P (a * (1 / a))` | `⊢ P 1` |

**R22 · `one_mul`** changes the **goal**. The lemma is `1 * a = a`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

**R23 · `mul_div_cancel₀ b ha`** changes the **goal**. The lemma is `mul_div_cancel₀ (b : G₀) (ha : a ≠ 0) :
a * (b / a) = b`; `G₀` is a type with `0`, `*`, `⁻¹` in which `*` commutes (`ℝ` qualifies). The explicit
argument `b` may be `_` when `rw` can find it. Placeholders: `(a b : ℝ) (ha : a ≠ 0)`.

| Before | After |
|---|---|
| `⊢ P (a * (b / a))` | `⊢ P b` |

**R24 · `rwa [e] at h`** **closes** the goal: it rewrites the hypothesis `h` with `e` (or a list of
rewrites), then finishes with `h` (`assumption`). Placeholders: `(a b : ℝ) (e : a = b) (h : P a)`.

| Before | After |
|---|---|
| `e : a = b, h : P a ⊢ P b` | closed |

### Worked combinations (on objects that are not the exercise's)

**W1: Jensen with two points.** For `f` concave on `[0, ∞)` and `x y ≥ 0`, R5 with
`(t := Finset.univ) (w := fun _ : Fin 2 => 1 / 2) (p := ![x, y])`, side goals by R6, `simp` and
`fin_cases i <;> simpa` (R10 by definition). `simpa [l] using h` runs `simp [l]` on both `h` and the goal,
then closes the goal with the simplified `h`. So `simpa [Fin.sum_univ_two] using hJ` closes the goal:
`Fin.sum_univ_two : ∑ i : Fin 2, f i = f 0 + f 1`, and `simp` applies R11 itself.

```lean-goal
⊢ 1 / 2 * f x + 1 / 2 * f y ≤ f (1 / 2 * x + 1 / 2 * y)
```

**W2: a constant sum.** `simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]` (R7, R8, R9) closes

```lean-goal
⊢ ∑ _i, b = ↑(Fintype.card α) * b
```

**W3: `negMulLog` at `1/3`.** `simp [Real.negMulLog, Real.log_inv]` (R13, R14, R15) goes from the first goal
to the second; `field_simp` (R16) closes it.

```lean-goal
⊢ (1 / 3).negMulLog = log 3 / 3
⊢ 3⁻¹ * log 3 = log 3 / 3
```

**W4: undoing `1 / a` and `/ a`.** From `h : 1 / a * x ≤ y / a` and `ha : 0 < a`: R18 with R17 gives
`h2 : a * (1 / a * x) ≤ a * (y / a)`; then R24 with R20, R21, R22, R23 (each with R19) turns `h2` into
`x ≤ y` and closes

```lean-goal
⊢ x ≤ y
```

---

## Part 2 · `uniform_attains`

Statement: `∑ _i : ι, negMulLog (1 / Ω) = log Ω`, with `Ω = ↑(Fintype.card ι)`. The sum is `Ω` copies of
`-(1/Ω) log (1/Ω) = (1/Ω) log Ω`.

One `simp [Real.negMulLog, Real.log_inv, Finset.card_univ]` does it: R13, R14, R15 evaluate the summand,
R7, R8, R9 the constant sum, and the last step is R25. A positivity fact `0 < (Fintype.card ι : ℝ)` (R3 with
R2) does no harm but `simp` does not need it.

**R25 · `mul_inv_cancel_left₀ ha`** changes the **goal**. The lemma is `a ≠ 0 → a * (a⁻¹ * b) = b`.
Placeholders: `(a b : ℝ) (ha : a ≠ 0)`. `simp` applies it by itself and proves `↑(Fintype.card ι) ≠ 0`
with `Nat.cast_eq_zero` (`(↑k : ℝ) = 0 ↔ k = 0`) and `Fintype.card_ne_zero` (`Fintype.card α ≠ 0` for a
nonempty `α`).

| Before | After |
|---|---|
| `⊢ P (a * (a⁻¹ * b))` | `⊢ P b` |

---

## Traps

- The `BANNED:` names `Hₛ_le_log_d`, `Hₛ_uniform`, `Sᵥₙ_le_log_d` are physlib's Shannon / von Neumann
  max-entropy lemmas (reachable by adding an import); the point is the Jensen argument. `try?` is banned
  because it can run for many minutes on these goals.
- `Real.log (Fintype.card ι)` contains a cast `ℕ → ℝ`: it is `log ↑(Fintype.card ι)`. A fact about
  `Fintype.card ι` in `ℕ` needs `exact_mod_cast` (R3) to be used in `ℝ`.
- With `?_` for Jensen's hypotheses, name `t`, `w`, `p` (R5); otherwise Lean cannot tell which sum you mean.
- After `set n := … with hn`, a goal may show `↑(Fintype.card ι)` again (for example inside a `simp`);
  `← hn` turns it back into `n`.
- `rw` fails under `∑ i, …` (the bound `i` blocks it): use `simp only […]` (R11, R12).
- Jensen's side goals start with `∀ i ∈ Finset.univ, …`: take the two arguments first (`fun _ _ => by positivity`,
  `fun i _ => hp i`); `positivity` on the `∀` itself fails.
- `simp` turns `1 / n` into `n⁻¹` (R14). State facts you want to `rw` with in the form the goal has.
- Cancellation lemmas need `n ≠ 0`, not `0 < n`: pass `hn0.ne'` (R19); `mul_le_mul_of_nonneg_left` needs
  `0 ≤ n`: pass `hn0.le` (R17).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| short name for `↑(Fintype.card ι)` | `set n : ℝ := (Fintype.card ι : ℝ) with hn` | R1 |
| `0 < Fintype.card α` | `Fintype.card_pos` | R2 |
| move a `ℕ` fact into `ℝ` | `exact_mod_cast h` | R3 |
| `negMulLog` is concave on `[0, ∞)` | `Real.concaveOn_negMulLog` | R4 |
| Jensen | `hf.le_map_sum (t := …) (w := …) (p := …) h0 h1 hm` | R5 |
| `0 ≤ 1 / ↑k` | `positivity` | R6 |
| sum of a constant | `Finset.sum_const`, `Finset.card_univ`, `nsmul_eq_mul` | R7, R8, R9 |
| `x ∈ Set.Ici a` | `Set.mem_Ici`, or just a proof of `a ≤ x` | R10 |
| `•` → `*`, pull a factor out of `∑` | `simp only [smul_eq_mul, ← Finset.mul_sum] at h` | R11, R12 |
| unfold `negMulLog` | `simp [Real.negMulLog, Real.log_inv]` | R13, R14, R15 |
| `a⁻¹ * b = b / a` | `field_simp` | R16 |
| `0 < a` → `0 ≤ a` / `a ≠ 0` | `ha.le` / `ha.ne'` | R17, R19 |
| multiply `b ≤ c` by `a ≥ 0` | `mul_le_mul_of_nonneg_left h ha` | R18 |
| regroup / cancel | `← mul_assoc`, `mul_one_div_cancel`, `one_mul`, `mul_div_cancel₀` | R20–R23 |
| rewrite a hypothesis and close with it | `rwa [...] at h` | R24 |
| `a * (a⁻¹ * b) = b` | `mul_inv_cancel_left₀ ha` (`simp` finds it) | R25 |
| see the state | infoview | |
