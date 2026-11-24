# H090 · Gibbs variational principle: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `apply`, `rw`, `simp`, `have`, `calc`,
anonymous functions `fun x => …`, `rcases` patterns. `ring` (closes commutative-ring identities) is in
`TACTIC_STATES.md`, "Closing". **New here:** Mathlib's real logarithm and
exponential (`Real.log`, `Real.exp`, `Real.negMulLog`), finite sums `∑` and their algebra (`Finset.sum_*`),
inequality lemmas (`div_pos`, `mul_le_mul_of_nonneg_left`, `div_le_div_of_nonneg_right`), the tactics
`linarith`, `field_simp`, `set`, `calc` steps left open with `?_`, and physlib's `CanonicalEnsemble` with its β-parameterised
partition function and Boltzmann probabilities.

**The physics, in symbols.** Units `k_B = 1`. A finite system has microstates `i ∈ ι` with energies
`E i`. At inverse temperature `b = 1/T > 0`:
$Z = \sum_i e^{-b E_i}$ (partition function), $q_i = e^{-b E_i}/Z$ (Boltzmann probability),
$F = -T \log Z = -\log Z / b$ (free energy). For any probability vector $p$ ($p_i \ge 0$, $\sum_i p_i = 1$),
$\langle E\rangle_p = \sum_i p_i E_i$ and $S(p) = \sum_i -p_i \log p_i$ (Gibbs entropy). Since
$\log q_i = -b E_i - \log Z$,
$$\sum_i p_i(\log q_i - \log p_i) = -b\langle E\rangle_p - \log Z + S(p).$$
The left side is $-D(p\,\|\,q) \le 0$ (relative entropy is nonnegative), from the termwise bound
$x(\log y - \log x) \le y - x$ for $x \ge 0$, $y > 0$ (from $\log t \le t - 1$ at $t = y/x$) summed:
$\le \sum q - \sum p = 0$. Dividing $-\log Z \le b\langle E\rangle_p - S(p)$ by $b > 0$ gives
$F \le \langle E\rangle_p - T S(p)$, with equality at $p = q$.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves alone.
- Lemmas that produce a fact are shown as `have h := lemma args`, so the context gains `h` and you see its
  type. In the exercise you usually pass them as arguments instead (`div_pos (exp_pos _) hZ`).
  `hz.ne'` is dot notation for `LT.lt.ne' hz` (the type of `hz` is `0 < z`, an `LT.lt`).
- Placeholders are real-valued (`ℝ`) here, as in the exercise. The sum lemmas hold in any commutative
  additive monoid or ring, the order lemmas in any ordered field; `ℝ` is the only instance used here.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `inst✝² : Fintype ι` | an instance argument (`[Fintype ι]` in the statement) with no name you can use; `✝` marks an inaccessible name, the superscript only tells them apart |
| `𝓒 : CanonicalEnsemble ι` | a physlib system with microstates of type `ι`; `𝓒.energy : ι → ℝ` is the energy `E` |
| `[Fintype ι]`, `[Nonempty ι]` | finitely many microstates; at least one (needed for `Z > 0`). `[MeasurableSpace ι]` is required by the structure and plays no role here |
| `𝓒.mathematicalPartitionFunctionBetaReal b` | `Z(b) = ∑ i, rexp (-b * 𝓒.energy i)`, a real number |
| `𝓒.probabilityBetaReal b i` | `q_i = rexp (-b * 𝓒.energy i) / Z(b)` (R1) |
| `rexp x` | `Real.exp x`, the real exponential |
| `log x` | `Real.log x` (printed short because of `open Real`). Total function: `log 0 = 0` and `log (-x) = log x` |
| `x.negMulLog` | `Real.negMulLog x = -x * log x` (R25); dot notation, since `x : ℝ` |
| `∑ i, f i` | the sum of `f i` over all `i : ι` (`Finset.univ`, the finite set of all elements) |
| `∑ i ∈ s, f i` | the sum over a finite set `s : Finset ι`; lemma statements use this form, with `s = Finset.univ` here |
| `∑ x, …` | the same sum; after `rw`/`simp` Lean often renames the bound variable to `x` |
| `∀ i ∈ Finset.univ, …` | `∀ i, i ∈ Finset.univ → …`; the membership is always true, discharge it with `fun i _ => …` |
| `L : ℝ := log x` | a local definition made by `set` (R23): `L` abbreviates `log x` |
| `case inl`, `case inr` | the two goals of `rcases h with … \| …` (left and right side of an `∨`) (R9) |
| `case calc_1`, `case calc_2` | the step goals a `calc` with `?_` leaves (R18) |
| `case hab`, `case hc` | the goals `apply` leaves, named after the lemma's hypotheses (R30) |

---

## Part 1 · `sum_boltzmann` (milestone)

Statement: `∑ i, 𝓒.probabilityBetaReal b i = 1`. Unfold `q`, pull the common denominator `Z b` out of
the sum; the numerator is then `Z b` itself (by definition), so it is `a / a = 1`.

**R1 · `simp only [probabilityBetaReal]`** changes the **goal**: the name `q` becomes its definition.
`rw [probabilityBetaReal]` works too when the term is not under a `∑ i, …` binder (Part 2).
Placeholders: `(𝓒 : CanonicalEnsemble ι) (t : ℝ) (i : ι)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.probabilityBetaReal t i)` | `⊢ P (rexp (-t * 𝓒.energy i) / 𝓒.mathematicalPartitionFunctionBetaReal t)` |

**R2 · `Finset.sum_div`** changes the **goal**. The lemma is
`Finset.sum_div : (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`; with `←` it pulls the common `/ a` out of the
sum. Inside `simp only [probabilityBetaReal, ← Finset.sum_div]` both happen in one call.
Placeholders: `(f : ι → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i / a)` | `⊢ P ((∑ i, f i) / a)` |

**R3 · `𝓒.mathematicalPartitionFunctionBetaReal_pos t`** changes the **context**: it is the fact `0 < Z t`
(physlib; it needs `[Nonempty ι]`, since an empty sum is `0`). Placeholders: `(𝓒 : CanonicalEnsemble ι) (t : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hZ : 0 < 𝓒.mathematicalPartitionFunctionBetaReal t ⊢ G` |

**R4 · `hz.ne'`** (`LT.lt.ne'`) changes the **context**: from `hz : 0 < z` it makes `z ≠ 0`, the form
`div_self` and `log_div` want. (`hz.ne` would give `0 ≠ z`.) Placeholders: `(z : ℝ)`.

| Before | After |
|---|---|
| `hz : 0 < z ⊢ z ≠ 0` | `h : z ≠ 0 ⊢ z ≠ 0` |

**R5 · `div_self`** changes the **context**: `div_self : a ≠ 0 → a / a = 1`. With `exact div_self h`,
Lean accepts `(∑ i, rexp (-b * E i)) / Z b = 1` because the numerator unfolds to `Z b` by definition.
Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ a / a = 1` | `h : a / a = 1 ⊢ a / a = 1` |

---

## Part 2 · `log_boltzmann` (milestone)

Statement: `log (q i) = -b * E i - log Z`. Unfold `q i` (R1, as `rw`), split the logarithm of the
quotient (R6), and cancel `log ∘ exp` (R8).

**R6 · `rw [Real.log_div hx hy]`** changes the **goal**. The lemma is
`Real.log_div : x ≠ 0 → y ≠ 0 → log (x / y) = log x - log y`. Both side conditions are passed as arguments:
for `x = rexp (…)` use `(Real.exp_pos _).ne'` (R7, R4), for `y = Z b` use R3 then R4.
Placeholders: `(x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)`.

| Before | After |
|---|---|
| `⊢ P (log (x / y))` | `⊢ P (log x - log y)` |

**R7 · `Real.exp_pos x`** changes the **context**: the fact `0 < rexp x`. `Real.exp_pos _` lets Lean find
`x`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 < rexp x` | `h : 0 < rexp x ⊢ 0 < rexp x` |

**R8 · `rw [Real.log_exp]`** changes the **goal**: `Real.log_exp : log (rexp x) = x`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (log (rexp x))` | `⊢ P x` |

---

## Part 3 · `term_le` (milestone)

Statement: `0 ≤ x → 0 < y → x * (log y - log x) ≤ y - x`. Split `x = 0` from `x > 0`. At `x = 0` both
sides simplify. At `x > 0` apply `log t ≤ t - 1` with `t = y / x`, split `log (y / x)`, and multiply by
`x ≥ 0`; the rest is linear once `x * (y / x - 1) = y - x` is known.

**R9 · `rcases hx.eq_or_lt with rfl | hx'`** changes the **goal list and the context**.
`hx.eq_or_lt : 0 = x ∨ 0 < x` (`LE.le.eq_or_lt`, from `hx : 0 ≤ x`). The pattern `rfl` substitutes `x := 0`
everywhere in the first goal; `hx'` names `0 < x` in the second. Placeholders: `(x : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `hx : 0 ≤ x ⊢ P x` | `hx : 0 ≤ 0 ⊢ P 0`, `hx' : 0 < x ⊢ P x` |

**R10 · `simp`** on the `x = 0` goal changes the **goal**: `zero_mul` and `sub_zero` erase the
`0 * (…)` and `- 0`. In the exercise this turns `0 * (log y - log 0) ≤ y - 0` into `0 ≤ y`, which
`linarith` (R11) closes from `hy : 0 < y`. Placeholders: `(c y : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 * c ≤ y - 0` | `⊢ 0 ≤ y` |

**R11 · `linarith`** **closes** a goal `t ≤ u`, `t < u` or `t = u` that follows from the hypotheses by adding
them with nonnegative coefficients. It first multiplies out products, then treats nonlinear pieces
(`x * log y`, `x * (y / x)`) as unknowns, so it needs the facts about them in the context
(`h2`, `h3` in the skeleton). Pass extra facts as `linarith [h i]`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `h1 : a ≤ b, h2 : b + c ≤ 1, h3 : 0 ≤ c ⊢ a ≤ 1` | no goals |

**R12 · `Real.log_le_sub_one_of_pos hx`** changes the **context**: `0 < x → log x ≤ x - 1`, the inequality
behind Gibbs. Placeholders: `(x : ℝ) (hx : 0 < x)`.

| Before | After |
|---|---|
| `hx : 0 < x ⊢ log x ≤ x - 1` | `h : log x ≤ x - 1 ⊢ log x ≤ x - 1` |

**R13 · `div_pos ha hb`** changes the **context**: `0 < a → 0 < b → 0 < a / b`. Used for `0 < y / x` here,
and for `0 < q i = rexp (…) / Z` in Part 4. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `ha : 0 < a, hb : 0 < b ⊢ 0 < a / b` | `h : 0 < a / b ⊢ 0 < a / b` |

**R14 · `rw [Real.log_div hx hy] at h`** changes the **context**: R6 applied inside hypothesis `h` instead
of the goal. Any `rw [e] at h` works this way. Placeholders: `(x y c : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)`.

| Before | After |
|---|---|
| `h : log (x / y) ≤ c ⊢ G` | `h : log x - log y ≤ c ⊢ G` |

**R15 · `mul_le_mul_of_nonneg_left hbc ha`** changes the **context**:
`b ≤ c → 0 ≤ a → a * b ≤ a * c` (multiply an inequality on the left by `a ≥ 0`). Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `hbc : b ≤ c, ha : 0 ≤ a ⊢ a * b ≤ a * c` | `h : a * b ≤ a * c ⊢ a * b ≤ a * c` |

**R16 · `hab.le`** (`LT.lt.le`) changes the **context**: `a < b` becomes `a ≤ b`. R15 and R30 want `0 ≤ x`,
you have `hx' : 0 < x`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `hab : a < b ⊢ a ≤ b` | `h : a ≤ b ⊢ a ≤ b` |

**R17 · `field_simp`** changes the **goal** (or closes it): it multiplies out every denominator it can prove
nonzero, using hypotheses such as `hz : 0 < z` or `hz : z ≠ 0` from the context, and normalises both sides.
If a goal remains, it is an equation without division; finish with `ring` (or `exact`). Placeholders:
`(a b z : ℝ) (hz : 0 < z)`.

| Before | After |
|---|---|
| `hz : 0 < z ⊢ a / z + b = (a + b * z) / z` | no goals |
| `⊢ a / z = b` | `⊢ a = z * b` |

---

## Part 4 · `gibbs_inequality` (milestone)

Statement: `∑ i, p i * (log (q i) - log (p i)) ≤ 0`. First `hq : ∀ i, 0 < q i` (R13 with R7, R3). Then a
`calc`: the sum is `≤ ∑ i, (q i - p i)` termwise by Part 3, and that sum is `∑ q - ∑ p = 1 - 1 = 0`.

**R18 · `calc`** changes the **goal list**: a chain `a ≤ b = c` proves `a ≤ c`, one step per line. `_` on the
first line is the goal's left side, on later lines the previous right side. Each step's proof follows
`:=`; with `?_` it becomes a goal of its own. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ a ≤ b`, `⊢ b = c` |

**R19 · `apply Finset.sum_le_sum`** changes the **goal**: `(∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`.
In term mode: `Finset.sum_le_sum fun i _ => …` (the `_` is the unused `i ∈ Finset.univ`).
Placeholders: `(f g : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ i, f i ≤ ∑ i, g i` | `⊢ ∀ i ∈ Finset.univ, f i ≤ g i` |

**R20 · `rw [Finset.sum_sub_distrib]`** changes the **goal**:
`∑ i ∈ s, (f i - g i) = ∑ i ∈ s, f i - ∑ i ∈ s, g i`. Placeholders: `(f g : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, (f i - g i))` | `⊢ P (∑ x, f x - ∑ x, g x)` |

**R21 · `rw [sub_self]`** changes the **goal**: `a - a = 0`. After `rw [Finset.sum_sub_distrib, sum_boltzmann, hsum]`
the goal is `1 - 1 = 0`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a - a)` | `⊢ P 0` |

**W1** (guide) runs the same pattern on `∑ i, w i * log (a i) ≤ ∑ i, w i * a i - 1`: R12 and R15 give each
term's bound, `linarith` (R11) adjusts it, R19 sums it inside R18, and R20 plus `hsum` finish:

```lean-goal
⊢ ∑ i, w i * log (a i) ≤ ∑ i, w i * a i - 1
```

---

## Part 5 · `gibbs_variational`

Statement: `-log Z / b ≤ ∑ i, p i * E i - (∑ i, negMulLog (p i)) / b`. Take Part 4 as `key`, rewrite its
`log (q i)` with Part 2, expand the sum into `-b ⟨E⟩ - log Z + S`, then divide by `b`.

**R22 · `simp only [e] at h`** with `e : ∀ …, l = r` changes the **context**: it rewrites `l` to `r` inside
`h`, also under the binder `∑ i, …` (where `rw` fails, because `l` mentions the bound `i`). Here `e` is
Part 2 (`log_boltzmann`) and `h` is `key`. Without `at h` it rewrites the goal (Part 6).
Placeholders: `(f g : ι → ℝ) (e : ∀ i, f i = g i)`.

| | Before | After |
|---|---|---|
| hypothesis | `h : ∑ i, f i ≤ 0` | `h : ∑ x, g x ≤ 0` |
| goal | `⊢ G` | `⊢ G` |

**R23 · `set L := e`** changes the **context and the goal**: it adds the local definition `L := e` and
replaces every `e` in the goal and context by `L`. Here `L := log Z` keeps the expansion readable.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (log x)` | `L : ℝ := log x ⊢ P L` |

**R24 · `apply Finset.sum_congr rfl`** changes the **goal**: two sums over the same set are equal when the
terms are. `Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`, and `rfl` fills
`s₁ = s₂`. In term mode: `Finset.sum_congr rfl fun i _ => by …`. Placeholders: `(f g : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ i, f i = ∑ i, g i` | `⊢ ∀ x ∈ Finset.univ, f x = g x` |

**R25 · `simp only [Real.negMulLog]`** changes the **goal**: `Real.negMulLog x` (printed `x.negMulLog`)
becomes its definition `-x * log x`. Then `ring` can see it. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P x.negMulLog` | `⊢ P (-x * log x)` |

**R26 · `rw [Finset.sum_add_distrib]`** changes the **goal**:
`∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i`. Placeholders: `(f g : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, (f i + g i))` | `⊢ P (∑ x, f x + ∑ x, g x)` |

**R27 · `Finset.mul_sum`** changes the **goal**: `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`. `rw [← Finset.mul_sum]`
pulls a constant factor out of a sum (Part 5); `rw [Finset.mul_sum]` pushes it in (Part 6). The constant must
be the **left** factor of each term (`-b * (p i * E i)`, `L * p i`), which is why the termwise rewrite puts
it there. Placeholders: `(f : ι → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, a * f i)` | `⊢ P (a * ∑ i, f i)` |
| `⊢ P (a * ∑ i, f i)` | `⊢ P (∑ i, a * f i)` |

**R28 · `rw [mul_one]`** changes the **goal**: `a * 1 = a`, for the `L * 1` left after `rw [hsum]`.
Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

**R29 · `rw [show A = B by tac]`** changes the **goal**: it proves the equation `A = B` on the spot with `tac`
and rewrites with it. Here `A` is the right side `∑ p E - S / b` and `B` is `(b * ∑ p E - S) / b`, proved by
`field_simp` (R17, using `hb : 0 < b`). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a + b)` | `⊢ P (b + a)` |

**R30 · `apply div_le_div_of_nonneg_right`** changes the **goal list**: `a ≤ b → 0 ≤ c → a / c ≤ b / c`.
In the exercise: `div_le_div_of_nonneg_right (by linarith) hb.le`, where `linarith` (R11) gets
`-log Z ≤ b * ∑ p E - S` from `key` and `hb.le` is R16. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a / c ≤ b / c` | `⊢ a ≤ b`, `⊢ 0 ≤ c` |

**W2** (guide) expands `∑ i, w i * (c * a i + d)` using `∑ w = 1`: R24 with `ring` puts each term in the form
`c * (w i * a i) + d * w i`, then R26, R27 `←` twice, `hsum`, R28:

```lean-goal
⊢ ∑ i, w i * (c * a i + d) = c * ∑ i, w i * a i + d
```

**W3** (guide) divides `u ≤ c * a - s` by `c > 0`: R29 (proved by R17), then R30 with R16:

```lean-goal
⊢ u / c ≤ a - s / c
⊢ u / c ≤ (c * a - s) / c
```

---

## Part 6 · `gibbs_attained`

Statement: the same with `p = q`, as an equation. Unfold `negMulLog` and rewrite `log (q i)` with Part 2 in
one `simp only` (R25, R22 on the goal). The entropy sum becomes `∑ i, -q i * (-b * E i - log Z)`; prove it
equals `b * ∑ i, q i * E i + log Z * ∑ i, q i` (R27 forward twice, R26 `←`, R24 with `ring`), rewrite with
that and with Part 1 (`∑ q = 1`), then R17 and `ring`.

---

## Traps

- Mathlib's `log` is total: `log 0 = 0` and `log (-x) = log x`. So `0 * log 0 = 0`, and zero-probability states
  drop out on their own, but `log_le_sub_one_of_pos` and `log_div` need positivity / nonzeroness, which is
  why Part 3 splits off `x = 0` (R9) first.
- `rw` cannot rewrite under `∑ i, …` when the pattern mentions `i`; use `simp only [e]` (R22), or
  `Finset.sum_congr rfl` (R24) to work on one term.
- `rw [← Finset.mul_sum]` needs the constant as the left factor of every term, literally. Put each term in
  that form first (`-b * (p i * E i) - L * p i + negMulLog (p i)`), with R24 and `ring`.
- `mathematicalPartitionFunctionBetaReal_pos` needs `[Nonempty ι]`; the milestones' `variable` line has it.
- `hz.ne'` (`z ≠ 0`) versus `hz.ne` (`0 ≠ z`): `div_self` and `log_div` want `z ≠ 0`.
- `field_simp` reads positivity from hypotheses in the context: have `hx' : 0 < x` or `hb : 0 < b` there.
- `linarith` does not unfold definitions or use `∀` facts by itself; put the instances it needs in the context
  (`have h2 := …`) or in brackets (`linarith [hfg i]`).
- `t1 ; t2` runs `t2` on the first goal only (TACTIC_STATES, "Structure"). After R9 or R30, use `·` bullets.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| see `q i` as `exp / Z` | `simp only [probabilityBetaReal]` (under `∑`), `rw [probabilityBetaReal]` | R1 |
| `∑ f / a` → `(∑ f) / a` | `rw [← Finset.sum_div]` | R2 |
| `0 < Z b`, `Z b ≠ 0` | `𝓒.mathematicalPartitionFunctionBetaReal_pos b`, `.ne'` | R3, R4 |
| `a / a = 1` | `div_self ha` | R5 |
| `log (x / y)`, `log (exp x)` | `Real.log_div hx hy`, `Real.log_exp` | R6, R8 |
| `0 < exp x`, `0 < a / b` | `Real.exp_pos _`, `div_pos ha hb` | R7, R13 |
| split `0 ≤ x` into `x = 0` / `0 < x` | `rcases hx.eq_or_lt with rfl \| hx'` | R9 |
| linear consequence of hypotheses | `linarith`, `linarith [h i]` | R11 |
| `log x ≤ x - 1` | `Real.log_le_sub_one_of_pos hx` | R12 |
| rewrite a hypothesis | `rw [e] at h`, `simp only [e] at h` | R14, R22 |
| multiply `b ≤ c` by `a ≥ 0` | `mul_le_mul_of_nonneg_left hbc ha` | R15 |
| `<` → `≤` | `h.le` | R16 |
| clear denominators | `field_simp` (then `ring`) | R17 |
| chain of `≤` / `=` | `calc _ ≤ b := … \n _ = c := …` | R18 |
| termwise `≤` of sums | `Finset.sum_le_sum fun i _ => …` | R19 |
| split / factor sums | `Finset.sum_sub_distrib`, `Finset.sum_add_distrib`, `Finset.mul_sum` | R20, R26, R27 |
| `a - a`, `a * 1` | `sub_self`, `mul_one` | R21, R28 |
| abbreviate a term | `set L := e` | R23 |
| termwise `=` of sums | `Finset.sum_congr rfl fun i _ => by …` | R24 |
| unfold `negMulLog` | `simp only [Real.negMulLog]` | R25 |
| rewrite by a fact proved inline | `rw [show A = B by tac]` | R29 |
| divide `a ≤ b` by `c ≥ 0` | `div_le_div_of_nonneg_right hab hc` | R30 |
| see the state | infoview | |
