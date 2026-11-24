# H072 · Global error of Euler's method: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033: `intro`, `exact`, `have`, `obtain`, `rw`, `simp`,
`induction … with`, `ring`, `norm_num`). The milestone `discrete_gronwall` is M119's theorem: if you did
M119, paste your proof (Part 3 below covers it anyway). **New here:** Mathlib's real numbers `ℝ` with
absolute value `|·|` and `Real.exp`; derivatives (`HasDerivAt`) and continuity; the mean value theorem
`exists_hasDerivAt_eq_slope`; intervals `Set.Icc`, `Set.Ioo`; the casts `↑k : ℝ` of natural numbers;
the inequality tactics `linarith`, `nlinarith`, `gcongr`, `positivity`.

**The mathematics.** Write `tₖ = t₀ + k h`, `Yₖ = eulerSeq F t₀ (y t₀) h k` (the Euler iterate) and
`eₖ = |y tₖ − Yₖ|` (the global error after `k` steps). Three facts give the theorem:

1. *Local error* (`local_error`): one exact step against one Euler step from the exact value,
   `|y(t+h) − y(t) − h y'(t)| ≤ M h²`. By the mean value theorem `y(t+h) − y(t) = h y'(c)` for some
   `c ∈ (t, t+h)`, so the left side is `h |y'(c) − y'(t)| ≤ h · M |c − t| ≤ M h²`.
2. *Error recursion* (`error_step`): `eₖ₊₁ ≤ (1 + hL) eₖ + M h²`. Split
   `y(tₖ+h) − Yₖ₊₁ = [y(tₖ+h) − y(tₖ) − h y'(tₖ)] + [(y(tₖ) − Yₖ) + h (F(tₖ, y tₖ) − F(tₖ, Yₖ))]`
   (using `y'(tₖ) = F(tₖ, y tₖ)`); bound the first bracket by 1 and the second by `eₖ + hL eₖ`.
3. *Discrete Gronwall* (`discrete_gronwall`, `a = hL`, `b = M h²`): `eₙ ≤ e^{na} (e₀ + n b)`, and `e₀ = 0`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`, `have` or `exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. `G : Prop` is any goal; `hG` only finishes the example.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Field α]` is a
  requirement on `α` (a *type class*); `ℝ` meets every bracket used here.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ`, `ℕ` | the real numbers; the natural numbers `0, 1, 2, …` |
| `↑k` (with `k : ℕ`) | `k` cast into `ℝ` (`Nat.cast`). `↑(k + 1)` and `↑k + 1` are equal but different text |
| `\|x\|` | absolute value of `x : ℝ` (`abs x`) |
| `Real.exp x` | `eˣ` |
| `HasDerivAt f v x` | `f : ℝ → ℝ` is differentiable at `x` with derivative `f'(x) = v` |
| `ContinuousAt f x`, `Continuous f` | `f` is continuous at `x`; at every point |
| `ContinuousOn f S` | `f` restricted to the set `S` is continuous |
| `Set ℝ` | the type of sets of reals |
| `Set.Icc a b`, `Set.Ioo a b` | the closed interval `[a, b]`; the open interval `(a, b)` |
| `c ∈ Set.Ioo a b` | `a < c ∧ c < b` (by definition, `Set.mem_Ioo`) |
| `∀ x ∈ S, Q x` | `∀ x, x ∈ S → Q x` |
| `∃ c ∈ S, Q c` | `∃ c, c ∈ S ∧ Q c` |
| `eulerSeq F t₀ (y t₀) h k` | the Euler iterate `Yₖ` |
| `t : ℝ := t₀ + ↑k * h` | a local definition made by `set` (R19); nested goals print it as `t : ℝ := ⋯` |
| `this` | the hypothesis made by `have := …` with no name (R31) |
| `case hbc`, `case h₁`, `case hab` | names `gcongr` gives the goals it leaves |
| `a✝`, `n✝` | an inaccessible name: you wrote `_` (R5), or a newer variable with the same name shadows it (`intro n` inside `discrete_gronwall`) |

---

## Part 1 · `local_error` (MILESTONE)

Statement: `|y (t + h) - y t - h * y' t| ≤ M * h ^ 2` for `h > 0`, `y` differentiable everywhere with
derivative `y'`, and `y'` `M`-Lipschitz (`|y' s - y' t| ≤ M * |s - t|`).

### Continuity and the mean value theorem

**R1 · `rw [continuous_iff_continuousAt]`** changes the **goal**. The lemma is
`Continuous f ↔ ∀ x, ContinuousAt f x`. Placeholders: `(f : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Continuous f` | `⊢ ∀ (x : ℝ), ContinuousAt f x` |

**R2 · `hf.continuousAt`** (`HasDerivAt.continuousAt`) **closes** `ContinuousAt f x`: differentiable at
`x` implies continuous at `x`. Placeholders: `(f : ℝ → ℝ) (f' x : ℝ) (hf : HasDerivAt f f' x)`. With R1 as
a term: `have hcont : Continuous y := continuous_iff_continuousAt.mpr fun s => (hy s).continuousAt`
(`.mpr` is the `←` direction of an `↔`).

| Before | After |
|---|---|
| `⊢ ContinuousAt f x` | closed |

**R3 · `hf.continuousOn`** (`Continuous.continuousOn`) **closes** `ContinuousOn f S` from
`hf : Continuous f`, for any set `S`. Placeholders: `(f : ℝ → ℝ) (s : Set ℝ)`.

| Before | After |
|---|---|
| `⊢ ContinuousOn f s` | closed |

**R4 · `linarith`** **closes** a goal `≤ < = ≥ >` that is a linear consequence of the hypotheses (sums
and numeral multiples; no products of variables). `linarith [t₁, t₂]` also uses the facts `tᵢ`. Used
inline as `(show t < t + h by linarith)` to feed `exists_hasDerivAt_eq_slope` its `a < b`.

| Before | After |
|---|---|
| `hs : 0 < s ⊢ a < a + s` | closed |

**R5 · `fun x _ => h x`** proves `∀ x ∈ S, Q x` from `h : ∀ x, Q x`: the `_` is the unused proof of
`x ∈ S`. The tactic form is `intro x _` then `exact h x`. Placeholders: `(S : Set ℝ) (Q : ℝ → Prop)`.
In the exercise: `(fun s _ => hy s)` is the derivative premise of the mean value theorem.

| Before | After `intro x _` |
|---|---|
| `⊢ ∀ x ∈ S, Q x` | `x : ℝ, a✝ : x ∈ S ⊢ Q x` |

**R6 · `obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hab hfc hff'`** changes the
**context**. The lemma (mean value theorem):

```
exists_hasDerivAt_eq_slope (f f' : ℝ → ℝ) {a b : ℝ} (hab : a < b)
  (hf : ContinuousOn f (Set.Icc a b)) (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
  ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a)
```

Placeholders: `(f f' : ℝ → ℝ) (a b : ℝ)`. `hfc` comes from R1–R3, `hff'` from R5, `hab` from R4.

| Before | After |
|---|---|
| `⊢ G` | `c : ℝ, hc : c ∈ Set.Ioo a b, hslope : f' c = (f b - f a) / (b - a) ⊢ G` |

In the exercise (`a = t`, `b = t + h`) this gives
`hslope : y' c = (y (t + h) - y t) / (t + h - t)`.

### Algebra on the slope

The goal is first the identity `y (t + h) - y t - h * y' t = h * (y' c - y' t)`. `rw [hslope]` replaces
`y' c` on the right by the slope; R7–R10 then make the two sides the same text, and `rw` closes the goal
with `rfl`.

**R7 · `rw [show u = v by ring]`** changes the **goal**: it rewrites with an equation proved on the spot.
Placeholders: `(a s : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a + s - a)` | `⊢ P s` |

**R8 · `rw [mul_sub]`** changes the **goal**. The lemma is `mul_sub : a * (b - c) = a * b - a * c`.
Placeholders: `{α : Type} [CommRing α] (a b c : α)`.

| Before | After |
|---|---|
| `⊢ P (a * (b - c))` | `⊢ P (a * b - a * c)` |

**R9 · `hab.ne'`** (`LT.lt.ne'`) changes the **context**: from `hab : a < b` it gives `b ≠ a`. So
`hh : 0 < h` gives `hh.ne' : h ≠ 0`, the form division lemmas want. Placeholders:
`{α : Type} [Preorder α] (a b : α)`.

| Before | After |
|---|---|
| `hab : a < b ⊢ G` | `hne : b ≠ a ⊢ G` |

**R10 · `rw [mul_div_cancel₀ _ hb]`** changes the **goal**. The lemma is
`mul_div_cancel₀ (a : α) (h : b ≠ 0) : b * (a / b) = a`. Placeholders: `{α : Type} [Field α] (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (b * (a / b))` | `⊢ P a` |

### Absolute values and inequalities

**R11 · `(abs_nonneg x).trans h`** changes the **context**. `abs_nonneg x : 0 ≤ |x|`, and `.trans`
(`le_trans`) chains `0 ≤ |x|` with `h : |x| ≤ c`. Placeholders: `(x c : ℝ)`. In the exercise this is how
you get `0 ≤ M` (it is not a hypothesis): `hlip` at two distinct points gives `|…| ≤ M * |s - t|` with
`|s - t| = 1`.

| Before | After |
|---|---|
| `⊢ G`, with `h : \|x\| ≤ c` | `hc : 0 ≤ c ⊢ G` |

**R12 · `simp at h`, `simpa using h`** changes the **context**: `simp` simplifies `h` (`x + 1 - x` → `1`,
`K * 1` → `K`; it also knows `|1| = 1`). `simpa using h` does this to `h` and the goal, then closes the
goal with `h`. Placeholders: `(K x : ℝ)`.

| Before | After `simp at h` |
|---|---|
| `h : 0 < K * (x + 1 - x) ⊢ 0 < K` | `h : 0 < K ⊢ 0 < K` |

**R13 · `hc.1`, `hc.2`** change the **context**: `c ∈ Set.Ioo a b` is by definition `a < c ∧ c < b`, so
its two halves are `.1` and `.2`. Pass them to `linarith` directly: `linarith [hc.1]`. Placeholders:
`(a b c : ℝ)`.

| Before | After `have h1 : a < c := hc.1`, `have h2 : c < b := hc.2` |
|---|---|
| `hc : c ∈ Set.Ioo a b ⊢ G` | `h1 : a < c, h2 : c < b ⊢ G` |

**R14 · `rw [abs_of_pos ha]`** changes the **goal**. The lemma is `abs_of_pos : 0 < a → |a| = a`.
Placeholders: `(a : ℝ) (ha : 0 < a)`. For `|c - t| ≤ h`: `rw [abs_of_pos (by linarith [hc.1])]`, then
`linarith [hc.2]`. Before, then after:

```lean-goal
⊢ P |a|
⊢ P a
```

**R15 · `rw [abs_mul]`** changes the **goal**. The lemma is `abs_mul : |a * b| = |a| * |b|`.
Placeholders: `(a b : ℝ)`. Before, then after:

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R16 · `calc`** changes the **goal list**: it proves `a ≤ d` from a chain of steps, each with its own
proof (`:= term` or `:= by tac`). Steps may mix `≤`, `<`, `=`. Later steps start with `_` (the previous
right side); the first step may also be `_ ≤ …` to mean the goal's left side. Placeholders: `(a b c d : ℝ)`.

```lean
calc a ≤ b := h1
  _ ≤ c := h2
  _ = d := h3
```

| Before | After |
|---|---|
| `h1 : a ≤ b, h2 : b ≤ c, h3 : c = d ⊢ a ≤ d` | closed |

**R17 · `gcongr`** changes the **goal**: for `c * x ≤ c * y` it leaves `x ≤ y` (*generalized
congruence*: it strips the common shape of both sides). The side goal `0 ≤ c` is closed by `positivity`
(R32) from a hypothesis `hc : 0 ≤ c` in the context; if there is none, `0 ≤ c` is left as the **first**
goal. Main goals that match a hypothesis are closed by it. Placeholders: `(c y z : ℝ) (f : ℝ → ℝ)`.

| Before | After |
|---|---|
| `hc : 0 ≤ c ⊢ c * f z ≤ c * y` | `⊢ f z ≤ y` |

### Worked combination W1 (not the exercise's object)

**W1.** `|f (a + s) - f a| ≤ K * s` from `|f' x| ≤ K`: R1–R3 for continuity, R6 with R4 and R5,
the identity `f (a + s) - f a = s * f' c` by `rw [hslope, show a + s - a = s by ring, mul_div_cancel₀ _ hs.ne']`
(R7, R9, R10), then R15, R14 and a `calc` (R16) whose step uses `gcongr` (R17). After `rw [e, abs_mul, abs_of_pos hs]`:

```lean-goal
⊢ s * |f' c| ≤ K * s
```

---

## Part 2 · `error_step` (MILESTONE)

Statement: `eₖ₊₁ ≤ (1 + h L) eₖ + M h²`, written out with `eulerSeq`. Uses `local_error` and `hode t`
(`y' t = F t (y t)`) and `hF` (`F` is `L`-Lipschitz in its second argument).

**R18 · `simp only [walk]`** changes the **goal**: it rewrites `walk a d g (k + 1)` by its second
defining equation. The argument `k` is a variable, so `walk a d g k` is left alone: exactly one step is
unfolded. In the exercise, `simp only [eulerSeq]` turns `eulerSeq F t₀ (y t₀) h (k + 1)` into
`eulerSeq F t₀ (y t₀) h k + h * F (t₀ + ↑k * h) (eulerSeq F t₀ (y t₀) h k)`. Placeholders:
`(a d : ℝ) (g : ℝ → ℝ) (k : ℕ)` with `walk` defined in the guide.

| Before | After |
|---|---|
| `⊢ P (walk a d g (k + 1))` | `⊢ P (g (walk a d g k) + d)` |

**R19 · `set u := e`** changes the **context and the goal**: it adds the local definition `u : ℝ := e` and
replaces every `e` in the goal by `u`. Name `t := t₀ + ↑k * h` and `Y := eulerSeq F t₀ (y t₀) h k`; the
goal becomes short enough to read. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a * b + 1) (a * b + 1)` | `u : ℝ := a * b + 1 ⊢ P u u` |

**R20 · `push_cast`** changes the **goal**: it moves casts `↑` inward, `↑(k + 1)` → `↑k + 1`. The goal
has `t₀ + ↑(k + 1) * h`; prove `ht : t₀ + ((k + 1 : ℕ) : ℝ) * h = t + h` by `push_cast; ring`, then
`rw [ht]`. Placeholders: `(k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑(k + 1)` | `⊢ P (↑k + 1)` |

**R21 · `abs_add_le a b`** changes the **context** (or, as a `calc` step's proof, closes it). The lemma is
the triangle inequality `abs_add_le (a b : ℝ) : |a + b| ≤ |a| + |b|`. In a `calc`, write
`_ ≤ |A| + |B| := abs_add_le _ _`. Placeholders: `(a b : ℝ)`.

| Before | After `have h := abs_add_le a b` |
|---|---|
| `⊢ G` | `⊢ G`, plus `h : \|a + b\| ≤ \|a\| + \|b\|` in the context |

**R22 · `gcongr` on a sum** changes the **goal list**: `p + q ≤ p' + q'` becomes `p ≤ p'` and `q ≤ q'`
(a summand equal on both sides gives no goal). Prove each with `·`. Placeholders:
`(f g : ℝ → ℝ) (x c d : ℝ)`.

| Before | After |
|---|---|
| `⊢ f x + g x ≤ c + d` | `⊢ f x ≤ c`, `⊢ g x ≤ d` |

In the exercise, after the split identity and `abs_add_le`, `gcongr` on
`|A| + |B| ≤ M * h ^ 2 + (|y t - Y| + h * (L * |y t - Y|))` leaves `|A| ≤ M * h ^ 2` (that is
`local_error`) and `|B| ≤ |y t - Y| + h * (L * |y t - Y|)` (R21 again, R15, R14, then R17 and `hF`).

### Worked combination W2 (not the exercise's object)

**W2.** For `walk` (`uₖ₊₁ = g uₖ + d`) with `g` `L`-Lipschitz: R18, then R19 twice, then the split
identity by `ring` and `rw [key]`:

```lean-goal
⊢ |g (walk a d g k) + d - (g (walk b 0 g k) + 0)| ≤ L * |walk a d g k - walk b 0 g k| + |d|
⊢ |g u + d - (g w + 0)| ≤ L * |u - w| + |d|
⊢ |g u - g w + d| ≤ L * |u - w| + |d|
```

then `calc _ ≤ |g u - g w| + |d| := abs_add_le _ _` and `_ ≤ L * |u - w| + |d| := by gcongr; exact hg u w`.

---

## Part 3 · `discrete_gronwall` (MILESTONE, from M119)

Statement: `eₙ₊₁ ≤ (1 + a) eₙ + b` with `a, b, e₀ ≥ 0` implies `eₙ ≤ e^{na} (e₀ + n b)`. Route: prove the
sharper `eₙ ≤ (1 + a)ⁿ (e₀ + n b)` by induction, then `1 + a ≤ eᵃ`.

**R23 · `one_le_pow₀ ha`** changes the **context**. The lemma is `one_le_pow₀ : 1 ≤ a → 1 ≤ a ^ n`.
Placeholders: `(a : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `ha : 1 ≤ a ⊢ G` | `h1 : 1 ≤ a ^ n ⊢ G` |

**R24 · `rw [pow_succ]`** changes the **goal**. The lemma is `pow_succ (a : α) (n : ℕ) : a ^ (n + 1) = a ^ n * a`.
Placeholders: `{α : Type} [Monoid α] (a : α) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

**R25 · `mul_le_mul_of_nonneg_left hbc ha`** changes the **context**. The lemma is
`b ≤ c → 0 ≤ a → a * b ≤ a * c`. Its use here is as an extra fact for `nlinarith` (R26). Placeholders:
`(a b c : ℝ)`.

| Before | After |
|---|---|
| `hbc : b ≤ c, ha : 0 ≤ a ⊢ G` | `h : a * b ≤ a * c ⊢ G` |

**R26 · `nlinarith [t₁, …]`** **closes** an inequality that needs products of hypotheses: it multiplies
pairs of hypotheses and extra facts, then runs `linarith` (R4). In the induction step the product
`(1 + a) * (1 + a) ^ n * …` is non-linear; give it R25's product as `t₁`.

| Before | After |
|---|---|
| `hx : 0 ≤ x, hy : 1 ≤ y ⊢ x ≤ x * y` | closed |

**R27 · `gcongr` with a right factor** changes the **goal**: `x * c ≤ y * c` → `x ≤ y`, side goal `0 ≤ c`
closed from the context. On `(1 + a) ^ n * (e 0 + n * b) ≤ Real.exp (n * a) * (e 0 + n * b)` it leaves
`(1 + a) ^ n ≤ Real.exp (↑n * a)`; the side goal `0 ≤ e 0 + ↑n * b` is closed from `he0`, `hb`.
Placeholders: `(c y z : ℝ) (f : ℝ → ℝ)`.

| Before | After |
|---|---|
| `hc : 0 ≤ c ⊢ f z * c ≤ y * c` | `⊢ f z ≤ y` |

**R28 · `Real.add_one_le_exp x`** changes the **context**: `x + 1 ≤ Real.exp x` for every real `x`. Feed it
to `linarith`: `linarith [Real.add_one_le_exp a]` proves `1 + a ≤ Real.exp a`.

| Before | After |
|---|---|
| `⊢ G` | `h : x + 1 ≤ Real.exp x ⊢ G` |

**R29 · `gcongr` on powers** changes the **goal**: `x ^ n ≤ y ^ n` → `x ≤ y`, side goal `0 ≤ x` closed from
the context. It needs both sides to be `_ ^ n`, so first rewrite `Real.exp (↑n * a)` as `Real.exp a ^ n`
(R30) in a `calc` step. Placeholders: `(y z : ℝ) (n : ℕ) (f : ℝ → ℝ)`, with `x = f z`. In the exercise
(`(1 + a) ^ n ≤ Real.exp a ^ n`) it leaves `1 + a ≤ Real.exp a` (case `hab`).

| Before | After |
|---|---|
| `hx : 0 ≤ f z ⊢ f z ^ n ≤ y ^ n` | `⊢ f z ≤ y` |

**R30 · `rw [← Real.exp_nat_mul]`** changes the **goal**. The lemma is
`Real.exp_nat_mul (x : ℝ) (n : ℕ) : Real.exp (↑n * x) = Real.exp x ^ n`; `←` uses it right to left.
Placeholders: `(x : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Real.exp x ^ n)` | `⊢ P (Real.exp (↑n * x))` |

**W3** (not the exercise's object): `x ^ n ≤ Real.exp (n * (x - 1))` for `x ≥ 0` by
`calc x ^ n ≤ Real.exp (x - 1) ^ n := by gcongr; linarith [Real.add_one_le_exp (x - 1)]` (R29, R28) and
`_ = Real.exp (n * (x - 1)) := by rw [← Real.exp_nat_mul]` (R30).

---

## Part 4 · `euler_global_error`

Statement: `|y (t₀ + ↑n * h) - eulerSeq F t₀ (y t₀) h n| ≤ Real.exp (↑n * (h * L)) * (↑n * (M * h ^ 2))`.
Apply `discrete_gronwall` to the error sequence `e = fun k : ℕ => |y (t₀ + ↑k * h) - eulerSeq F t₀ (y t₀) h k|`
with `a = h * L`, `b = M * h ^ 2`; `error_step …` is exactly its `hstep` (Lean unfolds `e (n + 1)` by itself).

**R31 · `have := lem (fun k => …) …`** changes the **context**: it adds `this`, the lemma's conclusion with
the function applied and already simplified (`(fun k => body) 3` shown as `body` at `3`). Placeholders:
`(f : ℕ → ℝ)` and a general lemma `lem` over all `e : ℕ → ℝ`.

| Before | After `have := lem (fun k => f k + f k) …` |
|---|---|
| `⊢ G` | `this : f 3 + f 3 ≤ f 3 + f 3 + (f 0 + f 0) ⊢ G` |

**R32 · `positivity`** **closes** `0 ≤ e` or `0 < e` when `e` is built from `+`, `*`, `^`, `|·|`, `Real.exp`,
numerals and atoms `x` with a hypothesis `0 ≤ x` or `0 < x` in the context. It proves the premises
`0 ≤ h * L` and `0 ≤ M * h ^ 2` (the second needs `0 ≤ M`, R11–R12, in the context first).

| Before | After |
|---|---|
| `hs : 0 < s, hL : 0 ≤ L, hK : 0 ≤ K ⊢ 0 ≤ s * L + K * s ^ 2` | closed |

**R33 · `simpa [walk] using this`** **closes** the goal after cleaning up `this`: `↑0` → `0`, `0 * s` → `0`,
`a + 0` → `a`, `walk … 0` → its start value (from `[walk]`), `v - v` → `0`, `0 + x` → `x` (and `|0|` → `0`). In the
exercise `this` has `e 0 = |y (t₀ + ↑0 * h) - eulerSeq F t₀ (y t₀) h 0|`; `simpa [eulerSeq] using this`
reduces it to `0`.

| Before | After |
|---|---|
| `this : g a ≤ c * (g (a + ↑0 * s) - walk (g a) 0 g 0 + s) ⊢ g a ≤ c * s` | closed |

---

## Traps

- `0 ≤ M` is not a hypothesis, and `gcongr` needs it for `h * (M * x) ≤ h * (M * h)` and `positivity`
  needs it for `0 ≤ M * h ^ 2`. Get it from `hlip` at two points at distance `1` (R11, R12), in
  `local_error` and again in the main theorem (a `have` belongs to one proof only).
- If `gcongr` cannot close a side goal such as `0 ≤ c`, it leaves it as the **first** goal, before the main
  one; `gcongr; exact …` then fails on the wrong goal. Put the fact in the context first.
- `t₀ + ↑(k + 1) * h` is not literally `t + h`: `rw` does not see through casts. Prove the equation with
  `push_cast; ring` (R20) and `rw` with it.
- `rw [hslope]` rewrites `y' c` (the left side of `hslope`), which sits on the right of the identity
  `… = h * (y' c - y' t)`. State the identity that way round.
- `simp only [eulerSeq]` unfolds only the `k + 1` term; `eulerSeq … k` stays (R18). Unfold before `set`:
  `set` renames only what is already in the goal, so unfolding afterwards brings back un-named copies of
  `t₀ + ↑k * h` and `eulerSeq F t₀ (y t₀) h k`.
- The mean value theorem's premise `∀ x ∈ Set.Ioo a b, HasDerivAt …` takes two arguments (the point and
  its membership proof): pass `fun s _ => hy s`, not `hy` (R5).
- The Lipschitz hypotheses are global (a simplification of `|y''| ≤ M` and a local Lipschitz bound). They are
  not vacuous: `F t u = -u + sin t`, `y t = (sin t - cos t) / 2` satisfy them with `L = M = 1`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `Continuous y` from `∀ t, HasDerivAt y (y' t) t` | `continuous_iff_continuousAt.mpr fun t => (hy t).continuousAt` | R1, R2 |
| `ContinuousOn y S` | `hcont.continuousOn` | R3 |
| `a < b` inline | `(show t < t + h by linarith)` | R4 |
| `∀ x ∈ S, Q x` from `∀ x, Q x` | `fun x _ => h x` | R5 |
| mean value theorem | `obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope y y' hab hcont.continuousOn (fun s _ => hy s)` | R6 |
| rewrite with a quick fact | `rw [show t + h - t = h by ring]` | R7 |
| `a * (b - c) → a * b - a * c` | `rw [mul_sub]` | R8 |
| `h ≠ 0` from `0 < h` | `hh.ne'` | R9 |
| `b * (a / b) → a` | `rw [mul_div_cancel₀ _ hb]` | R10 |
| `0 ≤ M` from a Lipschitz bound | `(abs_nonneg _).trans (hlip s t)`, then `simpa using` | R11, R12 |
| halves of `c ∈ Set.Ioo a b` | `hc.1`, `hc.2` | R13 |
| `\|a\| → a`, `\|a * b\| → \|a\| * \|b\|` | `rw [abs_of_pos ha]`, `rw [abs_mul]` | R14, R15 |
| chain of inequalities | `calc _ ≤ _ := … ; _ ≤ _ := by …` | R16 |
| `c * x ≤ c * y`, `x * c ≤ y * c`, sums, powers | `gcongr` | R17, R22, R27, R29 |
| unfold one recursion step | `simp only [eulerSeq]` | R18 |
| name a subterm | `set t := t₀ + k * h` | R19 |
| `↑(k + 1) → ↑k + 1` | `push_cast` | R20 |
| triangle inequality | `abs_add_le _ _` | R21 |
| `1 ≤ a ^ n`, `a ^ (n+1) = a ^ n * a` | `one_le_pow₀`, `rw [pow_succ]` | R23, R24 |
| non-linear inequality | `nlinarith [mul_le_mul_of_nonneg_left h1 ha]` | R25, R26 |
| `1 + a ≤ eᵃ` | `linarith [Real.add_one_le_exp a]` | R28 |
| `eᵃ ^ n = e^{na}` | `rw [← Real.exp_nat_mul]` | R30 |
| apply Gronwall to the error sequence | `have := discrete_gronwall (fun k : ℕ => …) … (error_step …) n` | R31 |
| `0 ≤ h * L`, `0 ≤ M * h ^ 2` | `by positivity` | R32 |
| clean up `e 0 = 0` and close | `simpa [eulerSeq] using this` | R33 |
| see the state | infoview | |
