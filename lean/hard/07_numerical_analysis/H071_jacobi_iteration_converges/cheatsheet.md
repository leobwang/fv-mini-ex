# H071 · Jacobi iteration converges: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`intro`, `have`, `exact`, `rw [h]`, `simp only [d]`, `simp`, `ring`, `refine`,
`exacts`) are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `by`, `rw`, `simp`, `exact`, `have`, `intro`,
`∀`/`∧`, induction on paper.
**New here:** Mathlib's vectors `Fin n → ℝ` with the sup norm `‖·‖`, matrices and `*ᵥ`, finite sums
`∑ j ∈ s, f j` over a `Finset`, absolute value lemmas, iterates `f^[k]`, the tactics `linarith`,
`positivity`, `gcongr`, `calc`, `conv_lhs`, `simpa`, and limits of sequences as
`Filter.Tendsto … atTop (𝓝 a)`.

**The mathematics.** Write `S_i(x) = ∑_{j≠i} A i j · x j` and `J(x) i = (b i − S_i(x)) / A i i` (one Jacobi
sweep, `jacobiStep A b`). If `A xs = b`, row `i` reads `A i i · xs i + S_i(xs) = b i`, so `J(xs) = xs`. For two
vectors `x, y`,

`J(x) i − J(y) i = −S_i(x − y) / A i i`, and `|S_i(x − y)| ≤ ∑_{j≠i} |A i j| · ‖x − y‖ ≤ ρ |A i i| ‖x − y‖`,

so `‖J(x) − J(y)‖ ≤ ρ ‖x − y‖` (`‖v‖ = maxᵢ |v i|`). With `xₖ = J^k(x₀)` and `J(xs) = xs`:
`‖xₖ₊₁ − xs‖ = ‖J(xₖ) − J(xs)‖ ≤ ρ ‖xₖ − xs‖`, so `‖xₖ − xs‖ ≤ ρᵏ ‖x₀ − xs‖`, and for `0 ≤ ρ < 1` this
tends to 0.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change. A
  hypothesis that itself contains `, ` (such as `h : ∑ x, M i x * v x = c i`) is written next to the state,
  not inside it.
- `P` (or `Q`) is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. `Q : Prop` is an arbitrary goal that the example finishes with `hQ`;
  it only exists so the new hypothesis can be shown.
- Placeholders are written as Lean binders. `{ι : Type}` is any index type; `[Fintype ι]` says it is finite
  (the exercise uses `Fin n = {0, …, n−1}`); `[DecidableEq ι]` says equality on it can be decided, which
  `s.erase a` needs (`Fin n` has both).
- A state that contains an absolute value `|…|` is shown as a `lean-goal` block instead of a table (the bar
  would split a table cell): the first line is the state before, the second the state after.
- Every `⊢` cell and every `lean-goal` line is a state Lean reaches in the companion file;
  `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin n → ℝ` | a vector in ℝⁿ: a function from the index set `{0, …, n−1}` to `ℝ` |
| `Matrix (Fin n) (Fin n) ℝ` | a real n×n matrix; `A i j` is row `i`, column `j` |
| `A *ᵥ v` | `Matrix.mulVec`: matrix times vector, `(A *ᵥ v) i = ∑ j, A i j * v j` (R3) |
| `v ⬝ᵥ w` | `dotProduct`: `∑ j, v j * w j`; `mulVec` is defined through it |
| `‖v‖` | for `v : Fin n → ℝ`, the sup norm `maxᵢ \|v i\|` (Mathlib's norm on a product of normed spaces) |
| `‖r‖` | for `r : ℝ`, the absolute value `\|r\|` (R12) |
| `\|a\|` | `abs a`, the absolute value |
| `(f - g) i` | entry `i` of the vector `f - g`, which is `f i - g i` (R11) |
| `noncomputable def` | a definition Lean cannot run as a program (real division is not computable); proofs use it as usual |
| `s : Finset ι` | a finite set of elements of `ι` (Mathlib's `Finset`); sums `∑` range over one |
| `univ` | `Finset.univ`, the finite set of all elements of a finite type (`open Finset`) |
| `univ.erase i` | `Finset.erase univ i`: all indices except `i` |
| `∑ x ∈ s, f x` | `Finset.sum s f`; `∑ x, f x` is the sum over `univ` |
| `∑ x_1 ∈ s, …` | the same sum; Lean renames the bound variable when `x` is already taken |
| `-∑ j ∈ s, f j`, `c * ∑ …` | the `∑` body extends as far right as possible: `-∑ j ∈ s, f j` is `-(∑ j ∈ s, f j)` |
| `x✝ : j ∈ s` | an anonymous hypothesis (made by `fun j _ => …`, R22) |
| `f^[k] x` | `Nat.iterate`: `f` applied `k` times to `x`; `f^[0] x = x` (R29, R30) |
| `Tendsto u atTop (𝓝 L)` | `Filter.Tendsto`: `u k → L` as `k → ∞` |
| `atTop` | `Filter.atTop`, "all sufficiently large `k`" |
| `𝓝 L` | `nhds L`, the neighbourhoods of `L` (notation from `open Topology`) |
| `fun e => ‖u e - L‖` | the sequence of distances to `L` |
| `case hbc`, `case succ` | names Lean gives to goals; ignore them |

---

## Part 1 · `jacobi_fixed` (milestone)

Statement: if `A i i ≠ 0` for all `i` and `A *ᵥ xs = b`, then `jacobiStep A b xs = xs`.
Proof on paper: row `i` of `A xs = b` is `A i i · xs i + S_i(xs) = b i`; solve for `xs i`.

**R1 · `funext i`** changes the **goal and the context**: two functions (here vectors) are equal when they
agree at every `i`. Placeholders: `{ι : Type} (f g : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ f = g` | `i : ι ⊢ f i = g i` |

**R2 · `have hi := congrFun h i`** changes the **context**. `congrFun : f = g → ∀ a, f a = g a` evaluates an
equation of functions at a point. Placeholders: `(f g : ι → ℝ) (i : ι) (h : f = g)`.

| Before | After |
|---|---|
| `⊢ Q` | `hi : f i = g i ⊢ Q` |

**R3 · `simp only [mulVec, dotProduct] at h`** changes the **context**: it unfolds the definitions of `*ᵥ`
and `⬝ᵥ`, so entry `i` of `M *ᵥ v` becomes an explicit sum. With `open Matrix`, `mulVec` is
`Matrix.mulVec`. Placeholders: `{n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v c : Fin n → ℝ) (i : Fin n)`.

| Before | After |
|---|---|
| `h : (M *ᵥ v) i = c i ⊢ Q` | `h : ∑ x, M i x * v x = c i` with goal `⊢ Q` |

**R4 · `rw [← add_sum_erase _ _ (mem_univ a)]`** changes the **goal** (add `at h` for a hypothesis). The lemma
is `Finset.add_sum_erase (s) (f) (h : a ∈ s) : f a + ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x`; right to left it
splits the term `a` off a sum. The two `_` are `s` and `f`, found from the goal. Placeholders:
`{ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (a : ι)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, f x)` | `⊢ P (f a + ∑ x ∈ univ.erase a, f x)` |

**R5 · `mem_univ a`** (`Finset.mem_univ`) **closes** `a ∈ univ`: it is the membership proof R4 needs.

| Before | After |
|---|---|
| `⊢ a ∈ univ` | no goals |

**R6 · `rw [div_eq_iff hc]`** changes the **goal**. The lemma is `div_eq_iff (hc : c ≠ 0) : a / c = b ↔ a = b * c`.
Placeholders: `(a b c : ℝ) (hc : c ≠ 0)`. In the exercise `hc` is `hdiag i`.

| Before | After |
|---|---|
| `⊢ a / c = b` | `⊢ a = b * c` |

**R7 · `linarith`** **closes** a goal `=`, `≤`, `<` that is a linear combination of the hypotheses. It
normalises first, so `d * x` and `x * d` are the same unknown, and a whole sum such as
`∑ j ∈ univ.erase i, A i j * xs j` is one unknown too. It never multiplies two hypotheses.

| Before | After |
|---|---|
| `h : d * x + s = c ⊢ c - s = x * d` | no goals |

---

## Part 2 · `jacobi_contract` (milestone)

Statement: under `hdom` (every row: `∑_{j≠i} |A i j| ≤ ρ |A i i|`) and `0 ≤ ρ`,
`‖jacobiStep A b x - jacobiStep A b y‖ ≤ ρ * ‖x - y‖`. Proof on paper: see *The mathematics* above; the work
is one coordinate `i`.

**R8 · `rw [pi_norm_le_iff_of_nonneg hr]`** changes the **goal**. The lemma is
`pi_norm_le_iff_of_nonneg (hr : 0 ≤ r) : ‖v‖ ≤ r ↔ ∀ i, ‖v i‖ ≤ r`: a sup norm is `≤ r` when every coordinate is.
Write `(by positivity)` (R9) for `hr`. Placeholders: `{n : ℕ} (v : Fin n → ℝ) (r : ℝ)`.

| Before | After |
|---|---|
| `⊢ ‖v‖ ≤ r` | `⊢ ∀ (i : Fin n), ‖v i‖ ≤ r` |

**R9 · `positivity`** **closes** `0 ≤ e` or `0 < e` by the shape of `e`: products, sums, powers, norms and
absolute values of things it knows are nonnegative, using hypotheses such as `hr : 0 ≤ r` for variables.

| Before | After |
|---|---|
| `hr : 0 ≤ r ⊢ 0 ≤ r * ‖v‖` | no goals |

**R10 · `abs_pos`** changes the **goal**: `abs_pos : 0 < |a| ↔ a ≠ 0`. Term form: `abs_pos.mpr ha : 0 < |a|`,
as in `have hpos : 0 < |A i i| := abs_pos.mpr (hdiag i)`. Placeholders: `(a : ℝ)`.

```lean-goal
⊢ 0 < |a|
⊢ a ≠ 0
```

**R11 · `Pi.sub_apply`** changes the **goal**: `(f - g) i = f i - g i`, entry of a difference of vectors.
Placeholders: `(f g : ι → ℝ) (i : ι)`.

| Before | After |
|---|---|
| `⊢ P ((f - g) i)` | `⊢ P (f i - g i)` |

**R12 · `Real.norm_eq_abs`** changes the **goal**: on `ℝ`, `‖r‖ = |r|`. Placeholders: `(r : ℝ)`.

```lean-goal
⊢ P ‖r‖
⊢ P |r|
```

R3-style unfolding of the sweep: `simp only [Pi.sub_apply, jacobiStep, Real.norm_eq_abs]` applies R11, the
definition of `jacobiStep` and R12 in one go.

**R13 · `rw [← sub_div]`** changes the **goal**. The lemma is `sub_div : (a - b) / c = a / c - b / c`; right to
left it merges two fractions with the same denominator. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a / c - b / c)` | `⊢ P ((a - b) / c)` |

**R14 · `abs_div`** changes the **goal**: `|a / b| = |a| / |b|`. Placeholders: `(a b : ℝ)`.

```lean-goal
⊢ P |a / b|
⊢ P (|a| / |b|)
```

**R15 · `rw [div_le_iff₀ hc]`** changes the **goal**. The lemma is
`div_le_iff₀ (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c`. In the exercise `c` is `|A i i|` and `hc` is `hpos` (R10).
Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a / c ≤ b` | `⊢ a ≤ b * c` |

**R16 · `simp only [mul_sub]`** changes the **goal**. The lemma is `mul_sub : a * (b - c) = a * b - a * c`.
`rw` cannot rewrite under the bound variable of a `∑`; `simp only` can. Placeholders:
`(s : Finset ι) (a u v : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ j ∈ s, a j * (u j - v j))` | `⊢ P (∑ x ∈ s, (a x * u x - a x * v x))` |

**R17 · `Finset.sum_sub_distrib`** changes the **goal**: `∑ j ∈ s, (f j - g j) = ∑ j ∈ s, f j - ∑ j ∈ s, g j`.
Placeholders: `(s : Finset ι) (f g : ι → ℝ)`. After R16 and R17, the identity for the numerator is a `ring`
fact: each sum is then one unknown.

| Before | After |
|---|---|
| `⊢ P (∑ j ∈ s, (f j - g j))` | `⊢ P (∑ x ∈ s, f x - ∑ x ∈ s, g x)` |

**R18 · `abs_neg`** changes the **goal**: `|-a| = |a|`. Lean prints `|-a|` as `|(-a)|`. Placeholders: `(a : ℝ)`.

```lean-goal
⊢ P |(-a)|
⊢ P |a|
```

**R19 · `calc`** **closes** `a ≤ d` from a chain of steps `a ≤ b`, `b = c`, `c ≤ d`, each with its own proof
after `:=`; mixing `≤`, `=` and `<` is allowed. Every line after the first starts with `_`, which is the
previous right side. The very first term may also be `_`: it is then the left side of the goal, so you need
not copy a long expression. Indent the `_` lines further than `calc`.

| Before | After |
|---|---|
| `⊢ a ≤ d` | no goals |

**R20 · `Finset.abs_sum_le_sum_abs`** **closes** the triangle inequality for finite sums:
`abs_sum_le_sum_abs (f) (s) : |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|`. Placeholders: `(s : Finset ι) (f : ι → ℝ)`.

```lean-goal
⊢ |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|
```

**R21 · `refine h₁.trans ?_`** changes the **goal**. `h₁.trans h₂` is `le_trans h₁ h₂ : a ≤ c` from
`h₁ : a ≤ b`, `h₂ : b ≤ c`. With `?_` for `h₂`, what is left to prove is `b ≤ c`. Typical use:
`(abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ b ≤ c` |

**R22 · `refine sum_le_sum fun j _ => ?_`** changes the **goal and the context**. The lemma is
`Finset.sum_le_sum : (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`: compare two sums over the same set
term by term. `fun j _ => ?_` names the index `j` and leaves its membership proof anonymous (`x✝`).
Placeholders: `(s : Finset ι) (f g : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ j ∈ s, f j ≤ ∑ j ∈ s, g j` | `j : ι, x✝ : j ∈ s ⊢ f j ≤ g j` |

**R23 · `abs_mul`** changes the **goal**: `|a * b| = |a| * |b|`. Placeholders: `(a b : ℝ)`.

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R24 · `gcongr`** changes the **goal**: for two sides of the same shape, such as `x * u ≤ x * w`, it leaves
the part that differs, `u ≤ w`. It proves side conditions such as `0 ≤ x` itself (by `positivity`), and it
closes the new goal at once when that goal is a hypothesis (in `jacobi_error`, the `ih`). Placeholders:
`(a u : ℝ)`.

```lean-goal
⊢ |a| * u ≤ |a| * |u|
⊢ u ≤ |u|
```

**R25 · `norm_le_pi_norm v j`** **closes** `‖v j‖ ≤ ‖v‖`: one coordinate is at most the sup norm.
Placeholders: `{n : ℕ} (v : Fin n → ℝ) (j : Fin n)`. Used on `v = x - y`, its type is `‖(x - y) j‖ ≤ ‖x - y‖`,
which R26 turns into `|x j - y j| ≤ ‖x - y‖`.

| Before | After |
|---|---|
| `⊢ ‖v j‖ ≤ ‖v‖` | no goals |

**R26 · `simpa [l] using e`** **closes** the goal: it simplifies the goal and the type of `e` with `simp`
(plus the lemmas `l`), then uses `e`. Here `simp` applies R11 (`(u - w) j` → `u j - w j`) and R12 (`‖·‖` → `|·|`).
Placeholders: `(u w : Fin n → ℝ) (j : Fin n) (r : ℝ) (h : ‖(u - w) j‖ ≤ r)`.

```lean-goal
⊢ |u j - w j| ≤ r
```

**R27 · `rw [sum_mul]`** changes the **goal**. The lemma is `Finset.sum_mul : (∑ i ∈ s, f i) * c = ∑ i ∈ s, f i * c`:
it moves a constant factor into or out of a sum. Placeholders: `(s : Finset ι) (f : ι → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((∑ i ∈ s, f i) * c)` | `⊢ P (∑ i ∈ s, f i * c)` |

### Worked combinations (W1, W2, on objects that are not the exercise's)

**W1: split one term off a sum and solve for it.** From `h : ∑ j, w j = 1`, R4 (`at h`) with R5 makes
`h : w i + ∑ x ∈ univ.erase i, w x = 1`, and R7 closes:

```lean-goal
⊢ w i = 1 - ∑ j ∈ univ.erase i, w j
```

**W2: a contraction in the sup norm**, for `half u = fun i => u i / 2`. R8 (with R9), `intro i`,
`simp only [Pi.sub_apply, half, Real.norm_eq_abs]` (R11, R12), then R13, R14, R15 (with `(by norm_num)`),
`have hi` from R25 and R26, `rw [abs_two]` (`|2| = 2`), R7:

```lean-goal
⊢ ‖half u - half w‖ ≤ 1 / 2 * ‖u - w‖
⊢ ∀ (i : Fin n), ‖(half u - half w) i‖ ≤ 1 / 2 * ‖u - w‖
⊢ |u i / 2 - w i / 2| ≤ 1 / 2 * ‖u - w‖
⊢ |u i - w i| ≤ 1 / 2 * ‖u - w‖ * |2|
⊢ |u i - w i| ≤ 1 / 2 * ‖u - w‖ * 2
```

---

## Part 3 · `jacobi_error`

Statement: `‖(jacobiStep A b)^[k] x₀ - xs‖ ≤ ρ ^ k * ‖x₀ - xs‖`. Proof: induction on `k`; the step uses
`jacobi_fixed` to write `xs` as `jacobiStep A b xs` on the left, then `jacobi_contract` and `ih`.

**R28 · `induction k with | zero => ?_ | succ k ih => ?_`** changes the **goal list**: the base case and the
step, whose context gains `k` and the induction hypothesis `ih`. You may instead write each case's proof after
its `=>` (on indented lines).

| Before | After |
|---|---|
| `⊢ P k` | `⊢ P 0`, `ih : P k ⊢ P (k + 1)` |

**R29 · `Function.iterate_zero_apply`** changes the **goal**: `f^[0] x = x`. In the base case `simp` applies
it, together with `pow_zero : a ^ 0 = 1` and `one_mul : 1 * a = a`, and closes `‖x₀ - xs‖ ≤ ‖x₀ - xs‖`.
Placeholders: `{α : Type} (f : α → α) (x : α)`.

| Before | After |
|---|---|
| `⊢ P (f^[0] x)` | `⊢ P x` |

**R30 · `rw [Function.iterate_succ_apply']`** changes the **goal**: `f^[k + 1] x = f (f^[k] x)`, the last
application comes out. (Without the prime, `Function.iterate_succ_apply` peels off the *first* one:
`f^[k] (f x)`, which is not what the contraction needs.) Placeholders: `(f : α → α) (x : α) (k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (f^[k + 1] x)` | `⊢ P (f (f^[k] x))` |

**R31 · `conv_lhs => rw [← hp]`** changes the **goal**: it rewrites only the left side of the `≤` (or `=`).
With `hp : f p = p`, the `p` on the left becomes `f p`; the right side keeps its `p`. A plain `rw [← hp]`
would rewrite every `p`. In the exercise `hp` is `jacobi_fixed A b xs hdiag hsol`, and afterwards the left
side is `‖jacobiStep A b (…) - jacobiStep A b xs‖`, the shape of `jacobi_contract`. Placeholders:
`(f : α → α) (p y : α) (hp : f p = p) (d : α → α → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ d (f y) p ≤ c * d y p` | `⊢ d (f y) (f p) ≤ c * d y p` |

**W3: the same induction for a scalar map**, `q x = x / 2 + 1` with fixed point `2`, in `guide.lean`
(`q_contract`, `q_error`): R28 with the cases written out, `simp` for `zero`, then R30, R31 with
`hfix : q 2 = 2`, and a three-line R19 `calc` whose middle step is R24 (closed by `ih`).

---

## Part 4 · `jacobi_tendsto`

Statement: for `0 ≤ ρ < 1`, `Tendsto (fun k => (jacobiStep A b)^[k] x₀) atTop (𝓝 xs)`. Proof: the distance
`‖xₖ − xs‖` lies between `0` and `ρᵏ ‖x₀ − xs‖` (by `jacobi_error`), and the upper bound tends to 0.

**R32 · `rw [tendsto_iff_norm_sub_tendsto_zero]`** changes the **goal**. The lemma is
`Tendsto u l (𝓝 L) ↔ Tendsto (fun e => ‖u e - L‖) l (𝓝 0)`: a sequence tends to `L` when its distance to `L`
tends to 0. Placeholders: `{n : ℕ} (u : ℕ → Fin n → ℝ) (L : Fin n → ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto u atTop (𝓝 L)` | `⊢ Tendsto (fun e => ‖u e - L‖) atTop (𝓝 0)` |

**R33 · `have h := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1`** changes the **context**. The lemma is
`0 ≤ r → r < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)`. If `r` is a numeral, give its type:
`(by norm_num : (0 : ℝ) ≤ 1 / 2)`. Placeholders: `(r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1)`.

| Before | After |
|---|---|
| `⊢ Q` | `h : Tendsto (fun n => r ^ n) atTop (𝓝 0) ⊢ Q` |

**R34 · `h.mul_const c`** (`Filter.Tendsto.mul_const`) changes the **context**: from `u k → a` it gives
`u k * c → a * c`. Placeholders: `(u : ℕ → ℝ) (c : ℝ) (h : Tendsto u atTop (𝓝 0))`.

| Before | After |
|---|---|
| `⊢ Q` | `h' : Tendsto (fun x => u x * c) atTop (𝓝 (0 * c)) ⊢ Q` |

**R35 · `rw [zero_mul] at h`** changes the **context**: `zero_mul : 0 * a = 0` cleans up the limit R34 left.
`simpa using h.mul_const c` does R34 and R35 in one step when the goal says `𝓝 0`.

| Before | After |
|---|---|
| `h : Tendsto u atTop (𝓝 (0 * c)) ⊢ Tendsto u atTop (𝓝 0)` | `h : Tendsto u atTop (𝓝 0) ⊢ Tendsto u atTop (𝓝 0)` |

**R36 · `refine squeeze_zero ?_ ?_ hg`** changes the **goal list**. The lemma is
`squeeze_zero : (∀ t, 0 ≤ f t) → (∀ t, f t ≤ g t) → Tendsto g l (𝓝 0) → Tendsto f l (𝓝 0)`. Each `?_` becomes
a goal; you may also pass terms directly, `squeeze_zero (fun _ => norm_nonneg _) (fun k => …) h0`.
Placeholders: `(f g : ℕ → ℝ) (hg : Tendsto g atTop (𝓝 0))`.

| Before | After |
|---|---|
| `⊢ Tendsto f atTop (𝓝 0)` | `⊢ ∀ (t : ℕ), 0 ≤ f t`, `⊢ ∀ (t : ℕ), f t ≤ g t` |

**R37 · `norm_nonneg v`** **closes** `0 ≤ ‖v‖`.

| Before | After |
|---|---|
| `⊢ 0 ≤ ‖v‖` | no goals |

**W4: the scalar limit**, `q^[k] a → 2`: R32, then `h0` from R33, R34, R35 (as one `simpa`), then
R36 with R37 and `q_error`, after R12 on the upper bound goal:

```lean-goal
⊢ Tendsto (fun k => q^[k] a) atTop (𝓝 2)
⊢ Tendsto (fun e => ‖q^[e] a - 2‖) atTop (𝓝 0)
⊢ ‖q^[k] a - 2‖ ≤ (1 / 2) ^ k * |a - 2|
⊢ |q^[k] a - 2| ≤ (1 / 2) ^ k * |a - 2|
```

---

## Traps

- `rw` cannot see under a `∑ j ∈ s, …` binder: `rw [mul_sub]` fails on `∑ j ∈ s, a j * (u j - v j)`. Use
  `simp only [mul_sub, sum_sub_distrib]` (R16, R17).
- `rw [← add_sum_erase _ _ (mem_univ i)]` must go **at** the row hypothesis (`at this`), which has the full sum
  `∑ x, …`; the goal already has only the sum over `univ.erase i`.
- `Function.iterate_succ_apply'` (with the prime) gives `f (f^[k] x)`; without the prime it gives
  `f^[k] (f x)` (R30).
- A plain `rw [← jacobi_fixed …]` rewrites **every** `xs`, including the one in `ρ ^ (k + 1) * ‖x₀ - xs‖`. Use
  `conv_lhs` (R31).
- `div_le_iff₀` needs `0 < |A i i|`, not `A i i ≠ 0`: build `hpos` with `abs_pos.mpr` first (R10, R15).
- The sweep's numerator difference is `-(…)`, so after rewriting with your identity `e` there is a `|-…|`;
  remove it with `abs_neg` (R18).
- `gcongr` silently closes a goal that is a hypothesis; if no goal is left, do not add `exact` (R24). When the
  goal left is `∑ … ≤ ρ * |A i i|`, close it with `hdom i` (it is a `∀`, so `gcongr` does not use it itself).
- After R34 the limit reads `𝓝 (0 * c)`, not `𝓝 0` (R35).
- `jacobi_tendsto` needs no new induction: it calls `jacobi_error` for each `k`.
- The specs of `jacobi_error` and `jacobi_tendsto` end with `:=` before `-- END SPEC`, so the proof replacing
  `sorry` must start with `by` (put the tactics on lines indented further than `by`).
- Write the induction alternatives `| zero => …` and `| succ k ih => …` either inline after `with` or each on
  its own line; the `calc` lines inside `succ` are indented further than `| succ`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| vector equation → coordinate | `funext i` | R1 |
| row `i` of `A *ᵥ xs = b` | `have := congrFun hsol i; simp only [mulVec, dotProduct] at this` | R2, R3 |
| split term `i` off `∑ x, f x` | `rw [← add_sum_erase _ _ (mem_univ i)] at h` | R4, R5 |
| `a / c = b` | `rw [div_eq_iff hc]` | R6 |
| linear consequence | `linarith` | R7 |
| `‖v‖ ≤ r` → coordinates | `rw [pi_norm_le_iff_of_nonneg (by positivity)]; intro i` | R8, R9 |
| `0 < \|a\|` | `abs_pos.mpr ha` | R10 |
| evaluate a coordinate | `simp only [Pi.sub_apply, f, Real.norm_eq_abs]` | R11, R12 |
| one fraction, then clear `\|c\|` | `rw [← sub_div, abs_div, div_le_iff₀ hpos]` | R13–R15 |
| expand a difference of sums | `simp only [mul_sub, sum_sub_distrib]; ring` | R16, R17 |
| `\|-a\| = \|a\|` | `rw [abs_neg]` | R18 |
| chain of inequalities | `calc _ ≤ b := … ` / `_ = c := …` | R19 |
| triangle inequality for `∑` | `(abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)` | R20–R22 |
| `\|a * b\|` | `rw [abs_mul]` | R23 |
| same shape on both sides | `gcongr` | R24 |
| `\|v j\| ≤ ‖v‖` | `simpa [Real.norm_eq_abs] using norm_le_pi_norm v j` | R25, R26 |
| factor out of a sum | `rw [sum_mul]` | R27 |
| induction | `induction k with \| zero => … \| succ k ih => …` | R28 |
| `f^[0] x`, `f^[k + 1] x` | `simp`, `rw [Function.iterate_succ_apply']` | R29, R30 |
| rewrite the left side only | `conv_lhs => rw [← h]` | R31 |
| limit → distance limit | `rw [tendsto_iff_norm_sub_tendsto_zero]` | R32 |
| `ρᵏ * c → 0` | `simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const c` | R33–R35 |
| squeeze to 0 | `squeeze_zero (fun _ => norm_nonneg _) hle h0` | R36, R37 |
| see the state | infoview | |
