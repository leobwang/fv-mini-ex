# H047 · Banach fixed-point theorem: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `intro`, `exact`, `rw`, `have`, `obtain`,
`∃`, `∧`, anonymous constructors `⟨…⟩`, `induction`. **New here** (Mathlib): metric spaces (`dist`),
complete spaces, Cauchy sequences, limits as `Filter.Tendsto`, "eventually" (`∀ᶠ`), finite sums over
`Finset.Ico`, the iterate notation `f^[n]`, and the tactics `calc`, `gcongr`, `nlinarith`, `simpa`.

The math. Let $(X, d)$ be a metric space, $f : X \to X$ with $d(f x, f y) \le k\, d(x, y)$ for all
$x, y$, where $0 \le k < 1$. Fix $x_0$ and set $x_n = f^n(x_0)$, $d_0 = d(x_0, f x_0)$.

1. *Step bound* (induction): $d(x_n, x_{n+1}) \le k^n d_0$.
2. *Distance bound* (triangle inequality + geometric sum): for $m \le n$,
   $d(x_m, x_n) \le \sum_{i=m}^{n-1} k^i d_0 \le \dfrac{k^m d_0}{1 - k}$.
3. *Cauchy*: the bound $k^m d_0/(1-k) \to 0$ as $m \to \infty$, so for every $\varepsilon > 0$ there is
   $N$ with $d(x_n, x_N) < \varepsilon$ for all $n \ge N$.
4. *Limit is fixed*: $X$ complete gives $x_n \to L$. Then $f(x_n) \to f(L)$ because
   $0 \le d(f x_n, f L) \le k\, d(x_n, L) \to 0$, and $f(x_n) = x_{n+1} \to L$. Limits are unique, so
   $f L = L$.
5. *Uniqueness*: $f x = x$, $f y = y$ give $d(x, y) \le k\, d(x, y)$, so $(1-k)\, d(x, y) \le 0$,
   $d(x, y) = 0$, $x = y$.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders. `{X : Type} [MetricSpace X]` is any metric space (in the
  exercise: your `X`); `u v w : ℕ → …` are sequences; `g : X → X` plays the role of `f`.
- "closes" means the step leaves no goal; then only the Before state is shown.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `{X : Type*} [MetricSpace X]` | `X` is any type with a distance `dist : X → X → ℝ` (symmetric, triangle inequality, `dist x y = 0 ↔ x = y`) |
| `[CompleteSpace X]` | every Cauchy sequence in `X` converges |
| `[Nonempty X]` | `X` has at least one point (an instance; get a point with R26) |
| `dist x y` | the distance $d(x, y)$, a real number |
| `f^[n] x` | `f` applied `n` times to `x` (`Nat.iterate`); `f^[0] x = x` |
| `n.succ` | `n + 1` (same thing by definition) |
| `∑ i ∈ Ico m n, g i` | $\sum_{i=m}^{n-1} g(i)$; `Ico m n` is `Finset.Ico m n = {m, …, n-1}` |
| `CauchySeq u` | `u` is Cauchy (R12 turns it into ε-N form) |
| `Tendsto u atTop (𝓝 L)` | $u_n \to L$ as $n \to \infty$ (`Filter.Tendsto`; `atTop` is "n large", `𝓝 L` is "near L") |
| `Tendsto (fun n => …) atTop (𝓝 0)` | the displayed expression tends to `0` |
| `∀ᶠ (n : ℕ) in atTop, Q n` | `Q n` holds for all large `n` ("eventually") |
| `∀ᶠ (y : ℝ) in 𝓝 0, Q y` | `Q y` holds for all `y` close enough to `0` |
| `∀ ε > 0, …` | `∀ ε, ε > 0 → …`; `intro ε hε` takes both |
| `∀ n ≥ N, …` | `∀ n, n ≥ N → …` |
| `∀ (b : ℕ), N ≤ b → Q b` | the same as `∀ b ≥ N, Q b` (how `hN` from R18 prints); `hN N le_rfl : Q N` |
| `X : Type u_1` | how `{X : Type*}` prints: `X` is a type in some universe `u_1` (ignore the level) |
| `∃! x, Q x` | exactly one `x` with `Q x`: `∃ x, Q x ∧ ∀ y, Q y → y = x` |
| `(fun x => Q x) y` | `Q y`, not yet β-reduced; `exact` accepts it as `Q y` |
| `‹T›` | "the hypothesis of type `T`" (here an instance such as `‹Nonempty X›`) |
| `inst✝ : MetricSpace X` | an unnamed instance argument |
| `case succ`, `case refine_1`, `case hbc` | labels of goals produced by `induction`, `refine`, `gcongr` |

---

## Part 1 · `iterate_step` (milestone)

Statement: `dist (f^[n] x0) (f^[n + 1] x0) ≤ k ^ n * dist x0 (f x0)`, i.e. $d(x_n, x_{n+1}) \le k^n d_0$.

**R1 · `induction n with | zero => ?_ | succ n ih => ?_`** changes the **goal list**: one goal per case
of `ℕ`; the `succ` case gains `n` and the induction hypothesis `ih`. `?_` leaves the case open for the
next tactics; in a proof put the tactics after `=>`. Placeholders: `(P : ℕ → Prop) (n : ℕ)`.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `ih : P n ⊢ P (n + 1)` |

**R2 · `Function.iterate_zero`, `Function.iterate_one`** change the **goal**: `g^[0] = id` and
`g^[1] = g` (with `zero_add : 0 + a = a`, `id_eq : id a = a`). Plain `simp` applies all four, which is
how the `zero` case closes. Placeholders: `{X : Type} (g : X → X) (x : X)`.

| Before | After |
|---|---|
| `⊢ P (g^[0] x) (g^[0 + 1] x)` | `⊢ P x (g x)` |

**R3 · `pow_zero`, `one_mul`** change the **goal**: `a ^ 0 = 1`, `1 * a = a` (`simp` knows both).
Placeholders: `(k a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (k ^ 0 * a)` | `⊢ P a` |

**R4 · `calc`** changes the **goal list**: the goal `a ≤ d` becomes one goal per step, each proved right
after its `:=`. Steps start with `_` (the previous right-hand side); `=` and `≤` (and `<`) may mix, and
the relation of the chain is the weakest one used. Placeholders: `(a b c d : ℝ)`.

```lean
calc a = b := h1
  _ ≤ c := h2
  _ = d := h3
```

| Before | After |
|---|---|
| `⊢ a ≤ d` | closed (each step by its proof) |

**R5 · `Function.iterate_succ_apply'`** changes the **goal**. The lemma is
`g^[n.succ] x = g (g^[n] x)`: it peels off the *last* application of `g`. (Unprimed
`Function.iterate_succ_apply` peels off the first: `g^[n.succ] x = g^[n] (g x)`.) Use
`simp only [Function.iterate_succ_apply']` to rewrite both sides of a goal at once.
Placeholders: `{X : Type} (g : X → X) (n : ℕ) (x : X)`.

| Before | After |
|---|---|
| `⊢ P (g^[n + 1] x)` | `⊢ P (g (g^[n] x))` |

**R6 · `have h := hf a b`** changes the **context**: it instantiates the `∀ x y` hypothesis at `a`, `b`.
As a `calc` step you write `hf _ _` and Lean fills `_` from the step's statement.
Placeholders: `{X : Type} [MetricSpace X] (g : X → X) (k : ℝ) (a b : X)`.

| Before | After |
|---|---|
| `⊢ dist (g a) (g b) ≤ k * dist a b` | `h : dist (g a) (g b) ≤ k * dist a b ⊢ dist (g a) (g b) ≤ k * dist a b` |

**R7 · `gcongr`** changes the **goal**: for `lhs ≤ rhs` with the same shape on both sides it leaves only
the differing parts as goals; side conditions such as `0 ≤ c` are proved from the context (by
`positivity` or an assumption). It also closes a remaining goal that a hypothesis states, e.g.
`k * A ≤ k * B` with `ih : A ≤ B` and `hk0 : 0 ≤ k` in the context. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `hc : 0 ≤ c ⊢ a * c ≤ b * c` | `⊢ a ≤ b` |

---

## Part 2 · `iterate_dist` (milestone)

Statement: for `m ≤ n`, `dist (f^[m] x0) (f^[n] x0) ≤ k ^ m * dist x0 (f x0) / (1 - k)`.
A five-step `calc`: telescope (R8), bound each term by Part 1 (R9), pull out `d0` (R10), bound the
geometric sum (R7 + R11), rearrange (`ring`).

**R8 · `dist_le_Ico_sum_dist u hmn`** **closes** the triangle inequality along the sequence. Statement:
`m ≤ n → dist (u m) (u n) ≤ ∑ i ∈ Ico m n, dist (u i) (u (i + 1))`.
Placeholders: `{X : Type} [MetricSpace X] (u : ℕ → X) (hmn : m ≤ n)`; for iterates
`u := fun i => f^[i] x0`.

| Before | After |
|---|---|
| `⊢ dist (u m) (u n) ≤ ∑ i ∈ Ico m n, dist (u i) (u (i + 1))` | closed |

**R9 · `Finset.sum_le_sum`** changes the **goal**: a sum is bounded termwise. Statement:
`(∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`. Term form in a `calc` step:
`sum_le_sum fun i _ => …` (the `_` is the unused `i ∈ s`).
Placeholders: `(s : Finset ℕ) (f g : ℕ → ℝ)`.

| Before | After `apply Finset.sum_le_sum` |
|---|---|
| `⊢ ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i` | `⊢ ∀ i ∈ s, f i ≤ g i` |

**R10 · `Finset.sum_mul`** changes the **goal**. Statement: `(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`.
After `rw [sum_mul]` the two sides of an equation are often identical, and `rw` closes it with `rfl`.
Placeholders: `(s : Finset ℕ) (f : ℕ → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((∑ i ∈ s, f i) * a)` | `⊢ P (∑ i ∈ s, f i * a)` |

**R11 · `geom_sum_Ico_le_of_lt_one hx0 hx1`** **closes** the geometric tail bound. Statement:
`0 ≤ x → x < 1 → ∑ i ∈ Ico m n, x ^ i ≤ x ^ m / (1 - x)` ($\sum_{i=m}^{n-1} x^i \le x^m/(1-x)$).
Placeholders: `(x : ℝ) (m n : ℕ)` (implicit). Use it after R7 has reduced
`(∑ …) * d0 ≤ k ^ m / (1 - k) * d0` to the bare sum.

| Before | After |
|---|---|
| `⊢ ∑ i ∈ Ico m n, x ^ i ≤ x ^ m / (1 - x)` | closed |

---

## Part 3 · `iterate_cauchy` (milestone)

Statement: `CauchySeq (fun n => f^[n] x0)`. Go to ε-N form (R12), prove the Part 2 bound tends to 0
(R13 → R14 → R15 → R16), extract `N` (R17 → R18), then compare (R19 → R20 → R21).

**R12 · `rw [Metric.cauchySeq_iff']`** changes the **goal**. Statement:
`CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) (u N) < ε` (every later term is within ε of `u N`).
Placeholders: `{X : Type} [MetricSpace X] (u : ℕ → X)`.

| Before | After |
|---|---|
| `⊢ CauchySeq u` | `⊢ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) (u N) < ε` |

**R13 · `tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1`** adds to the **context** (with `have`)
`r ^ n → 0`. Statement: `0 ≤ r → r < 1 → Tendsto (fun n => r ^ n) atTop (𝓝 0)`. Placeholders: `(r : ℝ)`.

| Before | After `have h := …` |
|---|---|
| `⊢ P` | `h : Tendsto (fun n => r ^ n) atTop (𝓝 0) ⊢ P` |

**R14 · `hv.mul_const b`** (lemma `Filter.Tendsto.mul_const`) adds to the **context**: limits pass through
`· * b`. Statement: `Tendsto v l (𝓝 a) → Tendsto (fun n => v n * b) l (𝓝 (a * b))`.
Placeholders: `(v : ℕ → ℝ) (a b : ℝ)`. The bound variable is renamed `x` in the display.

| Before | After `have h := hv.mul_const b` |
|---|---|
| `hv : Tendsto v atTop (𝓝 a) ⊢ P` | `h : Tendsto (fun x => v x * b) atTop (𝓝 (a * b)) ⊢ P` |

**R15 · `hv.div_const b`** (lemma `Filter.Tendsto.div_const`) adds to the **context**: limits pass through
`· / b`. Statement: `Tendsto v l (𝓝 a) → Tendsto (fun n => v n / b) l (𝓝 (a / b))`. In the display the
bound variable happens to be called `a`: `fun a => v a / b` is still "`v n / b`".

| Before | After `have h := hv.div_const b` |
|---|---|
| `hv : Tendsto v atTop (𝓝 a) ⊢ P` | `h : Tendsto (fun a => v a / b) atTop (𝓝 (a / b)) ⊢ P` |

**R16 · `simpa using e`** **closes** the goal: it simplifies both `e` and the goal, then matches them.
Here it turns the limit `0 * b` into `0`; in the exercise it turns `0 * d0 / (1 - k)` into `0`, and in
Part 5 `k * 0` into `0`. Placeholders: `(v : ℕ → ℝ) (b : ℝ)`.

| Before | After |
|---|---|
| `e : Tendsto (fun n => v n * b) atTop (𝓝 (0 * b)) ⊢ Tendsto (fun n => v n * b) atTop (𝓝 0)` | closed |

**R17 · `apply hv.eventually (p := fun y => y < ε)`** (lemma `Filter.Tendsto.eventually`) changes the
**goal**: "eventually along `v`" becomes "near the limit". Statement:
`Tendsto v l₁ l₂ → (∀ᶠ y in l₂, p y) → ∀ᶠ n in l₁, p (v n)`. Then `gt_mem_nhds hε` closes the new goal;
its statement is `b < a → ∀ᶠ x in 𝓝 b, x < a`. In the exercise use the one-term form
`hv.eventually (gt_mem_nhds hε) : ∀ᶠ n in atTop, v n < ε`.
Placeholders: `(v : ℕ → ℝ) (ε : ℝ) (hv : Tendsto v atTop (𝓝 0)) (hε : 0 < ε)`.

| Before | After |
|---|---|
| `⊢ ∀ᶠ (n : ℕ) in atTop, v n < ε` | `⊢ ∀ᶠ (y : ℝ) in 𝓝 0, y < ε` |

**R18 · `Filter.Eventually.exists_forall_of_atTop`** changes the **goal**: "for all large `n`" becomes an
explicit `N`. Statement: `(∀ᶠ n in atTop, Q n) → ∃ N, ∀ n ≥ N, Q n`. Term form:
`hQ.exists_forall_of_atTop`; with R17: `obtain ⟨N, hN⟩ := (hv.eventually (gt_mem_nhds hε)).exists_forall_of_atTop`.
Placeholders: `(Q : ℕ → Prop)`.

| Before | After `apply …` |
|---|---|
| `⊢ ∃ N, ∀ n ≥ N, Q n` | `⊢ ∀ᶠ (x : ℕ) in atTop, Q x` |

**R19 · `refine ⟨N, fun n hn => ?_⟩`** changes the **goal and the context**: it gives the witness `N` and
introduces the `∀ n ≥ N` binders. Placeholders: `(Q : ℕ → ℕ → Prop) (N : ℕ)`.

| Before | After |
|---|---|
| `⊢ ∃ M, ∀ n ≥ M, Q n M` | `n : ℕ, hn : n ≥ N ⊢ Q n N` |

**R20 · `rw [dist_comm]`** changes the **goal**. Statement: `dist x y = dist y x`. Needed because Part 2
bounds `dist (x N) (x n)` while R12 asks for `dist (x n) (x N)`.
Placeholders: `{X : Type} [MetricSpace X] (x y : X)`.

| Before | After |
|---|---|
| `⊢ P (dist x y)` | `⊢ P (dist y x)` |

**R21 · `h1.trans_lt h2`** (lemma `LE.le.trans_lt`) **closes** `a < c` from `h1 : a ≤ b` and
`h2 : b < c`. Placeholders: `(a b c : ℝ)`. In the exercise `h1` is Part 2 and `h2` is `hN N le_rfl`
(`le_rfl : N ≤ N`).

| Before | After |
|---|---|
| `h1 : a ≤ b, h2 : b < c ⊢ a < c` | closed |

---

## Part 4 · `fixed_unique` (milestone)

Statement: two fixed points `f x = x`, `f y = y` are equal. Instantiate `hf` (R6), rewrite with the
fixed-point equations (R22), get `dist x y ≤ 0` (R23 + R24), conclude (R25).

**R22 · `rw [ha, hb] at h`** changes the **context**: it rewrites inside the hypothesis `h` instead of the
goal. Placeholders: `{X : Type} [MetricSpace X] (g : X → X) (a b : X) (ha : g a = b) (hb : g b = a)`.

| Before | After |
|---|---|
| `h : dist (g a) (g b) ≤ k ⊢ dist b a ≤ k` | `h : dist b a ≤ k ⊢ dist b a ≤ k` |

**R23 · `dist_nonneg`** gives `0 ≤ dist x y`. Its `x y` are implicit: write
`dist_nonneg (x := a) (y := b)` to fix them, or just `dist_nonneg` where Lean can infer them.

| Before | After `have h := dist_nonneg (x := a) (y := b)` |
|---|---|
| `⊢ P` | `h : 0 ≤ dist a b ⊢ P` |

**R24 · `nlinarith [t₁, …]`** **closes** an inequality over `ℝ` that follows from the hypotheses and the
hint terms `tᵢ` by linear arithmetic after multiplying pairs of them. Here the hint is
`sq_nonneg (a - b) : 0 ≤ (a - b) ^ 2`. In the exercise the facts are `h : d ≤ k * d`, `hk1 : k < 1`
and the hint `dist_nonneg`; the product `(1 - k) * d ≥ 0` is what it needs. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ 2 * a * b ≤ a ^ 2 + b ^ 2` | closed |

**R25 · `dist_le_zero`** changes the **goal**. Statement: `dist x y ≤ 0 ↔ x = y` (needs a metric space,
where distance 0 means equal). `apply dist_le_zero.mp` uses the `→` direction backwards.
Placeholders: `{X : Type} [MetricSpace X] (a b : X)`.

| Before | After |
|---|---|
| `⊢ a = b` | `⊢ dist a b ≤ 0` |

---

## Part 5 · `banach_fixed_point`

Statement: `∃! x, f x = x` for a contraction `f` on a nonempty complete metric space. Pick `x0` (R26),
get the limit `L` (R27 with Part 3), show `f (x n) → f L` (R28 → R29 → R6, R23, R30 → R16), show
`f (x n) → L` (R31 → R32), conclude `f L = L` (R33), package with Part 4 (R34).

**R26 · `obtain ⟨x0⟩ := ‹Nonempty X›`** changes the **context**: it unpacks the instance into a point.
Placeholders: `{X : Type} [Nonempty X]`.

| Before | After |
|---|---|
| `⊢ P` | `x0 : X ⊢ P` |

**R27 · `cauchySeq_tendsto_of_complete hu`** adds to the **context** (with `obtain`) a limit. Statement:
`CauchySeq u → ∃ L, Tendsto u atTop (𝓝 L)`; needs `[CompleteSpace X]`.
Placeholders: `{X : Type} [MetricSpace X] [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u)`.

| Before | After `obtain ⟨L, hL⟩ := …` |
|---|---|
| `hu : CauchySeq u ⊢ P` | `L : X, hL : Tendsto u atTop (𝓝 L) ⊢ P` |

**R28 · `rw [tendsto_iff_dist_tendsto_zero] at hL ⊢`** changes the **goal and the context**: convergence in
`X` becomes convergence of real distances to 0. Statement:
`Tendsto u l (𝓝 a) ↔ Tendsto (fun n => dist (u n) a) l (𝓝 0)`. `at hL ⊢` rewrites `hL` and the goal.
Lean renames bound variables to avoid clashes (`b`, `b_1`); they are dummies.
Placeholders: `{X : Type} [MetricSpace X] (u w : ℕ → X) (a b : X)`.

| Before | After |
|---|---|
| `hL : Tendsto u atTop (𝓝 a) ⊢ Tendsto w atTop (𝓝 b)` | `hL : Tendsto (fun b => dist (u b) a) atTop (𝓝 0) ⊢ Tendsto (fun b_1 => dist (w b_1) b) atTop (𝓝 0)` |

**R29 · `refine squeeze_zero (g := w) (fun n => ?_) (fun n => ?_) ?_`** changes the **goal list**: the
sandwich lemma. Statement: `(∀ t, 0 ≤ v t) → (∀ t, v t ≤ w t) → Tendsto w l (𝓝 0) → Tendsto v l (𝓝 0)`
(all in `ℝ`). Placeholders: `(v w : ℕ → ℝ)`. In the exercise `v n = dist (f (x n)) (f L)`,
`w n = k * dist (x n) L`; the first two goals are `dist_nonneg` (R23) and `hf _ L` (R6), so they can be
given directly and `(g := …)` is not needed.

| Before | After |
|---|---|
| `⊢ Tendsto v atTop (𝓝 0)` | `n : ℕ ⊢ 0 ≤ v n`, `n : ℕ ⊢ v n ≤ w n`, `⊢ Tendsto w atTop (𝓝 0)` |

**R30 · `hv.const_mul b`** (lemma `Filter.Tendsto.const_mul`) adds to the **context**: limits pass through
`b * ·`. Statement: `Tendsto v l (𝓝 a) → Tendsto (fun n => b * v n) l (𝓝 (b * a))`. With `a = 0`, R16
turns `b * 0` into `0`. Placeholders: `(v : ℕ → ℝ) (a b : ℝ)`.

| Before | After `have h := hv.const_mul b` |
|---|---|
| `hv : Tendsto v atTop (𝓝 a) ⊢ P` | `h : Tendsto (fun x => b * v x) atTop (𝓝 (b * a)) ⊢ P` |

**R31 · `simp only [← Function.iterate_succ_apply' g]`** changes the **goal**: R5 right to left, folding
`g (g^[n] x)` into `g^[n.succ] x`, also under `fun n => …` (where `rw` cannot rewrite, because the
term mentions the bound `n`). `n.succ` is `n + 1` by definition, so `exact` accepts facts stated with
`n + 1`. Placeholders: `{X : Type} (g : X → X) (x : X) (Q : (ℕ → X) → Prop)`.

| Before | After |
|---|---|
| `⊢ Q fun n => g (g^[n] x)` | `⊢ Q fun n => g^[n.succ] x` |

**R32 · `apply (tendsto_add_atTop_iff_nat (f := u) 1).mpr`** changes the **goal**: a shifted sequence has
the same limit. Statement: `Tendsto (fun n => u (n + k)) atTop l ↔ Tendsto u atTop l` (its sequence
argument is the implicit `f`); `.mpr` is the `←` direction. Placeholders:
`{X : Type} [MetricSpace X] (u : ℕ → X) (a : X)`. After R31 the goal shows `f^[n.succ] x0`, not a literal
`u (n + 1)`, so plain `apply (tendsto_add_atTop_iff_nat 1).mpr` fails ("could not unify"): name the
sequence, `(f := fun n => f^[n] x0)`, or give the hypothesis at once, `exact (tendsto_add_atTop_iff_nat 1).mpr hL`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun n => u (n + 1)) atTop (𝓝 a)` | `⊢ Tendsto u atTop (𝓝 a)` |

**R33 · `tendsto_nhds_unique ha hb`** **closes** `a = b`: one sequence has at most one limit. Statement:
`Tendsto u l (𝓝 a) → Tendsto u l (𝓝 b) → a = b` (in a Hausdorff space, which every metric space is).
Placeholders: `{X : Type} [MetricSpace X] (u : ℕ → X) (a b : X)`.

| Before | After |
|---|---|
| `ha : Tendsto u atTop (𝓝 a), hb : Tendsto u atTop (𝓝 b) ⊢ a = b` | closed |

**R34 · `refine ⟨a, ha, fun y hy => ?_⟩`** changes the **goal and the context**: for `∃! x, Q x` give the
witness, its property, and leave uniqueness open. Placeholders: `{X : Type} (Q : X → Prop) (a : X)`.

| Before | After |
|---|---|
| `⊢ ∃! x, Q x` | `y : X, hy : (fun x => Q x) y ⊢ y = a` |

### Worked combinations (W1–W3 in `guide.lean`, on real sequences)

**W1.** `u (n+1) ≤ r * u n` and `0 ≤ r` give `u n ≤ r ^ n * u 0`: R1 with `simp` for `zero`, then a
`calc` (R4) whose middle step is `by gcongr` (R7, closed by `ih`) and whose last is `by ring`.
This is the shape of Part 1.

**W2.** `∃ N, ∀ n ≥ N, (1/2)^n * 5 < ε`: first `hlim` by R13 → R14 → R16, then R17 + R18 in one term.

```lean-goal
⊢ ∃ N, ∀ n ≥ N, (1 / 2) ^ n * 5 < ε
```

**W3.** `u (n+1) = c * u n` and `u → a` give `a = c * a`: the shifted sequence tends to `a` (R32) and to
`c * a` (`simp only [hu]`, then R30), so R33. This is the shape of Part 5.

```lean-goal
⊢ a = c * a
```

---

## Traps

- `Function.iterate_succ_apply'` (with `'`) peels the *outer* `f`: `f^[n+1] x = f (f^[n] x)`. The
  unprimed one gives `f^[n] (f x)`, which does not match `hf`.
- `rw` cannot rewrite under `fun n => …` when the pattern mentions `n`; use `simp only [...]` (R31).
- In the `calc` step of Part 1, `rw [Function.iterate_succ_apply', Function.iterate_succ_apply']` fixes
  the pattern to the first match each time and leaves `f^[n + 1] x0` against `f (f^[n] x0)`; it fails.
  `simp only [Function.iterate_succ_apply']` rewrites both sides until no `f^[_ + 1]` is left, then closes.
- `apply (tendsto_add_atTop_iff_nat 1).mpr` cannot guess the sequence when the goal shows `f^[n.succ] x0`;
  write `(f := fun n => f^[n] x0)` or pass `hL` (R32).
- `gcongr` needs the side goal `0 ≤ k` (or `0 ≤ dist …`) to be provable from the context; keep
  `hk0` around.
- `Metric.cauchySeq_iff'` asks for `dist (u n) (u N)`, Part 2 bounds `dist (u N) (u n)`: `dist_comm` (R20).
- `nlinarith` does not know `0 ≤ dist x y`; pass `dist_nonneg` as a hint (R23, R24).
- Milestones are optional: you may change or delete them, but the spec theorem must keep its statement.
- Do not use Mathlib's own contraction theory (`ContractingWith`, `LipschitzWith`, the
  `…_geometric` lemmas): they are on the `BANNED:` line and the checker rejects them.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on `n` with names | `induction n with \| zero => … \| succ n ih => …` | R1 |
| `f^[0] x`, `k ^ 0` | `simp` | R2, R3 |
| chain of `=`/`≤` | `calc a = b := … ; _ ≤ c := …` | R4 |
| `f^[n+1] x → f (f^[n] x)` | `simp only [Function.iterate_succ_apply']` | R5 |
| use a `∀` hypothesis | `hf _ _` / `have h := hf a b` | R6 |
| `k * A ≤ k * B` from `A ≤ B` | `gcongr` | R7 |
| triangle inequality along a sequence | `dist_le_Ico_sum_dist u hmn` | R8 |
| termwise bound of sums | `sum_le_sum fun i _ => …` | R9 |
| `(∑ f) * a = ∑ f * a` | `rw [sum_mul]` | R10 |
| geometric tail | `geom_sum_Ico_le_of_lt_one hk0 hk1` | R11 |
| Cauchy → ε-N | `rw [Metric.cauchySeq_iff']` | R12 |
| `r ^ n → 0` | `tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1` | R13 |
| limits through `* b`, `/ b`, `b *` | `.mul_const b`, `.div_const b`, `.const_mul b` | R14, R15, R30 |
| clean `0 * b`, `k * 0` in a limit | `simpa using …` | R16 |
| `v → 0`, `0 < ε` → `∃ N, ∀ n ≥ N, v n < ε` | `(hv.eventually (gt_mem_nhds hε)).exists_forall_of_atTop` | R17, R18 |
| witness + binders | `refine ⟨N, fun n hn => ?_⟩` | R19 |
| swap `dist` arguments | `rw [dist_comm]` | R20 |
| `a ≤ b`, `b < c` → `a < c` | `h1.trans_lt h2` | R21 |
| rewrite a hypothesis | `rw [hx, hy] at h` | R22 |
| `0 ≤ dist x y` | `dist_nonneg` | R23 |
| nonlinear arithmetic | `nlinarith [dist_nonneg (x := x) (y := y)]` | R24 |
| `dist x y ≤ 0 → x = y` | `dist_le_zero.mp` | R25 |
| a point of `X` | `obtain ⟨x0⟩ := ‹Nonempty X›` | R26 |
| Cauchy → limit | `obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete h` | R27 |
| convergence via distances | `rw [tendsto_iff_dist_tendsto_zero] at hL` (append ⊢ for the goal too) | R28 |
| sandwich to 0 | `squeeze_zero (fun n => …) (fun n => …) ?_` | R29 |
| fold `f (f^[n] x)` under `fun` | `simp only [← Function.iterate_succ_apply' f]` | R31 |
| shifted sequence | `(tendsto_add_atTop_iff_nat 1).mpr hL` / `apply (tendsto_add_atTop_iff_nat (f := u) 1).mpr` | R32 |
| two limits are equal | `tendsto_nhds_unique h1 h2` | R33 |
| `∃! x, Q x` | `refine ⟨L, hL, fun y hy => ?_⟩` | R34 |
