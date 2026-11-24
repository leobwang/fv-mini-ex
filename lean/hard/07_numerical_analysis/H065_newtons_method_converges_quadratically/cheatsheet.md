# H065 · Newton's method converges quadratically: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real analysis on `ℝ`: derivatives
(`deriv`, `iteratedDeriv`, derivatives *within* a set), smoothness classes (`ContDiff`), intervals
(`Icc`, `uIcc`), Taylor polynomials with the Lagrange remainder; absolute values `|·|`; the Mathlib
tactics `field_simp`, `linear_combination`, `gcongr`, `positivity`, `calc`; function iteration `g^[n]`.

The mathematics. Newton's step for a root of `f : ℝ → ℝ` is `N(x) = x - f(x)/f'(x)`. Let `r` be a root,
`f(r) = 0`. Taylor's theorem of order 1 at `x` with Lagrange remainder: for some `ξ` between `x` and
`r`, `0 = f(r) = f(x) + f'(x)(r - x) + f''(ξ)/2·(r - x)²`. Dividing by `f'(x)` gives the exact error
`N(x) - r = f''(ξ)/2·(r - x)²/f'(x)`. With `|f''| ≤ M` everywhere and `|f'(x)| ≥ m > 0`:
`|N(x) - r| ≤ C|x - r|²`, `C = M/(2m)`. Multiplying by `C`: the scaled error `εₙ = C|xₙ - r|` obeys
`εₙ₊₁ ≤ εₙ²`, so `εₙ ≤ ε₀^(2ⁿ) ≤ (Cδ)^(2ⁿ)` when `|x₀ - r| ≤ δ`: once `Cδ < 1`, the number of correct
digits doubles at every step. The hypotheses hold for all `t`, which is strong but not vacuous:
`f(x) = 2x + sin x` has `f' = 2 + cos ≥ 1`, `|f''| = |sin| ≤ 1`, root `0`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`.
  `G : Prop` is "any goal" in entries that only change the context.
- `g : ℝ → ℝ` stands for the exercise's `f`; `a b` for its points; `s : Set ℝ` for a set of reals.
- A state containing `|` (absolute value) cannot sit in a table's code span; it is in a
  ```` ```lean-goal ```` block below the table, before first, after second.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `deriv f x` | the derivative `f'(x)` (Mathlib returns `0` where `f` is not differentiable) |
| `iteratedDeriv n f x` | the `n`-th derivative `f⁽ⁿ⁾(x)`; `iteratedDeriv 2 f ξ` is `f''(ξ)` |
| `iteratedDerivWithin n f s x`, `derivWithin f s x` | the same, but derivatives taken only along points of the set `s` (one-sided at an endpoint) |
| `ContDiff ℝ 2 f` | `f` is `C²`: twice differentiable with continuous second derivative |
| `ContDiffOn ℝ n f s`, `ContDiffAt ℝ n f x` | `Cⁿ` on the set `s`; `Cⁿ` near the point `x` |
| `ContDiffAt ℝ (↑n) g a` | the order `n : ℕ` cast to `WithTop ℕ∞` (orders may be `∞` or `ω`), where `ContDiff` takes it |
| `Icc a b`, `uIcc a b`, `uIoo a b` | `[a, b]`; `[min a b, max a b]` (the "unordered" interval); `(min a b, max a b)` |
| `UniqueDiffOn ℝ s` | derivatives within `s` are unique at every point of `s`; true for `[a, b]` with `a < b`, false for a single point |
| `taylorWithinEval f n s x₀ x` | the degree-`n` Taylor polynomial of `f` at `x₀` (coefficients: derivatives within `s`), evaluated at `x` |
| `c • v` | scalar times vector; on `ℝ` it is `c * v` (`norm_num` and `simp` turn it into `*`) |
| `(1 + 1).factorial`, `Nat.factorial 0` | `(1 + 1)!` and `0!`, natural numbers; `↑` casts them to `ℝ` |
| `↑0 + 1` | the natural number `0` cast to `ℝ`, plus `1` |
| `a⁻¹` | the inverse `1 / a` (in `ℝ`, `0⁻¹ = 0`) |
| `\|a\|` | the absolute value of `a` |
| `g^[n] a` | `g` applied `n` times to `a` (`Nat.iterate`); `g^[0] a = a` |
| `q ^ 2 ^ n` | `q ^ (2 ^ n)`: `^` groups to the right |
| `newton f x` | the exercise's Newton step `x - f x / deriv f x`; it does not unfold by itself (R18) |
| `n✝`, `a✝` | names a tactic made that you cannot type; name them with `with` or `case … n ih` |
| `case inl`, `case inr`, `case zero`, `case succ`, `case hab`, `case hbc` | goal tags: left/right of an `∨`, the two induction cases, `gcongr` subgoals |

---

## Part 1 · `taylor1` (milestone)

Statement: for `f ∈ C²` and any `x y`, some `ξ` has `f y = f x + f'(x)(y - x) + f''(ξ)/2·(y - x)²`.
Mathlib's Taylor theorem needs `x ≠ y` and phrases everything with derivatives *within* `uIcc x y`;
the work is converting that to plain `deriv`. Used by Part 2.

**R1 · `rcases eq_or_ne x y with rfl | hxy`** changes the **goal list and the context**. `eq_or_ne x y :
x = y ∨ x ≠ y`. The pattern `rfl` substitutes `y := x` in the first case; `hxy` names `x ≠ y` in the
second. Placeholders: `{α : Type} (x y : α) (P : α → α → Prop)`.

| Before | After |
|---|---|
| `⊢ P x y` | `⊢ P x x`, `hxy : x ≠ y ⊢ P x y` |

**R2 · `rw [sub_self]`, then `simp`** changes the **goal**, then **closes** it. `sub_self : a - a = 0`;
`rw` replaces every `d - d`. `simp` then uses `mul_zero`, `zero_pow`, `add_zero`. In the exercise one
`simp` does both steps. Placeholders: `(a b c d : ℝ)`.

| Before | After `rw [sub_self]` | After `simp` |
|---|---|---|
| `⊢ c = c + a * (d - d) + b * (d - d) ^ 2` | `⊢ c = c + a * 0 + b * 0 ^ 2` | no goals |

**R3 · `hg.contDiffOn`** (lemma `ContDiff.contDiffOn : ContDiff 𝕜 n g → ContDiffOn 𝕜 n g s`) changes the
**context** when used in a `have`. Smooth everywhere implies smooth on any set `s`; Lean finds `s` from
where you use it. Placeholders: `(g : ℝ → ℝ) (s : Set ℝ) (hg : ContDiff ℝ 2 g)`.

| Before | After `have h := hg.contDiffOn (s := s)` |
|---|---|
| `hg : ContDiff ℝ 2 g ⊢ ContDiffOn ℝ 2 g s` | `h : ContDiffOn ℝ 2 g s ⊢ ContDiffOn ℝ 2 g s` |

**R4 · `obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hab hg`** changes the
**context**. Statement: `x₀ ≠ x → ContDiffOn ℝ (↑n + 1) f (uIcc x₀ x) → ∃ x' ∈ uIoo x₀ x,
f x - taylorWithinEval f n (uIcc x₀ x) x₀ x = iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) / ↑(n + 1).factorial`.
`(n := 1)` fixes the named implicit argument `n`; `ContDiffOn ℝ 2` is accepted as `ContDiffOn ℝ (↑1 + 1)`.
The pattern `-` discards `ξ ∈ uIoo a b` (not needed here). Placeholders: `(g : ℝ → ℝ) (a b : ℝ)
(hab : a ≠ b) (hg : ContDiffOn ℝ 2 g (uIcc a b))`.

| Before | After |
|---|---|
| `hg : ContDiffOn ℝ 2 g (uIcc a b) ⊢ G` | `ξ : ℝ, hξ : g b - taylorWithinEval g 1 (uIcc a b) a b = iteratedDeriv (1 + 1) g ξ * (b - a) ^ (1 + 1) / ↑(1 + 1).factorial ⊢ G` |

**R5 · `rcases hab.lt_or_gt with h | h`** changes the **goal list and the context**. `Ne.lt_or_gt : a ≠ b →
a < b ∨ b < a` (in any linear order, `ℝ` included). Placeholders: `(a b : ℝ) (hab : a ≠ b) (P : Prop)`.

| Before | After |
|---|---|
| `hab : a ≠ b ⊢ P` | `h : a < b ⊢ P`, `h : b < a ⊢ P` |

**R6 · `rw [uIcc_of_le h.le]`** changes the **goal**. `Set.uIcc_of_le : a ≤ b → uIcc a b = Icc a b`;
`h.le` turns `h : a < b` into `a ≤ b`. Placeholders: `(a b : ℝ) (h : a < b) (P : Set ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (uIcc a b)` | `⊢ P (Icc a b)` |

**R7 · `rw [uIcc_of_ge h.le]`** changes the **goal**. `Set.uIcc_of_ge : b ≤ a → uIcc a b = Icc b a`.
Placeholders: `(a b : ℝ) (h : b < a) (P : Set ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (uIcc a b)` | `⊢ P (Icc b a)` |

**R8 · `exact uniqueDiffOn_Icc h`** **closes** the goal. `uniqueDiffOn_Icc : a < b → UniqueDiffOn ℝ (Icc a b)`.
Placeholders: `(a b : ℝ) (h : a < b)`.

| Before | After |
|---|---|
| `h : a < b ⊢ UniqueDiffOn ℝ (Icc a b)` | no goals |

**R9 · `apply ContDiffAt.of_le hg.contDiffAt`** changes the **goal**. `ContDiff.contDiffAt : ContDiff 𝕜 n g →
ContDiffAt 𝕜 n g a`; `ContDiffAt.of_le : ContDiffAt 𝕜 n g a → m ≤ n → ContDiffAt 𝕜 m g a` (lower the order).
What is left is the order inequality, which `norm_num` closes. As a term: `hg.contDiffAt.of_le (by norm_num)`.
Placeholders: `(g : ℝ → ℝ) (a : ℝ) (hg : ContDiff ℝ 2 g)`.

| Before | After |
|---|---|
| `⊢ ContDiffAt ℝ 1 g a` | `⊢ 1 ≤ 2` |

**R10 · `exact left_mem_uIcc`** **closes** the goal. `Set.left_mem_uIcc : a ∈ uIcc a b` (`a`, `b` implicit).
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ∈ uIcc a b` | no goals |

**R11 · `rw [iteratedDerivWithin_eq_iteratedDeriv hs hg ha]`** changes the **goal**. Statement:
`UniqueDiffOn 𝕜 s → ContDiffAt 𝕜 (↑n) g a → a ∈ s → iteratedDerivWithin n g s a = iteratedDeriv n g a`.
In the exercise its three arguments come from your `UniqueDiffOn` fact (R5–R8), R9 and R10.
Placeholders: `(g : ℝ → ℝ) (s : Set ℝ) (a : ℝ) (n : ℕ) (hs : UniqueDiffOn ℝ s) (hg : ContDiffAt ℝ n g a)
(ha : a ∈ s)`.

| Before | After |
|---|---|
| `⊢ P (iteratedDerivWithin n g s a)` | `⊢ P (iteratedDeriv n g a)` |

**R12 · `rw [iteratedDeriv_one]`** changes the **goal**. `iteratedDeriv_one : iteratedDeriv 1 g = deriv g`.
Placeholders: `(g : ℝ → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (iteratedDeriv 1 g a)` | `⊢ P (deriv g a)` |

**R13 · `rw [taylorWithinEval_succ] at h`** changes the **context**. Statement: `taylorWithinEval g (n + 1) s a b =
taylorWithinEval g n s a b + (((↑n + 1) * ↑n.factorial)⁻¹ * (b - a) ^ (n + 1)) • iteratedDerivWithin (n + 1) g s a`.
`rw … at h` rewrites the hypothesis `h` instead of the goal. With `1 = 0 + 1` it peels off the linear term.
Placeholders: `(g : ℝ → ℝ) (s : Set ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `h : P (taylorWithinEval g 1 s a b) ⊢ G` | `h : P (taylorWithinEval g 0 s a b + (((↑0 + 1) * ↑(Nat.factorial 0))⁻¹ * (b - a) ^ (0 + 1)) • iteratedDerivWithin (0 + 1) g s a)` (Lean prints it over several lines) |

**R14 · `rw [taylor_within_zero_eval] at h`** changes the **context**. `taylor_within_zero_eval :
taylorWithinEval g 0 s a b = g a` (the degree-0 polynomial is the constant `g a`). Placeholders as in R13.

| Before | After |
|---|---|
| `h : P (taylorWithinEval g 0 s a b) ⊢ G` | `h : P (g a) ⊢ G` |

**R15 · `norm_num at h`** changes the **context**: it evaluates the numerals in `h` (`(↑0 + 1) * ↑0! = 1`,
`(…)⁻¹ = 1`, `e ^ (0 + 1) = e`, `1 + 1 = 2`, `↑(1 + 1)! = 2`) and turns `•` into `*`. It also rewrites
`iteratedDerivWithin 1` into `derivWithin` and `iteratedDeriv 1` into `deriv`: see Traps for the order.
Placeholders: `(g : ℝ → ℝ) (t c e : ℝ)`.

| Before | After |
|---|---|
| `h : (((↑0 + 1) * ↑(Nat.factorial 0))⁻¹ * e ^ (0 + 1)) • c = iteratedDeriv (1 + 1) g t * e ^ (1 + 1) / ↑(1 + 1).factorial ⊢ G` | `h : e * c = iteratedDeriv 2 g t * e ^ 2 / 2 ⊢ G` |

**R16 · `linear_combination k * h`** **closes** an equation goal `L = R` given `h : A = B`, when
`L - R - k * (A - B) = 0` holds by `ring` (commutative-ring arithmetic; `/ 2` counts as `* 2⁻¹`). With
`k = 1` write `linear_combination h`. Several facts: `linear_combination h₁ - 3 * h₂`. Find `k` by
comparing one term of `L - R` with the same term of `A - B`. Placeholders: `(a b c : ℝ) (h : a - b = c)`.

| Before | After |
|---|---|
| `h : a - b = c ⊢ 2 * a = 2 * b + 2 * c` | no goals |

---

## Part 2 · `newton_error_eq` (milestone)

Statement: if `f r = 0` and `f'(x) ≠ 0`, some `ξ` has `newton f x - r = f''(ξ)/2·(r - x)²/f'(x)`. Apply
`taylor1` at `x`, evaluated at `y := r`, then do algebra. Used by Part 4.

**R17 · `have h := h₁.symm.trans h₂`** changes the **context**. `Eq.symm : a = b → b = a`, `Eq.trans :
a = b → b = c → a = c`; dot notation `h₁.symm.trans h₂` chains them. In the exercise: the Taylor
identity `f r = …` and `hroot : f r = 0` give `… = 0`. Placeholders: `{α : Type} (a b c : α)`.

| Before | After |
|---|---|
| `h₁ : a = b, h₂ : a = c ⊢ G` | `h : b = c ⊢ G` |

**R18 · `unfold D`** changes the **goal**: the defined name is replaced by its body. A `def` does not unfold
by itself under `rw`/`field_simp`; `unfold newton` does it in the exercise. The guide uses its own
`halve g x = g x / 2`. Placeholders: `(g : ℝ → ℝ) (x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (halve g x)` | `⊢ P (g x / 2)` |

**R19 · `field_simp`** changes the **goal**: it multiplies out every division whose denominator it can
prove nonzero, from hypotheses such as `hb : b ≠ 0` or `hm : 0 < m`, or because it is a numeral like `2`.
The result is an equation without `/`, often with the sides reordered; follow with `linear_combination`
(R16) or `ring`. If the cleared equation already holds by `ring`, `field_simp` closes the goal itself (the
`= … * m` step of Part 4 needs nothing else). Placeholders: `(a b c d : ℝ) (hb : b ≠ 0)`.

| Before | After |
|---|---|
| `hb : b ≠ 0 ⊢ a - c / b = d` | `⊢ a * b - c = b * d` |

---

## Part 3 · `bound_nonneg` (milestone)

Statement: if `|g t| ≤ M` for all `t`, then `0 ≤ M`. Evaluate at any point, `t = 0`. Used in Parts 4–6:
`M ≥ 0` is what makes `C = M/(2m) ≥ 0`.

**R20 · `abs_nonneg a : 0 ≤ |a|`** changes the **context** when used in a `have`. Placeholders: `(a : ℝ)`.

| Before | After `have h := abs_nonneg a` |
|---|---|
| `⊢ G` | context gains `h : 0 ≤ \|a\|` |

**R21 · `h₁.trans h₂`, `h₁.trans_le h₂`** change the **context** (in a `have`) or close the goal (with
`exact`). `LE.le.trans : a ≤ b → b ≤ c → a ≤ c`, `LT.lt.trans_le : a < b → b ≤ c → a < c` (also
`trans_lt`). Placeholders: `(a b c : ℝ)`.

| Before | After `have h := h₁.trans_le h₂` |
|---|---|
| `h₁ : a < b, h₂ : b ≤ c ⊢ G` | `h : a < c ⊢ G` |

---

## Part 4 · `newton_quadratic`

Statement: `|newton f x - r| ≤ M / (2 * m) * |x - r| ^ 2` when `0 < m ≤ |f'(x)|` and `|f''| ≤ M`.
Substitute the exact error (Part 2), split the absolute value into factors, clear `/ |f'(x)|`, then a
three-step `calc`.

**R22 · `abs_pos.mp ha`** changes the **context** (in a `have`). `abs_pos : 0 < |a| ↔ a ≠ 0`; `.mp` is the
left-to-right direction. In the exercise it turns `0 < |deriv f x|` into the `deriv f x ≠ 0` that Part 2
needs. Placeholders: `(a : ℝ) (ha : 0 < |a|)`.

| Before | After `have h := abs_pos.mp ha` |
|---|---|
| `⊢ G` (with `ha : 0 < \|a\|`) | `h : a ≠ 0 ⊢ G` |

**R23 · `rw [abs_div]`** changes the **goal**. `abs_div : |a / b| = |a| / |b|`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| first line below (`\|` cannot sit in a table's code span) | second line below |

```lean-goal
⊢ P |a / b|
⊢ P (|a| / |b|)
```

**R24 · `rw [abs_mul]`** changes the **goal**. `abs_mul : |a * b| = |a| * |b|`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| first line below | second line below |

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R25 · `rw [abs_two]`** changes the **goal**. `abs_two : |2| = 2`.

| Before | After |
|---|---|
| first line below | `⊢ P 2` |

```lean-goal
⊢ P |2|
```

**R26 · `rw [abs_pow]`** changes the **goal**. `abs_pow : |a ^ n| = |a| ^ n`. Placeholders: `(a : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| first line below | second line below |

```lean-goal
⊢ P |a ^ n|
⊢ P (|a| ^ n)
```

**R27 · `rw [abs_sub_comm a b]`** changes the **goal**. `abs_sub_comm a b : |a - b| = |b - a|`. Give the
arguments: without them `rw` flips the first `|_ - _|` it meets, which may be the wrong one. In the
exercise the error formula has `(r - x)`, the goal `|x - r|`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| first line below | second line below |

```lean-goal
⊢ P |a - b|
⊢ P |b - a|
```

**R28 · `rw [div_le_iff₀ hc]`** changes the **goal**. `div_le_iff₀ : 0 < c → (b / c ≤ a ↔ b ≤ a * c)`; `rw`
with an `↔` replaces the whole inequality. Placeholders: `(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ b / c ≤ a` | `⊢ b ≤ a * c` |

**R29 · `calc`** changes the **goal list**: one goal `a ≤ d` becomes one goal per step. The first line
names the start term; each later line starts with `_` (the previous right-hand side). `≤` and `=` steps
combine into `≤`. Each step is `term := proof`, often `:= by tac`. Placeholders: `(a b c d : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ d` | goals `a ≤ b`, `b = c`, `c ≤ d`, each closed by its `:= …` |

**R30 · `gcongr`** changes the **goal**: for `lhs ≤ rhs` with the same shape on both sides, it keeps the
parts that differ and asks for `≤` between them ("generalized congruence"). Side goals such as `0 ≤ c`
(multiplying by `c` preserves `≤`) it proves itself with `positivity` (R31), which can use hypotheses
like `hc : 0 ≤ c`; a remaining goal that is a hypothesis it closes by `assumption`. Placeholders:
`(f : ℝ → ℝ) (a b c : ℝ) (hc : 0 ≤ c)`.

| Before | After |
|---|---|
| `hc : 0 ≤ c ⊢ f a * c ≤ b * c` | `⊢ f a ≤ b` |

---

## Part 5 · `scaled_step` (milestone)

Statement: `C·|newton f x - r| ≤ (C·|x - r|)²` with `C = M/(2m)`: multiply Part 4 by `C ≥ 0`. Used by Part 6.

**R31 · `positivity`** **closes** a goal `0 ≤ e`, `0 < e` or `e ≠ 0` when `e` is built from `+`, `*`, `/`,
`^`, `|·|`, numerals, and atoms whose sign is a hypothesis (`ha : 0 ≤ a`). It does no other reasoning.
Placeholders: `(a b x : ℝ) (ha : 0 ≤ a) (hb : 0 < b)`.

| Before | After |
|---|---|
| first line below | no goals |

```lean-goal
⊢ 0 ≤ a / (2 * b) * |x| ^ 2
```

---

## Part 6 · `newton_converges`

Statement: `C·|xₙ - r| ≤ (Cδ)^(2ⁿ)` for `xₙ = (newton f)^[n] x₀`. Induction on `n`; the step is Part 5
followed by squaring the induction hypothesis.

**R32 · `induction n`** changes the **goal list**: goal `P n` becomes `P 0` (case `zero`) and `P (n✝ + 1)`
with the hypothesis `P n✝` (case `succ`). Write `induction n with | zero => … | succ n ih => …` to name
`n✝` and the hypothesis (W3). Hypotheses mentioning `n` must be reverted first; here none do.
Placeholders: `(P : ℕ → Prop) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P n` | `⊢ P 0`, `n✝ : ℕ, a✝ : P n✝ ⊢ P (n✝ + 1)` |

**R33 · `mul_le_mul_of_nonneg_left`** changes the **context** (in a `have`) or is passed to `simpa`.
Statement: `b ≤ c → 0 ≤ a → a * b ≤ a * c`. Placeholders: `(a b c : ℝ) (hbc : b ≤ c) (ha : 0 ≤ a)`.

| Before | After `have h := mul_le_mul_of_nonneg_left hbc ha` |
|---|---|
| `hbc : b ≤ c, ha : 0 ≤ a ⊢ G` | `h : a * b ≤ a * c ⊢ G` |

**R34 · `simpa using e`** **closes** the goal: it simplifies both the goal and `e`, then uses `e`. Here
`simp` applies `Function.iterate_zero : g^[0] = id`, `id_eq`, `pow_zero : q ^ 0 = 1`, `pow_one`.
Placeholders: `(g : ℝ → ℝ) (a q : ℝ) (e : a ≤ q)`.

| Before | After |
|---|---|
| `e : a ≤ q ⊢ g^[0] a ≤ q ^ 2 ^ 0` | no goals |

**R35 · `rw [Function.iterate_succ_apply']`** changes the **goal**. Statement: `g^[n.succ] a = g (g^[n] a)`
(the last application on the outside; without `'` it is `g^[n] (g a)`). Placeholders: `(g : ℝ → ℝ) (a : ℝ)
(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (g^[n + 1] a)` | `⊢ P (g (g^[n] a))` |

**R36 · `rw [pow_succ]`** changes the **goal**. `pow_succ : a ^ (n + 1) = a ^ n * a`. It rewrites the first
`_ ^ (_ + 1)`; in `q ^ 2 ^ (n + 1)` that is the exponent `2 ^ (n + 1)`. Placeholders: `(q : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (q ^ 2 ^ (n + 1))` | `⊢ P (q ^ (2 ^ n * 2))` |

**R37 · `rw [pow_mul]`** changes the **goal**. `pow_mul : a ^ (m * n) = (a ^ m) ^ n`. Placeholders as in R36.

| Before | After |
|---|---|
| `⊢ P (q ^ (2 ^ n * 2))` | `⊢ P ((q ^ 2 ^ n) ^ 2)` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: degree-0 Taylor (the mean value theorem).** R4 with `(n := 0)` and `ContDiff ℝ 1 g`, then R14, R15,
R16. After `refine ⟨ξ, ?_⟩`, R14 and R15:

```lean-goal
⊢ g b = g a + deriv g ξ * (b - a)
```

and `hξ : g b - g a = deriv g ξ * (b - a)`, so `linear_combination hξ` closes it.

**W2: a quotient's absolute value.** `rw [abs_div, abs_mul, abs_pow, div_le_iff₀ hc]` (R23, R24, R26, R28):

```lean-goal
⊢ |a * b ^ 3 / c| ≤ 5
⊢ |a| * |b| ^ 3 ≤ 5 * |c|
```

**W3: squaring doubles the exponent.** A sequence with `e (n + 1) ≤ e n ^ 2`, `e 0 ≤ q`, `0 ≤ e n` gives
`e n ≤ q ^ 2 ^ n`: `induction n with` (R32), `zero` by `simpa using h0` (R34), `succ` by R36, R37, then a
two-step `calc` (R29) whose second step is `gcongr` (R30) with `this : 0 ≤ e n` in context.

```lean-goal
⊢ e n ≤ q ^ 2 ^ n
```

---

## Traps

- **Order in `taylor1`:** rewrite the coefficient `iteratedDerivWithin 1 f (uIcc x y) x` to `deriv f x`
  (your `d1`, from R11 and R12) **before** `norm_num at hξ`. `norm_num` first turns it into
  `derivWithin f (uIcc x y) x`, and R11 no longer matches. `rw [d1] at hξ` works even though `hξ` shows
  `iteratedDerivWithin (0 + 1)`: `0 + 1` and `1` are the same natural number to `rw`.
- Mathlib's Taylor theorem needs `x ≠ y`: handle `x = y` first (R1).
- `UniqueDiffOn ℝ (Icc a b)` needs `a < b` strictly, and `uIcc x y` is `Icc x y` or `Icc y x` depending on
  the order: split with R5 and use R6 or R7.
- `div_le_iff₀` and `abs_pos` need `0 < |deriv f x|`; derive it once (`hm.trans_le hd`, R21) and reuse it.
- `gcongr` and `positivity` need `0 ≤ M` in the context to see `0 ≤ M / (2 * m)`; prove it with
  `bound_nonneg` first. A `have` belongs to one proof only, so repeat it in each theorem that needs it.
- After `rw [e]` the goal has `(r - x)`, the statement `|x - r|`: use `abs_sub_comm r x` with arguments (R27).
- `q ^ 2 ^ n` is `q ^ (2 ^ n)`; `pow_succ` then `pow_mul` turn `q ^ 2 ^ (n + 1)` into `(q ^ 2 ^ n) ^ 2` (R36, R37).
- `Function.iterate_succ_apply'` (with `'`) puts the new step outside, where the milestone can act on it;
  `Function.iterate_succ_apply` (without) puts it inside.
- `newton` does not unfold by itself: `unfold newton` (R18) before `field_simp`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| case `x = y` / `x ≠ y` | `rcases eq_or_ne x y with rfl \| hxy` | R1 |
| kill `(x - x)` terms | `simp` (uses `sub_self`) | R2 |
| `ContDiff` → on a set / at a point | `hf.contDiffOn`, `hf.contDiffAt.of_le (by norm_num)` | R3, R9 |
| Taylor, order 1, Lagrange remainder | `obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy hf.contDiffOn` | R4 |
| case `x < y` / `y < x` | `rcases hxy.lt_or_gt with h \| h` | R5 |
| `uIcc` → `Icc` | `rw [uIcc_of_le h.le]` / `rw [uIcc_of_ge h.le]` | R6, R7 |
| `UniqueDiffOn ℝ (Icc a b)` | `uniqueDiffOn_Icc h` | R8 |
| `x ∈ uIcc x y` | `left_mem_uIcc` | R10 |
| within-derivative → `deriv` | `rw [iteratedDerivWithin_eq_iteratedDeriv hu hc hx, iteratedDeriv_one]` | R11, R12 |
| expand the Taylor polynomial | `rw [taylorWithinEval_succ, taylor_within_zero_eval] at hξ` | R13, R14 |
| tidy numerals in a hypothesis | `norm_num at hξ` | R15 |
| goal = ring combination of hypotheses | `linear_combination k * h` | R16 |
| chain equalities | `h₁.symm.trans h₂` | R17 |
| unfold a definition | `unfold newton` | R18 |
| clear denominators | `field_simp` | R19 |
| `0 ≤ \|a\|`, chain `<`/`≤` | `abs_nonneg a`, `h₁.trans h₂`, `h₁.trans_le h₂` | R20, R21 |
| `0 < \|a\|` → `a ≠ 0` | `abs_pos.mp h` | R22 |
| split `\|·\|` | `rw [abs_div, abs_mul, abs_two, abs_pow, abs_sub_comm a b]` | R23–R27 |
| `b / c ≤ a` → `b ≤ a * c` | `rw [div_le_iff₀ hc]` | R28 |
| chain of inequalities | `calc a ≤ b := … _ = c := … _ ≤ d := …` | R29 |
| compare two sides of the same shape | `gcongr` | R30 |
| `0 ≤ e` from signs | `positivity` | R31 |
| induction on `n` | `induction n with \| zero => … \| succ n ih => …` | R32 |
| multiply an inequality by `a ≥ 0` | `mul_le_mul_of_nonneg_left h ha` | R33 |
| close after simplifying | `simpa using e` | R34 |
| `g^[n+1] a` → `g (g^[n] a)` | `rw [Function.iterate_succ_apply']` | R35 |
| `q ^ 2 ^ (n+1)` → `(q ^ 2 ^ n) ^ 2` | `rw [pow_succ, pow_mul]` | R36, R37 |
| see the state | infoview | |
