# M125 · Gauss and Chebyshev nodes: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's interval integral
`∫ x in a..b, f x`, the real square root `√`, the Chebyshev polynomials `Polynomial.Chebyshev.T`,
casts `ℕ → ℤ → ℝ`, and the tactics `linear_combination`, `linarith`, `positivity`, `push_cast`,
`field_simp`, `omega`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type; `(x : ℝ)` a real number.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `∫ (x : ℝ) in a..b, f x` | the integral $\int_a^b f(x)\,dx$ (Mathlib's `intervalIntegral`); `in -1..1` is $[-1, 1]$ |
| `∀ k ≤ 3, P k` | `∀ k, k ≤ 3 → P k`; here `k : ℕ` |
| `√x` | `Real.sqrt x`, the nonnegative square root of `x : ℝ` (`√x = 0` for `x < 0`) |
| `x₁ ≠ 0` | `x₁ = 0 → False` |
| `Polynomial.Chebyshev.T ℝ n` | the Chebyshev polynomial $T_n$ with real coefficients, defined by $T_0 = 1$, $T_1 = X$, $T_{n+2} = 2X\,T_{n+1} - T_n$; its index is an integer `n : ℤ` |
| `Polynomial.eval x p` | `p.eval x`, the value $p(x)$ of the polynomial `p` at `x` |
| `Real.cos`, `Real.pi` | $\cos$ and $\pi$ on `ℝ` (printed with their full names: the file opens no namespace) |
| `↑n` | a cast: here `n : ℕ` seen as an integer or a real, depending on where it sits |
| `↑↑n` | two casts in a row, `ℕ → ℤ → ℝ`; `push_cast` turns it into the single cast `ℕ → ℝ` (R16) |
| `(↑4 + 1)` | from `integral_pow`: the exponent `4 : ℕ` cast into `ℝ`, plus one |
| `∃ k, θ = …` | the `k` is an integer, `k : ℤ` (hover over it to see the type) |
| `∃ k_1, …` | the same `∃`, renamed: Lean prints `k_1` because a `k` is already in the context |
| `case refine_1` | the name Lean gives the first `?_` of a `refine` |

---

## Part 1 · `gauss_nodes_forced`

Statement: for reals $w_1, w_2, x_1, x_2$, if $w_1 x_1^k + w_2 x_2^k = \int_{-1}^1 x^k\,dx$ for $k = 0, 1, 2, 3$,
then $x_1 + x_2 = 0$, $x_1 x_2 = -1/3$, $w_1 = 1$, $w_2 = 1$.

The math (method of moments). The four equations read $h_0: w_1 + w_2 = 2$, $h_1: w_1x_1 + w_2x_2 = 0$,
$h_2: w_1x_1^2 + w_2x_2^2 = 2/3$, $h_3: w_1x_1^3 + w_2x_2^3 = 0$. Let $s = x_1 + x_2$ and $p = x_1x_2$.
The polynomial $q(x) = x^2 - s x + p = (x - x_1)(x - x_2)$ vanishes at both nodes, so
$\sum_i w_i q(x_i) = 0$ and $\sum_i w_i x_i q(x_i) = 0$. Written in moments these are
$h_2 - s\,h_1 + p\,h_0$, i.e. $2/3 + 2p = 0$, and $h_3 - s\,h_2 + p\,h_1$, i.e. $-\tfrac23 s = 0$.
Each is one `linear_combination` (R4). Then $x_1 \ne 0$ (else $p = 0$) and $h_1$ with $x_2 = -x_1$ give
$(w_1 - w_2)x_1 = 0$, so $w_1 = w_2$, and $h_0$ finishes.

### Getting the moment equations

**R1 · `have h := hk a (by norm_num)`** changes the **context**: it adds the instance `h : P a` of a bounded
`∀`. `hk a` has type `a ≤ 3 → P a`, and `(by norm_num)` proves `a ≤ 3`. Placeholders: `(P : ℕ → Prop)
(hk : ∀ k ≤ 3, P k)`.

| Before | After |
|---|---|
| `⊢ P 2` (with `hk` in the context) | `h : P 2 ⊢ P 2` |

**R2 · `rw [integral_pow]`** changes the **goal**. The lemma is
`integral_pow : ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1)`, i.e.
$\int_a^b x^n\,dx = \frac{b^{n+1} - a^{n+1}}{n+1}$. Placeholders: `(a b : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (∫ (x : ℝ) in a..b, x ^ n)` | `⊢ P ((b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1))` |

**R3 · `norm_num [integral_pow] at h`** changes the **context**: `norm_num` rewrites `h` with R2 and then
evaluates the numbers; it also simplifies `x ^ 1` to `x`, `x ^ 0` to `1` and `w * 1` to `w`. List several
hypotheses to do them all at once: `at h0 h1 h2 h3`. Placeholders: `(w x : ℝ)`.

| Before | After |
|---|---|
| `h : w * x ^ 1 = ∫ (t : ℝ) in 0..3, t ^ 1` and `⊢ w * x = 9 / 2` | `h : w * x = 9 / 2 ⊢ w * x = 9 / 2` |

### Solving them

**R4 · `linear_combination e`** **closes** an equation `lhs = rhs`. Here `e` is a combination of hypotheses
$h_i : a_i = b_i$ with coefficients $c_i$ that may be polynomials, $e = \sum_i c_i h_i$; the tactic checks by `ring`
that $\text{lhs} - \text{rhs} = \sum_i c_i (a_i - b_i)$. Placeholders: `(a b x : ℝ)`. To find the coefficients, do
the algebra on paper (Part 1 above); `linear_combination` only checks it.

| Before | After |
|---|---|
| `h₁ : a + b = 2, h₂ : a * x + b * x = 6 ⊢ x = 3` | no goals, by `linear_combination (h₂ - x * h₁) / 2` |

**R5 · `rintro rfl`** changes the **goal and the context**. The goal `x ≠ 0` is `x = 0 → False`; `rintro rfl`
introduces the equation and substitutes it, so `x` becomes `0` in every hypothesis and the goal becomes `False`.
Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `h : x * y = 1 ⊢ x ≠ 0` | `h : 0 * y = 1 ⊢ False` |

**R6 · `norm_num at h`** **closes** the goal when `h` simplifies to `False` (here `0 * y = -1/3` becomes
`0 = -1/3`, which is false). Placeholders: `(y : ℝ)`.

| Before | After |
|---|---|
| `h : 0 * y = -1 / 3 ⊢ False` | no goals |

**R7 · `mul_eq_zero`** changes the **context** (as `have h' := mul_eq_zero.mp h`). The lemma is
`mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0`; `.mp` is the left-to-right direction of an `↔`, `.mpr` the other.
It holds in any type without zero divisors (`ℝ`, `ℤ`, `ℕ`). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : a * b = 0 ⊢ a = 0 ∨ b = 0` | `h' : a = 0 ∨ b = 0 ⊢ a = 0 ∨ b = 0` |

**R8 · `Or.resolve_right`** changes the **context**. The lemma is `Or.resolve_right : a ∨ b → ¬b → a`: if one
side is impossible, the other holds. Write it with dot notation, `h.resolve_right hb`. Placeholders:
`(A B : Prop) (h : A ∨ B) (hb : ¬B)`. Note `x ≠ 0` is `¬(x = 0)`, so it fits as `hb`.

| Before | After |
|---|---|
| `h : A ∨ B, hb : ¬B ⊢ A` | `h' : A ⊢ A` |

**R9 · `sub_eq_zero`** changes the **context**. The lemma is `sub_eq_zero : a - b = 0 ↔ a = b`; use `.mp`.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : a - b = 0 ⊢ a = b` | `h' : a = b ⊢ a = b` |

R7 → R8 → R9 chain as one term: `sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hx)` turns
`h : (a - b) * x = 0` and `hx : x ≠ 0` into `a = b`.

**R10 · `linarith`** **closes** a goal that follows from the hypotheses by adding up multiples of them
(linear arithmetic over `ℝ`, `ℚ`, `ℤ`, …: `=`, `≤`, `<`). Products of two variables count as atoms.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h₁ : a + b = 2, h₂ : a = b ⊢ a = 1` | no goals |

---

## Part 2 · `gauss_not_exact_quartic`

Statement: $\int_{-1}^1 x^4\,dx \ne (-1/\sqrt3)^4 + (1/\sqrt3)^4$. The left side is $2/5$, the right side is
$2/9$. `norm_num` cannot simplify `(1 / √3) ^ 4` by itself: it must first see `√3 ^ 2`, which R11 turns into `3`.
So: evaluate the integral (R2), reshape each power so that `√3 ^ 2` appears (R12), rewrite it (R11 with
`rw [hs]`), and finish with `norm_num`.

**R11 · `Real.sq_sqrt`** changes the **context** (as `have hs : √x ^ 2 = x := Real.sq_sqrt hx`). The lemma is
`Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x`. For a numeral, prove `0 ≤ 3` with `(by norm_num)`. Placeholders:
`(x : ℝ) (hx : 0 ≤ x)`.

| Before | After `have hs …` | After `rw [hs]` |
|---|---|---|
| `⊢ P (√x ^ 2)` | `hs : √x ^ 2 = x ⊢ P (√x ^ 2)` | `⊢ P x` |

**R12 · `rw [show a = b by ring]`** changes the **goal**: `show a = b by ring` is a proof of `a = b` written
in place, and `rw` uses it at once. The left side `a` must appear in the goal literally. Placeholders:
`(s : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((1 / s) ^ 4)` | `⊢ P (1 / (s ^ 2) ^ 2)` |

After R2 on `x ^ 4` over `[-1, 1]` the left side reads `(1 ^ (4 + 1) - (-1) ^ (4 + 1)) / (↑4 + 1)`;
`norm_num` evaluates that and decides `≠` between two numerals (W2).

---

## Part 3 · `chebyshev_node_root`

Statement: for `n k : ℕ` with `k < n`, $T_n\big(\cos\frac{(2k+1)\pi}{2n}\big) = 0$.

The math: $T_n(\cos\theta) = \cos(n\theta)$ (R13). With $\theta = \frac{(2k+1)\pi}{2n}$, $n\theta = \frac{(2k+1)\pi}{2}$,
which is a zero of $\cos$ (R14, witness $k$). The cancellation of $n$ needs $n \ne 0$ as a real number, which
follows from `k < n`.

**R13 · `rw [Polynomial.Chebyshev.T_real_cos]`** changes the **goal**. The lemma is
`T_real_cos (θ : ℝ) (n : ℤ) : (T ℝ n).eval (cos θ) = cos (n * θ)`. Because `T` takes an integer, `T ℝ m` with
`m : ℕ` is really `T ℝ ↑m`, and the factor in front of `θ` is `↑↑m` (`ℕ → ℤ → ℝ`). Placeholders:
`(θ : ℝ) (m : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Polynomial.eval (Real.cos θ) (Polynomial.Chebyshev.T ℝ ↑m))` | `⊢ P (Real.cos (↑↑m * θ))` |

**R14 · `rw [Real.cos_eq_zero_iff]`** changes the **goal**. The lemma is
`Real.cos_eq_zero_iff : cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * ↑k + 1) * π / 2`. Placeholders: `(θ : ℝ)`.

| Before | After |
|---|---|
| `⊢ Real.cos θ = 0` | `⊢ ∃ k, θ = (2 * ↑k + 1) * Real.pi / 2` |

**R15 · `refine ⟨k, ?_⟩` with `k : ℕ`** changes the **goal**: it gives the witness of an `∃ j : ℤ`. Lean casts
the natural number `k` to `ℤ` by itself, so the goal shows `↑k`; inside a real expression that becomes `↑↑k`.
Placeholders: `(k : ℕ) (P : ℤ → Prop)`.

| Before | After |
|---|---|
| `⊢ ∃ j, P j` | `⊢ P ↑k` |

**R16 · `push_cast`** changes the **goal**: it moves casts inward and merges cast chains; here it uses
`Int.cast_natCast : ((k : ℤ) : ℝ) = (k : ℝ)`. Placeholders: `(k : ℕ) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P ↑↑k` | `⊢ P ↑k` |

**R17 · `omega`** **closes** linear goals over `ℕ` and `ℤ` (with `+`, `-`, `<`, `≤`, numerals), using the
hypotheses. Placeholders: `(k n : ℕ)`.

| Before | After |
|---|---|
| `hk : k < n ⊢ 0 < n` | no goals |

**R18 · `positivity`** **closes** a goal `0 < e`, `0 ≤ e` or `e ≠ 0` by looking at the shape of `e`
(products, sums, casts, squares…); for a bare variable it looks for a hypothesis such as `h : 0 < n`. It does
not prove anything else. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `h : 0 < n ⊢ 2 * ↑n ≠ 0` | no goals |

**R19 · `field_simp`** changes or **closes** the **goal**: it multiplies out every denominator it can show
nonzero (from `≠ 0` hypotheses in the context, or numerals), then normalizes with `ring_nf`; if that leaves
nothing, the goal is closed. Put the `≠ 0` facts in the context first (with R18). Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `hx : x ≠ 0 ⊢ x * (y / (3 * x)) = y / 3` | no goals |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: the midpoint rule.** A one-point rule `w f(x)` exact for `1, x` on `[0, 2]`: after R1 twice and R3,

```lean-goal
⊢ w = 2 ∧ x = 1
```

with `h0 : w = 2` and `h1 : w * x = 2`. `refine ⟨h0, ?_⟩` leaves `⊢ x = 1`, and
`linear_combination (h1 - x * h0) / 2` closes it (R4: `x - 1 = ((w x - 2) - x (w - 2)) / 2`).

**W2: non-exactness.** `∫ t in (0:ℝ)..2, t ^ 2 ≠ 2 * 1 ^ 2` after R2:

```lean-goal
⊢ (2 ^ (2 + 1) - 0 ^ (2 + 1)) / (↑2 + 1) ≠ 2 * 1 ^ 2
```

and `norm_num` closes it ($8/3 \ne 2$).

**W3: a cast chain and a squared denominator.** With `hm : ↑m ≠ 0` from R18, R16 merges the casts and
R19 then closes the goal:

```lean-goal
⊢ ↑↑m * (x / ↑m ^ 2) = x / ↑m
⊢ ↑m * (x / ↑m ^ 2) = x / ↑m
```

---

## Traps

- `Polynomial.Chebyshev.T` is indexed by `ℤ`, so `T ℝ n` with `n : ℕ` carries a cast and the goal shows `↑↑n`
  (`ℕ → ℤ → ℝ`) next to plain `↑n`. `field_simp` does not see that `↑↑n` and `↑n` are the same: run
  `push_cast` (R16) first.
- `field_simp` needs `(n : ℝ) ≠ 0` **in the context**; it does not know `k < n`. Prove `0 < n` with `omega`
  (R17), then `(n : ℝ) ≠ 0` with `positivity` (R18), both inside a `have`.
- `hexact 0` alone has type `0 ≤ 3 → …`; pass the proof `(by norm_num)` to get the equation (R1).
- After `norm_num … at h0 h1 h2 h3` the hypotheses are restated (`x₁ ^ 1` is gone). Write later steps against
  the new forms shown in the infoview.
- `linear_combination` checks the coefficients, it does not find them. Get them on paper first (Part 1).
- `rw [show a = b by ring]` fails if `a` is not literally in the goal: `(-1 / √3) ^ 4` and `(1 / √3) ^ 4` need
  one `show` each.
- `√3 ^ 2` and `√3 * √3` are different text for `rw`; `Real.sq_sqrt` is the `^ 2` form.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| instance of `∀ k ≤ 3, P k` | `have h := hk 2 (by norm_num)` | R1 |
| evaluate $\int_a^b x^n$ in the goal | `rw [integral_pow]` | R2 |
| evaluate it in hypotheses | `norm_num [integral_pow] at h0 h1` | R3 |
| equation from a weighted sum of equations | `linear_combination c₁ * h₁ + c₂ * h₂` | R4 |
| prove `x ≠ 0` by substituting `x = 0` | `rintro rfl` | R5 |
| hypothesis is numerically false | `norm_num at h` | R6 |
| `a * b = 0` → cases | `mul_eq_zero.mp h` | R7 |
| drop the impossible side of `A ∨ B` | `h.resolve_right hb` | R8 |
| `a - b = 0` → `a = b` | `sub_eq_zero.mp h` | R9 |
| linear consequence of hypotheses | `linarith` | R10 |
| `√x ^ 2 = x` | `Real.sq_sqrt (by norm_num)` | R11 |
| reshape a subterm in place | `rw [show a = b by ring]` | R12 |
| split goal, some parts known | `refine ⟨hs, hp, ?_, ?_⟩` | TACTIC_STATES |
| $T_n(\cos\theta) = \cos(n\theta)$ | `rw [Polynomial.Chebyshev.T_real_cos]` | R13 |
| $\cos\theta = 0$ ↔ odd multiple of $\pi/2$ | `rw [Real.cos_eq_zero_iff]` | R14 |
| natural witness for `∃ j : ℤ` | `refine ⟨k, ?_⟩` | R15 |
| `↑↑k` → `↑k` | `push_cast` | R16 |
| linear `ℕ`/`ℤ` facts | `omega` | R17 |
| `(n : ℝ) ≠ 0` from `0 < n` | `positivity` | R18 |
| clear denominators | `field_simp` | R19 |
| numeric `≠` | `norm_num` | TACTIC_STATES |
| see the state | infoview | |
