# H038 · Division with remainder in ℤ[i]: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `have`, `exact`, `rw`, `simp`, `ring`, `∃`, `∧`,
`refine ⟨x, ?_⟩`, `·` focusing. **New here:** Mathlib's `Zsqrtd d` (the ring `ℤ√d`) and `GaussianInt`, the
norm `Zsqrtd.norm`, the conjugate `star`, integer `/` and `%` on `ℤ`, absolute value `|x|`, and the tactics
`by_cases`, `push Not`, `obtain`, `by_contra`, `linarith`, `nlinarith`.

The math. A Gaussian integer is $z = x + y\,i$ with $x, y \in \mathbb{Z}$. Its conjugate is
$\bar z = x - y\,i$ and its norm is $N(z) = z \bar z = x^2 + y^2 \in \mathbb{Z}$; the norm is multiplicative,
$N(zw) = N(z)N(w)$, and $N(\bar z) = N(z)$. Given $a, b$ with $b \ne 0$, put $N = N(b) > 0$ and
$w = a\bar b$, so that $a / b = w / N$ in $\mathbb{C}$. Round each coordinate: pick $s, t \in \mathbb{Z}$ with
$2|w_{re} - Ns| \le N$ and $2|w_{im} - Nt| \le N$ (`round_int`), and set $q = s + t\,i$, $r = a - bq$. Then
$r\bar b = w - Nq$ (`mul_conj_sub`), so
$N(r)\,N = N(r \bar b) = (w_{re} - Ns)^2 + (w_{im} - Nt)^2 \le N^2/4 + N^2/4$ (`norm_mul_norm`), hence
$N(r) \le N/2 < N$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves alone.
- Placeholders are written as Lean binders. `{d : ℤ}` is any integer `d`, and `x : ℤ√d` an element of
  `ℤ√d`; with `d := -1` that is `GaussianInt`, so every `ℤ√d` entry applies to the exercise.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℤ√d` | `Zsqrtd d`: numbers `re + im·√d` with `re im : ℤ`; a structure with fields `.re`, `.im` |
| `GaussianInt` | `ℤ√(-1)`, i.e. `ℤ[i]`; a reducible abbreviation, so all `Zsqrtd` lemmas apply |
| `⟨s, t⟩`, printed `{ re := s, im := t }` | the element `s + t·i` (anonymous constructor) |
| `x.re`, `x.im` | the integer coordinates of `x` |
| `star x` | the conjugate `x.re - x.im·√d` (for `GaussianInt`: `re - im·i`) |
| `x.norm`, printed `Zsqrtd.norm x` on a `GaussianInt` (but `(star x).norm` keeps the dot form) | the norm `re² - d·im²` (for `GaussianInt`: `re² + im²`), an integer |
| `-1 * x.im * x.im` | the `- d * im * im` term of the norm with `d = -1`, before simplification |
| `↑n` with `n : ℤ`, goal in `ℤ√d` | the integer `n` cast into `ℤ√d`, i.e. `⟨n, 0⟩` |
| `↑x.norm`, printed `↑(Zsqrtd.norm x)` on a `GaussianInt` | the norm (an integer) cast back into `ℤ√d` (R10) |
| `a / b`, `a % b` on `ℤ` | Euclidean quotient and remainder: `a % b + b * (a / b) = a` and, for `b ≠ 0`, `0 ≤ a % b < |b|` |
| `\|x\|` | absolute value `max x (-x)` |
| `case pos`, `case neg` | the two branches made by `by_cases`: hypothesis true, hypothesis false |
| `hn.ne'` | from `hn : 0 < n`, the fact `n ≠ 0` (`LT.lt.ne'`; plain `hn.ne` is `0 ≠ n`) |

---

## Part 1 · `round_int` (milestone)

Statement: for `0 < n`, every integer `u` has an `s` with `2 * |u - n * s| ≤ n`: `u` is within `n / 2` of a
multiple of `n`. Take `s = u / n` when the remainder `u % n` is at most `n / 2`, else `s = u / n + 1`.

### Facts about `/` and `%`

**R1 · `have h := Int.emod_nonneg a hb.ne'`** changes the **context**. The lemma is
`Int.emod_nonneg : b ≠ 0 → 0 ≤ a % b`. Placeholders: `(a b : ℤ) (hb : 0 < b)`.

| Before | After |
|---|---|
| `⊢ G` | `h : 0 ≤ a % b ⊢ G` |

**R2 · `have h := Int.emod_lt_of_pos a hb`** changes the **context**. The lemma is
`Int.emod_lt_of_pos : 0 < b → a % b < b`. Placeholders: `(a b : ℤ) (hb : 0 < b)`.

| Before | After |
|---|---|
| `⊢ G` | `h : a % b < b ⊢ G` |

**R3 · `have h := Int.emod_add_mul_ediv a b`** changes the **context**. The lemma is
`Int.emod_add_mul_ediv : a % b + b * (a / b) = a`, with no hypothesis. It is the only link between `/` and `%`
that `linarith` needs. Placeholders: `(a b : ℤ)`.

| Before | After |
|---|---|
| `⊢ G` | `h : a % b + b * (a / b) = a ⊢ G` |

### Case split and linear arithmetic

**R4 · `by_cases h : p`** changes the **goal list and the context**: one goal becomes two, `case pos` with
`h : p` and `case neg` with `h : ¬p`. Placeholders: `(p G : Prop)`. Prove each with a `·` block.

| Before | After |
|---|---|
| `⊢ G` | `h : p ⊢ G`, `h : ¬p ⊢ G` |

**R5 · `linarith`** **closes** a goal `t ≤ t'`, `t < t'` or `t = t'` that follows from the hypotheses by adding
them with nonnegative coefficients. It treats every product of two non-numerals, such as `n * (u / n)`, as one
unknown, and it reads `¬a ≤ b` as `b < a` by itself. Placeholders: `(a b c : ℤ)`.

| Before | After |
|---|---|
| `h1 : a + b = c, h2 : 0 ≤ b ⊢ a ≤ c` | closed |

**R6 · `rw [show e₁ = e₂ by linarith]`** changes the **goal**: `show T by tac` is a term proving `T`, so this
rewrites with an equation you state and prove in place. Use it to turn `u - n * (u / n)` into `u % n` with R3
in the context. Placeholders: `(x y z : ℤ) (h : x + y = z)`.

| Before | After |
|---|---|
| `⊢ P (z - x)` | `⊢ P y` |

### Absolute value

**R7 · `rw [abs_of_nonneg hx]`** changes the **goal**. The lemma is `abs_of_nonneg : 0 ≤ x → |x| = x`
(any ordered additive group; `ℤ`, `ℚ`, `ℝ` qualify). Placeholders: `(x : ℤ) (hx : 0 ≤ x)`.

Before, then after (in a block, because `|` cannot sit inside a table cell):

```lean-goal
⊢ P |x|
⊢ P x
```

**R8 · `push Not at h`** changes the **context**: it pushes `¬` inward, so `¬a ≤ b` becomes `b < a` (and
`¬∀` becomes `∃ ¬`, and so on). Without `at h` it acts on the goal. Placeholders: `(a b : ℤ)`.

| Before | After |
|---|---|
| `h : ¬a ≤ b ⊢ G` | `h : b < a ⊢ G` |

**R9 · `rw [abs_of_neg hx]`** changes the **goal**. The lemma is `abs_of_neg : x < 0 → |x| = -x`. In the
exercise the hypothesis is proved inline: `abs_of_neg (by linarith)`. Placeholders: `(x : ℤ) (hx : x < 0)`.

```lean-goal
⊢ P |x|
⊢ P (-x)
```

---

## Part 2 · `mul_conj_sub` (milestone)

Statement: `(a - b * q) * star b = a * star b - ↑b.norm * q`, i.e. $r\bar b = a\bar b - N(b)\,q$. The cast
`↑b.norm` is the only thing `ring` cannot see through.

**R10 · `rw [Zsqrtd.norm_eq_mul_conj]`** changes the **goal**. The lemma is
`Zsqrtd.norm_eq_mul_conj : ↑x.norm = x * star x` (the norm cast into `ℤ√d`). Placeholders:
`{d : ℤ} (x : ℤ√d)`.

| Before | After |
|---|---|
| `⊢ P ↑x.norm` | `⊢ P (x * star x)` |

**R11 · `ring`** **closes** an identity of commutative rings. `ℤ√d` is one, and `ring` treats `star x`, `x.re`,
`↑n` as unknowns. It also closes the final integer identity of Part 3. Placeholders: `{d : ℤ} (x y z : ℤ√d)`.

| Before | After |
|---|---|
| `⊢ (x - y) * star z = x * star z - y * star z` | closed |

---

## Part 3 · `norm_mul_norm` (milestone, uses `mul_conj_sub`)

Statement: `(a - b * ⟨s, t⟩).norm * b.norm = ((a * star b).re - b.norm * s) ^ 2 + ((a * star b).im - b.norm * t) ^ 2`,
i.e. $N(r)\,N(b) = N(r\bar b)$ written in coordinates. Plan: make the left side one norm (R12, R13), rewrite its
argument with `mul_conj_sub`, expand the norm (R14), compute coordinates (R15), finish with R11.

**R12 · `rw [← Zsqrtd.norm_conj x]`** changes the **goal**. The lemma is `Zsqrtd.norm_conj : (star x).norm = x.norm`;
right to left it replaces **every** `x.norm` in the goal by `(star x).norm`, the right-hand side included.
Placeholders: `{d : ℤ} (x : ℤ√d)`.

| Before | After |
|---|---|
| `⊢ P x.norm` | `⊢ P (star x).norm` |

**R13 · `rw [← Zsqrtd.norm_mul]`** changes the **goal**. The lemma is `Zsqrtd.norm_mul : (x * y).norm = x.norm * y.norm`;
right to left it merges a product of norms into one norm. Placeholders: `{d : ℤ} (x y : ℤ√d)`.

| Before | After |
|---|---|
| `⊢ P (x.norm * y.norm)` | `⊢ P (x * y).norm` |

**R14 · `rw [Zsqrtd.norm_def]`** changes the **goal**. The lemma is
`Zsqrtd.norm_def : x.norm = x.re * x.re - d * x.im * x.im`; with `d = -1` the term prints as `- -1 * …`.
Placeholders: `(x : GaussianInt)`.

| Before | After |
|---|---|
| `⊢ P (Zsqrtd.norm x)` | `⊢ P (x.re * x.re - -1 * x.im * x.im)` |

**R15 · `simp`** changes the **goal**: it computes `.re` and `.im` of sums, differences, products, `star`,
casts `↑n` and literals `⟨s, t⟩`, and cleans up `-1 *`. Lemmas it uses: `Zsqrtd.re_sub`, `Zsqrtd.re_mul`
(`(z * w).re = z.re * w.re + d * z.im * w.im`), `Zsqrtd.im_mul` (`(z * w).im = z.re * w.im + z.im * w.re`),
`Zsqrtd.re_star`, `Zsqrtd.im_star` (`(star z).im = -z.im`), `Zsqrtd.smul_val`, and it turns `(star b).norm`
back into `b.norm`. Placeholders: `(x y : GaussianInt) (n s t : ℤ)`.

| Before | After |
|---|---|
| `⊢ P (x * star y - ↑n * { re := s, im := t }).re` | `⊢ P (x.re * y.re + x.im * y.im - n * s)` |

After R15 in the exercise the two sides differ only by `u * u` versus `u ^ 2` and sign rearrangements: R11.

**W2 · a norm in `ℤ√2` by coordinates (R14 then R15).** `simp` closes the second line:

```lean-goal
⊢ { re := 3, im := 2 }.norm = 1
⊢ { re := 3, im := 2 }.re * { re := 3, im := 2 }.re - 2 * { re := 3, im := 2 }.im * { re := 3, im := 2 }.im = 1
```

**W3 · the same lemmas left to right in `ℤ√2`.** `rw [Zsqrtd.norm_mul]` then `rw [Zsqrtd.norm_conj]`
(the last `rw` closes the goal by `rfl`):

```lean-goal
⊢ (x * star y).norm = x.norm * y.norm
⊢ x.norm * (star y).norm = x.norm * y.norm
```

---

## Part 4 · `div_mod`

Statement: for `b ≠ 0` there are `q r : GaussianInt` with `a = b * q + r` and `r.norm < b.norm`. Prove the
three milestones first: `round_int` (applied twice, to the coordinates of `a * star b`), `norm_mul_norm`
(the key identity), which itself uses `mul_conj_sub`.

**R16 · `GaussianInt.norm_pos`** is the lemma `0 < x.norm ↔ x ≠ 0`; `.mpr` is its right-to-left direction.
`have h : 0 < x.norm := GaussianInt.norm_pos.mpr hx` changes the **context**. Placeholders:
`(x : GaussianInt) (hx : x ≠ 0)`.

| Before | After |
|---|---|
| `⊢ G` | `h : 0 < Zsqrtd.norm x ⊢ G` |

**R17 · `obtain ⟨s, hs⟩ := e`** changes the **context**: `e : ∃ s, Q s` is replaced by a witness and its
property. Here `e` is `round_int N u hN`. Placeholders: `(Q : ℤ → Prop) (e : ∃ s, Q s)`.

| Before | After |
|---|---|
| `⊢ G` | `s : ℤ, hs : Q s ⊢ G` |

**R18 · `refine ⟨w₁, w₂, by ring, ?_⟩`** changes the **goal**: `∃ q r, A ∧ B` nests as `∃ q, ∃ r, A ∧ B`, so one
flat pattern fills both witnesses, proves `A` on the spot and leaves `B`. A Gaussian-integer witness is written
`⟨s, t⟩`. Placeholders: `(s t : ℤ) (n : GaussianInt) (P : GaussianInt → GaussianInt → Prop)`.

| Before | After |
|---|---|
| `⊢ ∃ q r, n = q + r ∧ P q r` | `⊢ P { re := s, im := t } (n - { re := s, im := t })` |

### Squares and nonlinear arithmetic

**R19 · `sq_abs x`** is `|x| ^ 2 = x ^ 2`; `have h := sq_abs x` changes the **context**. Placeholders: `(x : ℤ)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, context gains `h : \|x\| ^ 2 = x ^ 2` |

**R20 · `abs_nonneg x`** is `0 ≤ |x|`; `have h := abs_nonneg x` changes the **context**. Placeholders: `(x : ℤ)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, context gains `h : 0 ≤ \|x\|` |

**R21 · `nlinarith [f₁, f₂]`** **closes** a polynomial (in)equality: it adds the products of pairs of hypotheses
and of the listed facts `fᵢ`, then runs `linarith`. It does not know anything about `|·|`: pass R19 and R20 for
the term you square. Placeholders: `(x y : ℤ)`.

| Before | After |
|---|---|
| `h1 : 0 ≤ x, h2 : x ≤ y ⊢ x * x ≤ y * y` | closed |

**R22 · `by_contra h`** changes the **goal and the context**: the goal `G` becomes `False` with `h : ¬G`.
Follow it with R8 to turn `¬(x < y)` into `y ≤ x`. Placeholders: `(G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h : ¬G ⊢ False` |

**W1 · from a bound on `|x|` to a bound on `x ^ 2` (R19, R20, R21).** With `h : 3 * |x| ≤ 6`,
`nlinarith [sq_abs x, abs_nonneg x]` closes `x ^ 2 ≤ 4`: it multiplies `6 - 3|x| ≥ 0` by `|x| ≥ 0` and by itself.

**W4 · strict `<` by contradiction (R22, R8, R21).** With `hn : 0 < n` and `h : x * n < n * n`:

```lean-goal
⊢ x < n
⊢ False
```

| Before | After |
|---|---|
| `hx : ¬x < n ⊢ False` | `hx : n ≤ x ⊢ False` |

and `nlinarith` closes it (it multiplies `n ≤ x` by `0 < n`).

---

## Traps

- `GaussianInt` already has `/` and `%` (Mathlib makes it a Euclidean domain), but all their lemmas are banned:
  build `q` yourself as `⟨s, t⟩`. Never write `a / b` with `a b : GaussianInt`.
- `rw [← Zsqrtd.norm_conj b]` (R12) rewrites **every** `b.norm`, so the right-hand side shows `(star b).norm`
  until `simp` (R15) turns it back. Do R12 before R13: R13 needs the pattern `_.norm * _.norm`.
- `b.norm` and `Zsqrtd.norm b` are the same term; Lean prints the second for a `GaussianInt`. `⟨s, t⟩` prints as
  `{ re := s, im := t }`. Write the short forms in your own `have`s.
- `Int.emod_nonneg` wants `b ≠ 0`, not `0 < b`: pass `hn.ne'`. `hn.ne` is `0 ≠ n`, the wrong way round.
- `linarith` sees `n * (u / n)` as one atom: give it `Int.emod_add_mul_ediv` (R3) as a hypothesis and state the
  rewrite with `show … by linarith` (R6), with `n * (u / n)` written exactly as in the goal.
- `nlinarith` cannot go from `2 * |e| ≤ N` to `4 * e ^ 2 ≤ N ^ 2` alone: list `sq_abs e` and `abs_nonneg e`
  with the same `e` (R19–R21). Prove the two square bounds as separate `have`s before the final `nlinarith`.
- `t1 ; t2` after `by_cases` runs `t2` on the first branch only; use one `·` block per branch.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `0 ≤ u % n`, `u % n < n`, `u % n + n * (u / n) = u` | `Int.emod_nonneg u hn.ne'`, `Int.emod_lt_of_pos u hn`, `Int.emod_add_mul_ediv u n` | R1–R3 |
| split on a proposition | `by_cases h : p` | R4 |
| linear arithmetic from hypotheses | `linarith` | R5 |
| rewrite with an ad-hoc equation | `rw [show e₁ = e₂ by linarith]` | R6 |
| drop `\|·\|` | `rw [abs_of_nonneg h]` / `rw [abs_of_neg (by linarith)]` | R7, R9 |
| `¬a ≤ b → b < a` | `push Not at h` | R8 |
| `↑x.norm → x * star x` | `rw [Zsqrtd.norm_eq_mul_conj]` | R10 |
| ring identity in `ℤ√d` or `ℤ` | `ring` | R11 |
| `N(r) * N(b) → N(r * star b)` | `rw [← Zsqrtd.norm_conj b, ← Zsqrtd.norm_mul]` | R12, R13 |
| norm → coordinates | `rw [Zsqrtd.norm_def]; simp` | R14, R15 |
| `b ≠ 0 → 0 < b.norm` | `GaussianInt.norm_pos.mpr hb` | R16 |
| unpack `∃` | `obtain ⟨s, hs⟩ := round_int …` | R17 |
| give `q`, `r`, prove `a = b * q + r` | `refine ⟨⟨s, t⟩, a - b * ⟨s, t⟩, by ring, ?_⟩` | R18 |
| `2 * \|e\| ≤ N → 4 * e ^ 2 ≤ N ^ 2` | `nlinarith [sq_abs e, abs_nonneg e]` | R19–R21 |
| prove `<` by contradiction | `by_contra h; push Not at h; nlinarith` | R22, R8, R21 |
| see the state | infoview | |
