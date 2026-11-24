# M118 · Euler's method on y' = λy: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`rw [h]`, `constructor`, `<;>`, `have`, `ring`, `norm_num`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def` by pattern matching on `ℕ`, `rw`, `simp`,
`have`, `exact`, `constructor`. **New here:** Mathlib's real numbers `ℝ`, `Real.exp`, absolute value
`|·|`, the monotonicity tactic `gcongr`, the arithmetic deciders `linarith` / `nlinarith`, `calc` chains,
and limits written with `Filter.Tendsto … atTop atTop`.

The mathematics. Forward Euler with step size `h` on `y' = λy` is the recursion
`y₀`, `yₙ₊₁ = yₙ + h·(λ yₙ)` (`euler lam h y₀ n` is `yₙ`). Each step multiplies by the
*amplification factor* `1 + hλ`, so `yₙ = (1 + hλ)ⁿ y₀`. All four theorems are statements about that factor:
`1 + hλ ≤ e^(hλ)` (Part 2), `|1 + hλ| ≤ 1` when `-2 ≤ hλ ≤ 0` (Part 3), `|1 + hλ| > 1` when `hλ < -2` (Part 4).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{M : Type}` is any type. A bracket such as `[Monoid M]` is a
  requirement on `M` (a *type class*): here, `M` has an associative `*` with unit `1`; `ℕ`, `ℝ`, `ℂ` and
  square matrices qualify. Most entries are stated directly on `ℝ`, the only type the exercise uses.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- A Markdown table cell cannot hold a literal `|`, so a state with an absolute value `|a|` is repeated below
  its table in a plain block, exactly as the infoview prints it.

## Reading the goals

| You see | It means |
|---|---|
| `lam` | the rate λ. `λ` is reserved in Lean (it is `fun`), so the exercise writes `lam` |
| `y₀` | the initial value, an ordinary name (`y₀` is typed `y\0`) |
| `h` | the step size, a real number. It is not a hypothesis; the hypotheses are `hl`, `hh`, `hy`, `hstab` |
| `h * -lam` | `h * (-lam)`: Lean prints unary minus without parentheses |
| `euler lam h y₀ n` | the n-th Euler iterate `yₙ` |
| `↑n` | the natural number `n : ℕ` cast into `ℝ`. `n * h` with `n : ℕ`, `h : ℝ` is elaborated as `↑n * h` |
| `Real.exp x` | `eˣ` on the reals |
| `\|a\|` | absolute value of `a` (typed `\|a\|` with the bar key) |
| `x ^ n` | power with natural exponent `n : ℕ` |
| `case zero`, `case succ` | the two goals after `induction n` |
| `case hab`, `case hbc`, `case ha` | goal names `gcongr` and `calc` give to their subgoals; they do not matter |
| `ih : P n` | the induction hypothesis in the `succ` case |
| `fun n => u n` | the sequence `n ↦ u n`; `rw` cannot rewrite inside it (R19) |
| `Tendsto u atTop atTop` | `u n → ∞` as `n → ∞`: for every bound `B`, eventually `u n ≥ B`. `atTop` is the filter of "large values" (`Filter.atTop`; the file has `open Filter`) |
| `inst✝ : Monoid M` | an anonymous type-class hypothesis, from a `[Monoid M]` binder |

---

## Part 1 · `euler_closed_form`

Statement: `euler lam h y₀ n = (1 + h * lam) ^ n * y₀` for every `n : ℕ`. Prove it by induction; every later
part uses it.

**R1 · `induction n with | zero => ?_ | succ n ih => ?_`** changes the **goal list and the context**: `P n`
becomes two goals, `P 0` and `P (n + 1)`, and the second has the induction hypothesis `ih : P n`.
Placeholders: `(P : ℕ → Prop) (n : ℕ)`. Writing `?_` after each `=>` leaves both goals open, to be proved
with `·` bullets. The multi-line form

```
induction n with
| zero => tac₀
| succ n ih => tac₁
```

is the same thing with the proofs written in place.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `n : ℕ, ih : P n ⊢ P (n + 1)` |

**R2 · `simp only [d]`** changes the **goal**: on `d … 0` it applies the `| 0 => …` equation of the recursive
`def d`. Placeholders: `dbl` from guide.lean (`dbl x₀ 0 = x₀`). `simp [d]` (without `only`) also cleans up
`a ^ 0 = 1` and `1 * a = a` and closes the base case outright.

| Before | After |
|---|---|
| `⊢ P (dbl x₀ 0)` | `⊢ P x₀` |

**R3 · `rw [d]`** changes the **goal**: on `d … (n + 1)` it applies the `| n + 1 => …` equation once, so the
goal speaks about `d … n`, which `ih` covers. Then `rw [ih]`. Placeholders: `(x₀ : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (dbl x₀ (n + 1))` | `⊢ P (dbl x₀ n + dbl x₀ n)` |

**R4 · `rw [pow_succ]`** changes the **goal**. The lemma is `pow_succ : a ^ (n + 1) = a ^ n * a`.
Placeholders: `{M : Type} [Monoid M] (a : M) (n : ℕ)`; `ℝ` qualifies. After it the step goal is a pure ring
identity: finish with `ring`.

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

**W1** (guide.lean) is the whole pattern on `dbl x₀ n = 2 ^ n * x₀`: R1, then `simp [dbl]` for the base and
`rw [dbl, ih, pow_succ]; ring` for the step.

---

## Part 2 · `euler_le_exact`

Statement: for `λ ≥ 0`, `h ≥ 0`, `y₀ ≥ 0`: `euler lam h y₀ n ≤ Real.exp (lam * (↑n * h)) * y₀`, i.e.
`(1 + hλ)ⁿ y₀ ≤ e^(λ·nh) y₀`. Euler underestimates the growing exact solution.

**R5 · `rw [thm]`** with a theorem `thm : ∀ n, f n = g n` changes the **goal**. `rw` finds the arguments
itself, so `rw [euler_closed_form]` works without naming `lam h y₀ n`. A theorem proved earlier in the file is
used exactly like a library lemma. Placeholders: `(f g : ℕ → ℝ) (thm : ∀ n, f n = g n)`.

| Before | After |
|---|---|
| `⊢ P (f n)` | `⊢ P (g n)` |

**R6 · `gcongr`** ("generalized congruence") changes the **goal**. It compares the two sides of `≤`, finds the
part that differs, and reduces the goal to an inequality between those parts, using monotonicity lemmas such
as `a ≤ b → 0 ≤ c → a * c ≤ b * c`. *Side goals* such as `0 ≤ c` are discharged by `positivity`, which may
use hypotheses `0 ≤ x` of the context; a side goal it cannot prove is left to you. A main goal that is
literally a hypothesis is closed by assumption. Placeholders: `(a c : ℝ) (hc : 0 ≤ c)`; `f a` is "the other
side".

| Before | After |
|---|---|
| `⊢ a * c ≤ f a * c` | `⊢ a ≤ f a` |

In Part 2, after `rw [euler_closed_form]` and `gcongr` (side goal `0 ≤ y₀` closed from `hy`), the goal is
`(1 + h * lam) ^ n ≤ Real.exp (lam * (↑n * h))`: the left side of your `calc` (R7) must be `(1 + h * lam) ^ n`
and its last right side `Real.exp (lam * (n * h))`.

**R7 · `calc`** **closes** a goal `a ≤ c` by a chain of steps, each with its own proof:

```
calc a ≤ b := proof₁
  _ = c := proof₂
```

`_` stands for the previous right-hand side. Mixing `≤` and `=` gives `≤`. Write `:= by` and indented
tactics for a longer step proof. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | (closed) |

**R8 · `gcongr`** on powers changes the **goal**: `a ^ n ≤ b ^ n` becomes `a ≤ b`, with side goal `0 ≤ a`
(left to you if `positivity` cannot prove it from the context). In Part 2 the side goal `0 ≤ 1 + h * lam` is
proved from `hl` and `hh` automatically. Placeholders: `(a : ℝ) (n : ℕ) (ha : 0 ≤ a)`.

| Before | After |
|---|---|
| `⊢ a ^ n ≤ f a ^ n` | `⊢ a ≤ f a` |

**R9 · `Real.add_one_le_exp`** changes the **context** when added with `have` (or is passed to `linarith`,
R10). The lemma is `Real.add_one_le_exp : ∀ x : ℝ, x + 1 ≤ Real.exp x`, the tangent-line bound `1 + x ≤ eˣ`.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P` | `h : x + 1 ≤ Real.exp x ⊢ P` |

**R10 · `linarith [t₁, t₂]`** **closes** a goal `≤`, `<`, `=` (or `False`) that follows from the hypotheses and
the extra facts `tᵢ` by adding them with nonnegative coefficients. It treats every nonlinear subterm
(`h * lam`, `Real.exp x`) as an opaque atom. Placeholders: `(x y : ℝ) (hf : ∀ z, z + 1 ≤ f z)`.

| Before | After |
|---|---|
| `hxy : y ≤ x ⊢ y + 1 ≤ f x` | (closed by `linarith [hf x]`) |

**R11 · `rw [← Real.exp_nat_mul]`** changes the **goal**. The lemma is
`Real.exp_nat_mul : ∀ (x : ℝ) (n : ℕ), Real.exp (↑n * x) = Real.exp x ^ n`, i.e. `(eˣ)ⁿ = e^(nx)`; `←` uses it
right to left. Placeholders: `(x : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Real.exp x ^ n)` | `⊢ P (Real.exp (↑n * x))` |

**R12 · `ring_nf`** **closes** `f s = f t` when `s` and `t` are equal as commutative-ring expressions: it puts
every subterm, including the arguments of `f`, in a normal form, and then both sides are the same. `ring`
alone works only when the two sides are ring expressions at top level. In Part 2 it turns
`Real.exp (↑n * (h * lam)) = Real.exp (lam * (↑n * h))` into a triviality. Placeholders: `(a b c : ℝ)
(f : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ f (a * (b * c)) = f (c * (b * a))` | (closed) |

**W2** (guide.lean) chains R7, R8, R10 + R9, R11, R12 on `(1 + x/2)ⁿ ≤ e^(nx/2)`.

---

## Part 3 · `euler_stable`

Statement: for `λ ≤ 0`, `h ≥ 0`, `h·(-λ) ≤ 2`: `|euler lam h y₀ n| ≤ |y₀|`. The condition says
`-2 ≤ hλ ≤ 0`, so `|1 + hλ| ≤ 1`, and multiplying by it never increases `|y|`.

**R13 · `rw [abs_mul]`** changes the **goal**. The lemma is `abs_mul : |a * b| = |a| * |b|`. Placeholders:
`(a b : ℝ)` (any linearly ordered ring).

| Before | After |
|---|---|
| <code>⊢ P &#124;a * b&#124;</code> | <code>⊢ P (&#124;a&#124; * &#124;b&#124;)</code> |

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R14 · `rw [abs_pow]`** changes the **goal**. The lemma is `abs_pow : |a ^ n| = |a| ^ n`. Placeholders:
`(a : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| <code>⊢ P &#124;a ^ n&#124;</code> | <code>⊢ P (&#124;a&#124; ^ n)</code> |

```lean-goal
⊢ P |a ^ n|
⊢ P (|a| ^ n)
```

**R15 · `rw [abs_le]`** changes the **goal**: an absolute-value bound becomes two linear bounds. The lemma is
`abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b`; `rw` with an `↔` replaces the left side by the right. Follow with
`constructor` (TACTIC_STATES) to get the two goals. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| <code>⊢ &#124;a&#124; ≤ b</code> | <code>⊢ -b ≤ a ∧ a ≤ b</code> |

```lean-goal
⊢ |a| ≤ b
⊢ -b ≤ a ∧ a ≤ b
```

**R16 · `nlinarith`** **closes** goals that need *products* of hypotheses: it multiplies pairs of hypotheses
(and squares) and then runs `linarith`. In Part 3, `1 + h * lam ≤ 1` needs `h * lam ≤ 0`, which is the
product of `0 ≤ h` and `lam ≤ 0`: `linarith` cannot see it, `nlinarith` can. Placeholders: `(a b : ℝ)
(ha : 0 ≤ a) (hb : b ≤ 0)`.

| Before | After |
|---|---|
| `ha : 0 ≤ a, hb : b ≤ 0 ⊢ a * b ≤ 0` | (closed) |

Then R8 again: `gcongr` on `|1 + h * lam| ^ n * |y₀| ≤ 1 ^ n * |y₀|` goes through `* |y₀|` and `^ n` in one
call and reduces to `|1 + h * lam| ≤ 1`, which it closes by assumption if that fact is in the context.

**R17 · `one_pow`, `one_mul`** change the **goal**: `one_pow : 1 ^ n = 1`, `one_mul : 1 * a = a`. `simp` applies
both by itself. Placeholders: `(a : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (1 ^ n * a)` | `⊢ P a` |

---

## Part 4 · `euler_unstable`

Statement: if `2 < h·(-λ)` and `y₀ ≠ 0`, then `Tendsto (fun n => |euler lam h y₀ n|) atTop atTop`, i.e.
`|yₙ| → ∞`. The hypothesis says `1 + hλ < -1`, so `|1 + hλ| > 1`. No sign hypothesis on `λ` or `h` is needed.

**R18 · `rw [abs_of_neg]`** changes the **goal list**. The lemma is `abs_of_neg : a < 0 → |a| = -a`, so the goal
is rewritten and a side goal `a < 0` is added. Write `rw [abs_of_neg (by linarith)]` to prove the side goal
on the spot. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| <code>⊢ P &#124;a&#124;</code> | <code>⊢ P (-a)</code>, <code>⊢ a < 0</code> |

```lean-goal
⊢ P |a|
⊢ P (-a)
⊢ a < 0
```

**R19 · `simp_rw [l₁, l₂]`** changes the **goal**: it rewrites with each `lᵢ` in turn, also *under binders*
such as `fun n => …`. `rw [euler_closed_form]` fails there with "Did not find an occurrence of the pattern", because
the bound `n` is not a fixed term it can instantiate the lemma with. In Part 4 use `simp_rw [euler_closed_form, abs_mul, abs_pow]`.
Placeholders: `(f g : ℕ → ℝ) (thm : ∀ n, f n = g n) (P : (ℕ → ℝ) → Prop)`.

| Before | After |
|---|---|
| <code>⊢ P fun n => &#124;f n&#124;</code> | <code>⊢ P fun n => &#124;g n&#124;</code> |

```lean-goal
⊢ P fun n => |f n|
⊢ P fun n => |g n|
```

**R20 · `tendsto_pow_atTop_atTop_of_one_lt`** changes the **goal** with `apply`, or closes it with `exact … hr`.
The lemma is `1 < r → Tendsto (fun n => r ^ n) atTop atTop`: powers of a number above 1 go to infinity.
Placeholders: `(r : ℝ)` (any archimedean ordered semiring).

| Before | After |
|---|---|
| `⊢ Tendsto (fun n => r ^ n) atTop atTop` | `⊢ 1 < r` |

**R21 · `Filter.Tendsto.atTop_mul_const`** changes the **goal**. The lemma is
`0 < r → Tendsto f l atTop → Tendsto (fun x => f x * r) l atTop`: a sequence tending to ∞ times a positive
constant still tends to ∞. `l` is any filter (here `atTop` on `ℕ`). Because its name starts with
`Filter.Tendsto`, you can write it with *dot notation* on a proof `hu : Tendsto u atTop atTop`:
`hu.atTop_mul_const hc` means `Filter.Tendsto.atTop_mul_const hc hu`. Placeholders: `(u : ℕ → ℝ) (c : ℝ)
(hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun n => u n * c) atTop atTop` | `⊢ Tendsto u atTop atTop` |

**R22 · `abs_pos.mpr`** changes the **goal**. The lemma is `abs_pos : 0 < |a| ↔ a ≠ 0`; `.mpr` is its
right-to-left direction, a function from `a ≠ 0` to `0 < |a|` (`.mp` is left to right). Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| <code>⊢ 0 < &#124;a&#124;</code> | <code>⊢ a ≠ 0</code> |

```lean-goal
⊢ 0 < |a|
⊢ a ≠ 0
```

**W3** (guide.lean) is the whole Part 4 pattern on `|(-3)ⁿ c| → ∞`: prove `1 < |(-3)|` first, `simp_rw [abs_mul,
abs_pow]`, then one `exact` combining R20, R21, R22 by dot notation. After the `simp_rw` the goal is

```lean-goal
⊢ Tendsto (fun n => |(-3)| ^ n * |c|) atTop atTop
```

which has exactly the shape `fun n => r ^ n * c` that R21 applied to R20 produces.

---

## Traps

- `try?` is **banned**: it finds a proof of the closed form by itself. Prove that one by induction (R1).
- `λ` is reserved syntax (`fun`); the exercise names the rate `lam`.
- Prove the closed form first: in the later theorems `rw [euler_closed_form]` (R5) is the first step, and
  without it `euler` is an opaque recursion.
- `rw` cannot reach inside `fun n => …` (Part 4): use `simp_rw` (R19).
- `linarith` treats `h * lam` as an atom: it can use `h * (-lam) ≤ 2` (after normalising, that is linear in the
  atom `h * lam`), but not derive `h * lam ≤ 0` from `0 ≤ h` and `lam ≤ 0`. That needs `nlinarith` (R16).
- `Real.exp_nat_mul` is stated as `Real.exp (↑n * x)`: after `rw [← Real.exp_nat_mul]` the argument is
  `↑n * (h * lam)`, not the spec's `lam * (↑n * h)`. Close the difference with `ring_nf` (R12), not `rw`.
- `gcongr` leaves a side goal `0 ≤ a` when `positivity` cannot prove it from the hypotheses `0 ≤ x` in the
  context. Keep the sign hypotheses (`hl`, `hh`) in the context, or prove the side goal yourself.
- `t1 ; t2` runs `t2` on the first goal only. After `constructor`, use `<;>` to hit both bounds.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| closed form of a recursion | `induction n with \| zero => … \| succ n ih => …` | R1 |
| unfold the recursion at `0` / at `n + 1` | `simp [d]` / `rw [d]` | R2, R3 |
| `a ^ (n + 1) → a ^ n * a` | `rw [pow_succ]` | R4 |
| use an earlier theorem | `rw [thm]` | R5 |
| drop a common factor or exponent in `≤` | `gcongr` | R6, R8 |
| chain inequalities and equalities | `calc a ≤ b := … _ = c := …` | R7 |
| `x + 1 ≤ exp x` | `Real.add_one_le_exp x` | R9 |
| linear arithmetic, plus extra facts | `linarith [t]` | R10 |
| `exp x ^ n → exp (↑n * x)` | `rw [← Real.exp_nat_mul]` | R11 |
| equal up to ring algebra inside a function | `ring_nf` | R12 |
| `\|a * b\|`, `\|a ^ n\|` | `rw [abs_mul, abs_pow]` | R13, R14 |
| `\|a\| ≤ b` → two bounds | `rw [abs_le]; constructor` | R15 |
| needs a product of hypotheses | `nlinarith` | R16 |
| `1 ^ n * a → a` | `simp` | R17 |
| `\|a\|` with `a < 0` | `rw [abs_of_neg (by linarith)]` | R18 |
| rewrite under `fun n => …` | `simp_rw [l₁, l₂]` | R19 |
| `rⁿ → ∞` for `1 < r` | `tendsto_pow_atTop_atTop_of_one_lt hr` | R20 |
| `uₙ → ∞` ⇒ `uₙ · c → ∞` for `0 < c` | `hu.atTop_mul_const hc` | R21 |
| `0 < \|a\|` from `a ≠ 0` | `abs_pos.mpr ha` | R22 |
| see the state | infoview | |
