# H073 · Euler's method for y' = y converges to exp: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), including `induction` on `ℕ` and functions defined by
pattern matching. **New here:** Mathlib's real numbers `ℝ`, the casts `ℕ → ℝ`, `Real.exp`, absolute value
and `max`; limits (`Filter.Tendsto`, `atTop`, `𝓝`, `∀ᶠ`); the tactics `exact_mod_cast`, `simpa`, `calc`,
`omega`, `field_simp`, `positivity`, `linarith`, `set`, `congr`, `obtain`, `gcongr`, `filter_upwards`.

**The math.** Euler's method for `y' = f(y)` with step `h` is `y_{k+1} = y_k + h f(y_k)`. For `y' = y`,
`y(0) = 1`, on `[0, x]` with `n` steps, `h = x/n` and `y_{k+1} = y_k + h y_k = (1 + h) y_k`, so
$y_k = (1 + h)^k$ (Part 1). The exact solution is $e^t$, and after `n` steps $e^{x} = (e^{h})^n$. Put
$a = e^{h}$ (one exact step) and $b = 1 + h$ (one Euler step). For real `a, b` and `n ≥ 1`,

$$|a^n - b^n| \le |a - b| \cdot n \cdot \max(|a|, |b|)^{n-1}$$

(factor $a^n - b^n = (a - b)\sum_{i<n} a^{i} b^{n-1-i}$: `n` terms, each at most $\max^{n-1}$; R32). Three bounds feed it:

| Bound | Why | Milestone |
|---|---|---|
| $\lvert a - b\rvert = \lvert e^{h} - 1 - h\rvert \le h^2$ | Taylor, valid for $\lvert h\rvert \le 1$, i.e. $n \ge \lvert x\rvert$ | `exp_step_close` |
| $\lvert a\rvert, \lvert b\rvert \le e^{\lvert x\rvert/n}$ | $e^{h} \le e^{\lvert h\rvert}$; $\lvert 1 + h\rvert \le 1 + \lvert h\rvert \le e^{\lvert h\rvert}$ | `both_le` |
| $(e^{\lvert x\rvert/n})^{n-1} \le e^{\lvert x\rvert}$ | $(n-1)\lvert x\rvert/n \le \lvert x\rvert$ | `pow_bound` |

Together: $|e^{x} - (1 + x/n)^n| \le (x/n)^2 \cdot n \cdot e^{|x|} = x^2 e^{|x|}/n$ (Part 5): the global error
of Euler's method is $O(h)$, first order. Since $C/n \to 0$ for the constant $C = x^2 e^{|x|}$, the error
tends to 0 (Part 6, a *squeeze*: $0 \le |u_n - L| \le C/n$ for all large `n`).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` with `g : … → G` is an arbitrary goal for entries that only add a fact.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[LinearOrder α]` is a
  requirement on `α` (a *type class*); each entry says which familiar types meet it.
- A state containing `|` cannot sit in a Markdown table, so those entries show a ```` lean-goal ```` block: the
  first line is the goal before, the second the goal after.
- Every `⊢` cell and every `lean-goal` line is a state Lean reaches in the companion file;
  `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers |
| `↑n` | `(n : ℝ)`, the natural number `n` cast to `ℝ`; `↑(n - 1)` casts the ℕ-difference, `↑n - 1` subtracts in `ℝ` |
| `x / ↑n` | real division; Lean defines `x / 0 = 0`, which is why the theorems assume `0 < n` |
| `n - 1` (in `ℕ`) | *truncated* subtraction: `0 - 1 = 0` |
| `Real.exp x` | $e^x$ |
| `\|a\|` | absolute value `abs a` |
| `‖a‖` | the norm of `a`; for `a : ℝ` it equals `\|a\|` (R41) |
| `max a b` | the larger of `a`, `b`; `max \|a\| \|b\| ^ (n - 1)` is `(max \|a\| \|b\|) ^ (n - 1)` |
| `Tendsto u atTop (𝓝 L)` | $u_n \to L$ as $n \to \infty$. `atTop` is the filter "eventually, for large `n`"; `𝓝 L` is "near `L`" (`open Topology` for `𝓝`) |
| `∀ᶠ n in atTop, p n` | `p n` holds for all sufficiently large `n` (∃ `N`, ∀ `n ≥ N`, `p n`) |
| `fun e => ‖u e - L‖` | the sequence $e \mapsto \lVert u_e - L\rVert$ (the bound variable's name is arbitrary) |
| `a : ℝ := Real.exp y` | a local definition made by `set` (R25): `a` *is* `Real.exp y` |
| `n✝`, `a✝` | inaccessible names Lean invents; name them with `case succ k ih =>` or `with` (R1) |
| `case zero`, `case succ`, `case left`, `case right`, `case refine_1`, `case calc_1`, `case hbc` | tags of open goals, made by the tactic that split them (`induction`, `constructor`, `refine`, `calc`, `gcongr`) |
| `a : ℝ := ⋯` | a `set` variable (R25) whose value Lean hides in this view; it is still `Real.exp (x / ↑n)` |
| `↑1` | the natural number `1` cast to `ℝ`, left by R19; R20 turns it into `1` |
| `noncomputable def` (in the spec) | a definition over `ℝ` that Lean cannot run as a program; proofs about it are unaffected |

---

## Part 1 · `eulerExp_eq_pow`

Statement: `eulerExp x n k = (1 + x / ↑n) ^ k` for every `k`: Euler's method returns the closed form.

**R1 · `induction k`** changes the **goal list**: the goal for an arbitrary `k` becomes one goal for `0` and
one for `k + 1` with the induction hypothesis. Placeholders: `(P : ℕ → Prop) (k : ℕ)`. Lean names the new
variable and hypothesis `n✝ a✝`; `case succ k ih =>` (or `induction k with | zero => … | succ k ih => …`)
names them `k`, `ih`.

| Before | After |
|---|---|
| `k : ℕ ⊢ P k` | `⊢ P 0`, `n✝ : ℕ, a✝ : P n✝ ⊢ P (n✝ + 1)` |

**R2 · `rw [f]`** for a function `f` defined by pattern matching changes the **goal**: `f` applied to
`k + 1` becomes the right side of its `k + 1` clause. Placeholders: the toy `geo c : ℕ → ℝ` with clauses
`0 => 1` and `k + 1 => c * geo c k`; `(c : ℝ) (k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (geo c (k + 1))` | `⊢ P (c * geo c k)` |

**R3 · `rw [pow_succ]`** changes the **goal**. The lemma is `pow_succ : a ^ (n + 1) = a ^ n * a`.
Placeholders: `{M : Type} [Monoid M] (a : M) (n : ℕ)` (`[Monoid M]`: an associative `*` with `1`; `ℝ`
qualifies).

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

The zero case closes by `rfl` (both sides compute to `1`); after `rw [eulerExp, ih, pow_succ]` the succ case
is a ring identity in `y = (1 + x/↑n) ^ k`, closed by `ring` (TACTIC_STATES).

**W1** in the guide: `geo c k = c ^ k` by exactly this pattern.

---

## Part 2 · `exp_step_close` (MILESTONE 1)

Statement: for `0 < n` and `|x| ≤ ↑n`, `|Real.exp (x / ↑n) - (1 + x / ↑n)| ≤ (x / ↑n) ^ 2`: one exact step
versus one Euler step.

**R4 · `exact_mod_cast h`** **closes** a goal that is `h` up to casts. Used as
`have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0`. Placeholders: `(n : ℕ) (hn : 0 < n)`.

| Before | After |
|---|---|
| `hn : 0 < n ⊢ 0 < ↑n` | no goals |

**R5 · `rw [abs_div]`** changes the **goal**. The lemma is `abs_div : |a / b| = |a| / |b|`. Placeholders:
`(a b : ℝ)`.

```lean-goal
⊢ P |a / b|
⊢ P (|a| / |b|)
```

**R6 · `rw [abs_of_pos ha]`** changes the **goal**. The lemma is `abs_of_pos : 0 < a → |a| = a`.
Placeholders: `(a : ℝ) (ha : 0 < a)`.

```lean-goal
⊢ P |a|
⊢ P a
```

**R7 · `rw [div_le_one hb]`** changes the **goal**. The lemma is `div_le_one : 0 < b → (a / b ≤ 1 ↔ a ≤ b)`;
`rw` with an `↔` replaces one proposition by the other. Placeholders: `(a b : ℝ) (hb : 0 < b)`.

| Before | After |
|---|---|
| `⊢ a / b ≤ 1` | `⊢ a ≤ b` |

R5 → R6 → R7 turn `|x / ↑n| ≤ 1` into `|x| ≤ ↑n`, which is the hypothesis `hn`.

**R8 · `Real.abs_exp_sub_one_sub_id_le`** changes the **context** (as a `have`). The lemma is
`|y| ≤ 1 → |Real.exp y - 1 - y| ≤ y ^ 2` (Taylor: $e^y = 1 + y + O(y^2)$ with constant 1 on $|y| \le 1$).
Placeholders: `(y : ℝ) (hy : |y| ≤ 1)`. After `have h := Real.abs_exp_sub_one_sub_id_le hy` the goal `G` is
unchanged and the context gains

```text
h : |Real.exp y - 1 - y| ≤ y ^ 2
```

**R9 · `rw [sub_sub]`** changes the **goal**. The lemma is `sub_sub : a - b - c = a - (b + c)`. Placeholders:
`(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a - b - c)` | `⊢ P (a - (b + c))` |

**R10 · `simpa [l] using e`** **closes** the goal: it simplifies the goal and the type of `e` with the simp
set plus `l`, then closes the goal with the simplified `e`. Use it when `e` is the goal up to a rewrite such as
R9. Placeholders: `(a b c r : ℝ) (e : |a - b - c| ≤ r)`.

```lean-goal
⊢ |a - (b + c)| ≤ r
```

(then no goals). R8's bound has `- 1 - y`; the milestone has `- (1 + y)`: R9 bridges them.

---

## Part 3 · `both_le` (MILESTONE 2)

Statement: for `0 < n`, `|Real.exp (x / ↑n)| ≤ Real.exp (|x| / ↑n) ∧ |1 + x / ↑n| ≤ Real.exp (|x| / ↑n)`.
Split with `constructor` (TACTIC_STATES).

**R11 · `rw [Real.abs_exp]`** changes the **goal**. The lemma is `Real.abs_exp : |Real.exp y| = Real.exp y`.
Placeholders: `(y : ℝ)`.

```lean-goal
⊢ P |Real.exp y|
⊢ P (Real.exp y)
```

**R12 · `rw [Real.exp_le_exp]`** changes the **goal**. The lemma is
`Real.exp_le_exp : Real.exp a ≤ Real.exp b ↔ a ≤ b` (`exp` is strictly increasing). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ Real.exp a ≤ Real.exp b` | `⊢ a ≤ b` |

**R13 · `rw [div_le_div_iff_of_pos_right hc]`** changes the **goal**. The lemma is
`0 < c → (a / c ≤ b / c ↔ a ≤ b)`. Placeholders: `(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ a / c ≤ b / c` | `⊢ a ≤ b` |

**R14 · `le_abs_self`** **closes** the goal: `le_abs_self a : a ≤ |a|`. Placeholders: `(a : ℝ)`.

```lean-goal
⊢ a ≤ |a|
```

**R15 · `calc`** changes the **goal list**: a goal `a ≤ c` is proved as a chain of links
`a ≤ b`, `b = c`, each proved after its own `:=` (`_` is the previous right side). Lean combines `≤` and `=`
links into `≤`. Written with `?_` as the proofs, each link becomes a goal. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ a ≤ b`, `⊢ b = c` |

For the second conjunct the chain is `|1 + x/↑n| ≤ 1 + |x/↑n| = |x|/↑n + 1 ≤ Real.exp (|x|/↑n)`.

**R16 · `abs_add_le`** changes the **context** (as a `have`). The lemma is the triangle inequality
`abs_add_le a b : |a + b| ≤ |a| + |b|`. Placeholders: `(a b : ℝ)`. The context gains

```text
h : |a + b| ≤ |a| + |b|
```

With `a = 1` it reads `|1 + y| ≤ |1| + |y|`; `simpa using abs_add_le 1 y` (R10) turns `|1|` into `1`.

**R17 · `Real.add_one_le_exp`** changes the **context** (as a `have`), or closes a goal of exactly its form
by `exact`. The lemma is `Real.add_one_le_exp y : y + 1 ≤ Real.exp y`. Placeholders: `(y : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `h : y + 1 ≤ Real.exp y ⊢ G` |

---

## Part 4 · `pow_bound` (MILESTONE 3)

Statement: for `0 < n`, `Real.exp (|x| / ↑n) ^ (n - 1) ≤ Real.exp |x|` (`n - 1` is ℕ subtraction).

**R18 · `rw [← Real.exp_nat_mul]`** changes the **goal**. The lemma is
`Real.exp_nat_mul y n : Real.exp (↑n * y) = Real.exp y ^ n`; right to left it pulls the power into the
exponent. Placeholders: `(y : ℝ) (n : ℕ)`. Then R12 leaves `↑(n - 1) * (|x| / ↑n) ≤ |x|`.

| Before | After |
|---|---|
| `⊢ P (Real.exp y ^ n)` | `⊢ P (Real.exp (↑n * y))` |

**R19 · `rw [Nat.cast_sub hmn]`** changes the **goal**. The lemma is
`Nat.cast_sub : m ≤ n → ↑(n - m) = ↑n - ↑m`: the cast of a truncated difference is the real difference only
when no truncation happens. Placeholders: `(n m : ℕ) (hmn : m ≤ n)`; the target is `ℝ`.

| Before | After |
|---|---|
| `⊢ P ↑(n - m)` | `⊢ P (↑n - ↑m)` |

**R20 · `rw [Nat.cast_one]`** changes the **goal**: `Nat.cast_one : ↑1 = 1` (the natural number `1` cast to
`ℝ`). Needed after R19 with `m = 1`, since `↑n - ↑1` is not yet `↑n - 1`.

| Before | After |
|---|---|
| `⊢ P ↑1` | `⊢ P 1` |

**R21 · `omega`** **closes** linear goals over `ℕ`/`ℤ`, including `max`, `min` and truncated `-`. Here it proves
R19's side condition: `rw [Nat.cast_sub (by omega)]` with `hn0 : 0 < n` in the context. Placeholders:
`(n N : ℕ) (hn : max N 1 ≤ n)`.

| Before | After |
|---|---|
| `hn : max N 1 ≤ n ⊢ 1 ≤ n` | no goals |

**R22 · `field_simp`** changes the **goal**: it multiplies out the denominators it can prove nonzero (it reads
`hk : 0 < k` or `k ≠ 0` from the context) and may close the goal outright. Use it for a fact such as
`(↑n - 1) * (|x| / ↑n) = |x| - |x| / ↑n`. Placeholders: `(y k : ℝ) (hk : 0 < k)`.

| Before | After |
|---|---|
| `hk : 0 < k ⊢ y / k + 1 = 2` | `⊢ y + k = k * 2` |

**R23 · `positivity`** **closes** `0 ≤ e` or `0 < e` for `e` built from `|·|`, `Real.exp`, squares, casts of
`ℕ`, `+`, `*`, `/`. Placeholders: `(y : ℝ) (k : ℕ)`.

```lean-goal
⊢ 0 ≤ |y| / ↑k
```

**R24 · `linarith`** **closes** a linear equality or inequality that follows by adding up hypotheses
(products of variables count as atoms). It finishes `pow_bound` from the R22 fact and the R23 fact.
Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `h1 : a = b - c, h2 : 0 ≤ c ⊢ a ≤ b` | no goals |

---

## Part 5 · `euler_exp_error`

Statement: for `0 < n` and `|x| ≤ ↑n`, `|Real.exp x - (1 + x / ↑n) ^ n| ≤ x ^ 2 * Real.exp |x| / ↑n`.

**R25 · `set a := e`** changes the **context and the goal**: the context gains the local definition
`a : T := e`, and every `e` in the goal becomes `a`. It keeps long subterms readable. Placeholders:
`(y : ℝ)`, `e = Real.exp y`.

| Before | After |
|---|---|
| `⊢ P (Real.exp y)` | `a : ℝ := Real.exp y ⊢ P a` |

**R26 · `congr 1`** changes the **goal**: `f a = f b` becomes `a = b` (one level of arguments). It closes
the new goal by itself when it is a hypothesis. Use it for `hpow : a ^ n = Real.exp x` after R18:
`Real.exp (↑n * (x / ↑n)) = Real.exp x` → `↑n * (x / ↑n) = x`, then R22. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ Real.exp a = Real.exp b` | `⊢ a = b` |

**W2** in the guide: `Real.exp (y / 3) ^ 3 = Real.exp y` by R18, R26, R22, `ring`.

**R27 · `obtain ⟨ha, hb⟩ := h`** changes the **context**: `h : A ∧ B` is replaced by its two halves. Use it
on a milestone: `obtain ⟨ha, hb⟩ := both_le x n hn0`. Placeholders: `(A B G : Prop)`.

| Before | After |
|---|---|
| `h : A ∧ B ⊢ G` | `ha : A, hb : B ⊢ G` |

**R28 · `pow_le_pow_left₀`** changes the **context** (as a `have`, or as a term). The lemma is
`0 ≤ a → a ≤ b → ∀ n, a ^ n ≤ b ^ n`. Placeholders: `(a b : ℝ) (n : ℕ) (h0 : 0 ≤ a) (hab : a ≤ b)`.

| Before | After |
|---|---|
| `⊢ G` | `h : a ^ n ≤ b ^ n ⊢ G` |

**R29 · `le_max_of_le_left`** changes the **context**: `a ≤ b → a ≤ max b c`. With `abs_nonneg _ : 0 ≤ |a|` it
gives `0 ≤ max |a| |b|`, R28's first hypothesis. Placeholders: `{α : Type} [LinearOrder α] (a b c : α)`
(`[LinearOrder α]`: any two elements compare; `ℝ` and `ℕ` qualify).

| Before | After |
|---|---|
| `⊢ G` | `h : a ≤ max b c ⊢ G` |

The lemma `abs_nonneg r : 0 ≤ |r|` (for `r : ℝ`) supplies the `a ≤ b` here. The second example in the guide
chains them, `have h0 := abs_nonneg r` then `have h := le_max_of_le_left (c := s) h0`, and the context gains

```text
h0 : 0 ≤ |r|
h : 0 ≤ max |r| s
```

**R30 · `max_le`** changes the **context**: `a ≤ c → b ≤ c → max a b ≤ c`. From R27's `ha`, `hb` it gives
`max |a| |b| ≤ Real.exp (|x| / ↑n)`, R28's second hypothesis. Placeholders as R29.

| Before | After |
|---|---|
| `⊢ G` | `h : max a b ≤ c ⊢ G` |

**R31 · `h₁.trans h₂`** (lemma `le_trans`) changes the **context**: from `h₁ : a ≤ b` and `h₂ : b ≤ c`,
`a ≤ c`. Chains R28 with MILESTONE 3 into `hmax : max |a| |b| ^ (n - 1) ≤ Real.exp |x|`. Placeholders:
`(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `h : a ≤ c ⊢ G` |

**R32 · `abs_pow_sub_pow_le`** changes the **context** (or starts a `calc`, R15). The lemma is
`abs_pow_sub_pow_le a b n : |a ^ n - b ^ n| ≤ |a - b| * ↑n * max |a| |b| ^ (n - 1)`.
Placeholders: `(a b : ℝ) (n : ℕ)` (any ordered commutative ring). The context gains

```text
h : |a ^ n - b ^ n| ≤ |a - b| * ↑n * max |a| |b| ^ (n - 1)
```

**R33 · `gcongr`** changes the **goal list**: for `f s ≤ f S` where both sides have the same shape, it leaves
one goal per position where they differ. A position whose inequality is a hypothesis (here `hM`, in the
problem `hmax`) is closed for you, and `0 ≤ …` side conditions go to `positivity` (R23). Placeholders:
`(s t r M : ℝ) (k m : ℕ) (hM : |t| ^ m ≤ M)`.

```lean-goal
⊢ |s| * ↑k * |t| ^ m ≤ r ^ 2 * ↑k * M
⊢ |s| ≤ r ^ 2
```

In the problem the remaining goal is `|a - b| ≤ (x / ↑n) ^ 2`: MILESTONE 1. The last `calc` link,
`(x / ↑n) ^ 2 * ↑n * Real.exp |x| = x ^ 2 * Real.exp |x| / ↑n`, is R22.

---

## Part 6 · `euler_converges_exp`

Statement: `Tendsto (fun n : ℕ => (1 + x / ↑n) ^ n) atTop (𝓝 (Real.exp x))`, i.e. $(1 + x/n)^n \to e^x$.

**R34 · `rw [tendsto_iff_norm_sub_tendsto_zero]`** changes the **goal**: `u → L` becomes `‖u n - L‖ → 0`.
Placeholders: `(u : ℕ → ℝ) (L : ℝ)`.

| Before | After |
|---|---|
| `⊢ Tendsto u atTop (𝓝 L)` | `⊢ Tendsto (fun e => ‖u e - L‖) atTop (𝓝 0)` |

**R35 · `refine squeeze_zero' ?_ ?_ hg`** changes the **goal list**. The lemma is
`squeeze_zero' : (∀ᶠ t in l, 0 ≤ f t) → (∀ᶠ t in l, f t ≤ g t) → Tendsto g l (𝓝 0) → Tendsto f l (𝓝 0)`.
Give the third argument (`hg`, or R38): it fixes the upper sequence `g`. Placeholders:
`(f g : ℕ → ℝ) (hg : Tendsto g atTop (𝓝 0))`.

| Before | After |
|---|---|
| `⊢ Tendsto f atTop (𝓝 0)` | `⊢ ∀ᶠ (t : ℕ) in atTop, 0 ≤ f t`, `⊢ ∀ᶠ (t : ℕ) in atTop, f t ≤ g t` |

**R36 · `Eventually.of_forall`** changes the **goal**: "eventually" follows from "always". The lemma is
`(∀ x, p x) → ∀ᶠ x in f, p x`. As a term: `Eventually.of_forall fun n => norm_nonneg _` (with R37) fills the
first `?_` of R35. Placeholders: `(p : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ᶠ (n : ℕ) in atTop, p n` | `⊢ ∀ (x : ℕ), p x` |

**R37 · `norm_nonneg`** **closes** `0 ≤ ‖v‖`: `norm_nonneg v : 0 ≤ ‖v‖`. Placeholders: `(v : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ ‖v‖` | no goals |

**R38 · `tendsto_const_div_atTop_nhds_zero_nat C`** **closes** `C / ↑n → 0`. Placeholders: `(C : ℝ)`; in the
problem `C = x ^ 2 * Real.exp |x|`.

| Before | After |
|---|---|
| `⊢ Tendsto (fun n => C / ↑n) atTop (𝓝 0)` | no goals |

**R39 · `obtain ⟨N, hN⟩ := exists_nat_ge y`** changes the **context**. The lemma is
`exists_nat_ge y : ∃ N : ℕ, y ≤ ↑N` (ℝ is Archimedean). With `y = |x|`, `N` is the index from which R8 applies.
Placeholders: `(y : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `N : ℕ, hN : y ≤ ↑N ⊢ G` |

**R40 · `filter_upwards [eventually_ge_atTop N] with n hn`** changes the **goal and the context**: an
"eventually" goal becomes the claim for one fixed `n` with `hn : N ≤ n`
(`eventually_ge_atTop N : ∀ᶠ n in atTop, N ≤ n`). Use `max N 1` in place of `N` to get `0 < n` as well
(R21, R43). Placeholders: `(p : ℕ → Prop) (N : ℕ)`.

| Before | After |
|---|---|
| `⊢ ∀ᶠ (n : ℕ) in atTop, p n` | `n : ℕ, hn : N ≤ n ⊢ p n` |

**R41 · `rw [Real.norm_eq_abs]`** changes the **goal**: `Real.norm_eq_abs r : ‖r‖ = |r|`. Placeholders:
`(r : ℝ)`.

```lean-goal
⊢ P ‖r‖
⊢ P |r|
```

**R42 · `rw [abs_sub_comm]`** changes the **goal**: `abs_sub_comm a b : |a - b| = |b - a|`. R34 produces
`(1 + x/↑n)^n - Real.exp x`; Part 5 bounds `Real.exp x - (1 + x/↑n)^n`. Placeholders: `(a b : ℝ)`.

```lean-goal
⊢ P |a - b|
⊢ P |b - a|
```

**R43 · `le_of_max_le_left`** changes the **context**: `max a b ≤ c → a ≤ c`. From R40's `hn : max N 1 ≤ n` it
gives `N ≤ n`; R4 (`exact_mod_cast`) moves it to `↑N ≤ ↑n`, and `hN.trans` (R31) gives `|x| ≤ ↑n`.
Placeholders as R29.

| Before | After |
|---|---|
| `hm : max a b ≤ c ⊢ G` | `h : a ≤ c ⊢ G` |

**W3** in the guide chains R34 → R35 (with R36 + R37 and R38 as arguments) → R40 → R41 for an abstract
sequence `u` with an eventual bound `|u n - L| ≤ C / ↑n`:

```lean-goal
⊢ Tendsto u atTop (𝓝 L)
⊢ Tendsto (fun e => ‖u e - L‖) atTop (𝓝 0)
⊢ ∀ᶠ (t : ℕ) in atTop, ‖u t - L‖ ≤ C / ↑t
⊢ ‖u n - L‖ ≤ C / ↑n
⊢ |u n - L| ≤ C / ↑n
```

---

## Traps

- `n - 1 : ℕ` is truncated. `↑(n - 1) = ↑n - 1` needs `1 ≤ n` (R19 + R20, side goal by R21).
- `0 < n` (in `ℕ`) and `(0 : ℝ) < ↑n` are different statements; convert with `exact_mod_cast` (R4). Most
  real-number lemmas (R6, R7, R13, R22) want the real one, so prove `hnpos` first.
- `x / ↑0 = 0` in Lean, so every bound needs `0 < n`. In the limit, filter with `max N 1` (R40), not `N`.
- R8 needs `|x / ↑n| ≤ 1`, not `|x| ≤ ↑n`: rewrite with R5 → R6 → R7.
- After `set a := …` (R25) the goal shows `a`, not `Real.exp (x / ↑n)`. `rw [h]` needs the left side of `h` to
  appear literally, so state facts such as `hpow` in terms of `a` after the `set`.
- `gcongr` (R33) uses hypotheses already in the context: prove `hmax` before you call it.
- Facts you get after `set` (such as `ha`, `hb` from `obtain … := both_le x n hn0`) still show
  `Real.exp (x / ↑n)` and `1 + x / ↑n`, not `a`, `b`. They are still accepted where `|a|`, `|b|` is expected
  (`max_le ha hb`), because `a` is by definition that term; `rw` with them, however, looks for the literal text.
- `simp` writes `|1|` as `1`: use `simpa using abs_add_le 1 (x / ↑n)` rather than `exact`.
- The MILESTONE lemmas are optional, but `euler_exp_error` below uses them by name; if you rename or delete
  one, adjust its uses.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| closed form of a recursion | `induction k with \| zero => rfl \| succ k ih => rw [f, ih, pow_succ]; ring` | R1–R3 |
| `(0 : ℝ) < ↑n` from `0 < n` | `exact_mod_cast hn0` | R4 |
| `\|x / ↑n\| ≤ 1` → `\|x\| ≤ ↑n` | `rw [abs_div, abs_of_pos hnpos, div_le_one hnpos]` | R5–R7 |
| Taylor bound for `exp` | `Real.abs_exp_sub_one_sub_id_le h` | R8 |
| `a - b - c` vs `a - (b + c)` | `simpa [sub_sub] using e` | R9, R10 |
| `\|exp y\| ≤ exp z` | `rw [Real.abs_exp, Real.exp_le_exp]` | R11, R12 |
| `a / c ≤ b / c` → `a ≤ b` | `rw [div_le_div_iff_of_pos_right hc]` | R13 |
| `a ≤ \|a\|`, triangle inequality | `le_abs_self a`, `abs_add_le a b` | R14, R16 |
| chain of (in)equalities | `calc a ≤ b := … _ = c := …` | R15 |
| `y + 1 ≤ exp y` | `Real.add_one_le_exp y` | R17 |
| `exp y ^ n` → `exp (↑n * y)` | `rw [← Real.exp_nat_mul]` | R18 |
| `↑(n - 1)` → `↑n - 1` | `rw [Nat.cast_sub (by omega), Nat.cast_one]` | R19–R21 |
| clear denominators | `field_simp` | R22 |
| `0 ≤ …`, linear finish | `positivity`, `linarith` | R23, R24 |
| name a subterm | `set a := e` | R25 |
| `exp u = exp v` → `u = v` | `congr 1` | R26 |
| split `A ∧ B` in the context | `obtain ⟨ha, hb⟩ := h` | R27 |
| `aⁿ ≤ bⁿ` | `pow_le_pow_left₀ h0 hab n` | R28 |
| bounds on `max` | `le_max_of_le_left (abs_nonneg _)`, `max_le`, `le_of_max_le_left` | R29, R30, R43 |
| chain two `≤` | `h₁.trans h₂` | R31 |
| `\|aⁿ - bⁿ\|` bound | `abs_pow_sub_pow_le a b n` | R32 |
| compare products factor by factor | `gcongr` | R33 |
| `u → L` → `‖u - L‖ → 0` | `rw [tendsto_iff_norm_sub_tendsto_zero]` | R34 |
| squeeze to 0 | `refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ (tendsto_const_div_atTop_nhds_zero_nat C)` | R35–R38 |
| an index `N ≥ y` | `obtain ⟨N, hN⟩ := exists_nat_ge y` | R39 |
| "for all large `n`" | `filter_upwards [eventually_ge_atTop (max N 1)] with n hn` | R40 |
| `‖r‖` → `\|r\|`, swap `\|a - b\|` | `rw [Real.norm_eq_abs, abs_sub_comm]` | R41, R42 |
| see the state | infoview | |
