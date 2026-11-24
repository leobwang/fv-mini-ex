# M104 · Floating-point products: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): lists, `def` by pattern matching, `∃`, `∧`, `rw`, `exact`.
**New here:** Mathlib's real numbers `ℝ`, absolute value `|x|`, `List.prod`, and the inequality tactics
`gcongr` and `nlinarith`.

**The model.** A floating-point system with unit roundoff `u` (for IEEE double, `u = 2⁻⁵³`) is modelled by
an arbitrary function `fl : ℝ → ℝ` that satisfies `RelErr u fl`: for every real `x` there is a `δ` with
`|δ| ≤ u` and `fl x = x * (1 + δ)`. Nothing else about `fl` is known. `fprod fl [x₁, …, xₙ]` rounds after
every multiplication, from the right: `fl (x₁ * fl (x₂ * … fl (xₙ * 1)))`. The claim is that the whole
product carries one relative error `θ` with `|θ| ≤ (1 + u)ⁿ - 1 ≈ n u`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. All of this problem's numbers are in `ℝ`; the lemmas hold more
  generally (`abs_add_le` in any ordered additive group, `pow_succ` in any monoid), but you never need that.
- Every `⊢` cell in backticks is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
  A Markdown table cannot hold a `|` inside backticks, so states with absolute values are written as plain
  text in the table and repeated, checked, in a `lean-goal` block under it.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers |
| `\|x\|` | `abs x`, the absolute value of `x` (Mathlib notation) |
| `x :: xs` | the list with head `x` and tail `xs`; `[]` is the empty list |
| `xs.length` | `List.length xs : ℕ`, the number of elements |
| `xs.prod` | `List.prod xs`, the product of the elements; `[].prod = 1` |
| `(1 + u) ^ n` | `1 + u` multiplied by itself `n` times (`n : ℕ`) |
| `fl : ℝ → ℝ` | an unknown rounding function; `RelErr u fl` is all you know about it |
| `fprod fl (x :: xs)` | unfolds (R4) to `fl (x * fprod fl xs)` |
| `case nil`, `case cons` | the two goals after `induction xs` |
| `case cons.refine_1`, `case cons.refine_2`, `case h₁`, `case b0` | names Lean gives to new goals (after `refine` in the `cons` case, inside `gcongr`); ignore them |

---

## Part 1 · `fprod_error`

Statement: for every list `xs` there is a `θ` with `|θ| ≤ (1 + u) ^ xs.length - 1` and
`fprod fl xs = xs.prod * (1 + θ)`. Induction on `xs`. In the step, the tail has error `θ` (from `ih`) and the
last rounding has error `δ` (from `hfl`). Since `(1 + θ)(1 + δ) = 1 + (θ + δ + θδ)`, the new error is
`θ + δ + θ * δ`, and it obeys `|θ + δ + θδ| ≤ |θ| + |δ| + |θ||δ| ≤ ((1+u)ⁿ - 1) + u + ((1+u)ⁿ - 1)u = (1+u)ⁿ⁺¹ - 1`.

### Induction and the empty list

**R1 · `induction xs with | nil => … | cons x xs ih => …`** changes the **goal list and the context**: one goal
for the empty list and one for `x :: xs`, where `ih` is the statement for the tail `xs`. Placeholders:
`(P : List ℝ → Prop) (xs : List ℝ)`.

| Before | After |
|---|---|
| `⊢ P xs` | `⊢ P []`, `x : ℝ, xs : List ℝ, ih : P xs ⊢ P (x :: xs)` |

**R2 · `refine ⟨w, ?_, ?_⟩`** changes the **goal list**: it picks the witness `w` of an `∃` and leaves one goal
per conjunct. `exact ⟨w, p, q⟩` does the same with both proofs supplied, e.g. `⟨0, by simp, by simp [f]⟩`.
Placeholders: `(A B : ℝ → Prop) (w : ℝ)`.

| Before | After |
|---|---|
| `⊢ ∃ θ, A θ ∧ B θ` | `⊢ A w`, `⊢ B w` |

**R3 · `List.length_nil`, `pow_zero`, `sub_self`, `abs_zero`** change the **goal**:
`[].length = 0`, `a ^ 0 = 1`, `a - a = 0`, `|0| = 0`. `simp` applies all four and closes the result `0 ≤ 0`.
Placeholders: `(a : ℝ)` (it plays `1 + u`).

| Before | After `List.length_nil` | After `pow_zero` | After `sub_self` | After `abs_zero` |
|---|---|---|---|---|
| ⊢ \|0\| ≤ a ^ [].length - 1 | ⊢ \|0\| ≤ a ^ 0 - 1 | ⊢ \|0\| ≤ 1 - 1 | ⊢ \|0\| ≤ 0 | closed |

```lean-goal
⊢ |0| ≤ a ^ [].length - 1
⊢ |0| ≤ a ^ 0 - 1
⊢ |0| ≤ 1 - 1
⊢ |0| ≤ 0
```

**R4 · `rw [f]` / `simp [f]`** changes the **goal**: a recursive definition applied to `[]` or to `x :: xs` is
replaced by the matching clause. Placeholders: `f` defined by `f [] = 1`, `f (x :: xs) = 2 * x * f xs`.
Use it in both cases: `simp [fprod]` in `nil`, `rw [fprod]` in `cons`.

| Before | After |
|---|---|
| `⊢ P (f (x :: xs))` | `⊢ P (2 * x * f xs)` |
| `⊢ P (f [])` | `⊢ P 1` |

**R5 · `List.prod_nil`, `add_zero`, `mul_one`** change the **goal**: `[].prod = 1`, `a + 0 = a`, `a * 1 = a`.
`simp` applies them. Placeholders: none beyond `P : ℝ → Prop`.

| Before | After `List.prod_nil` | After `add_zero` | After `mul_one` |
|---|---|---|---|
| `⊢ P ([].prod * (1 + 0))` | `⊢ P (1 * (1 + 0))` | `⊢ P (1 * 1)` | `⊢ P 1` |

### Taking hypotheses apart

**R6 · `obtain ⟨θ, hA, hB⟩ := h`** changes the **context**: an `∃ … ∧ …` hypothesis becomes a witness and two
facts, and `h` disappears. The goal is unchanged. Use it on `ih`, and on `hfl t` (R7). Placeholders:
`(A B : ℝ → Prop) (h : ∃ θ, A θ ∧ B θ)`.

| Before | After |
|---|---|
| `h : ∃ θ, A θ ∧ B θ`  `⊢ G` | `θ : ℝ, hA : A θ, hB : B θ ⊢ G` |

**R7 · `hg t`** changes the **context** (with `have` or `obtain`): a hypothesis `hg : ∀ x, Q x` applied to a
term `t` gives `Q t`. This works even when `hg`'s type is a defined name such as `Lip c g` (or `RelErr u fl`),
because Lean unfolds the definition to find the `∀`. A theorem proved earlier in the file is used the same way:
`obtain ⟨θ, hθ, h⟩ := my_theorem args`. Placeholders: `(c t : ℝ) (g : ℝ → ℝ) (hg : Lip c g)` where
`Lip c g := ∀ x, |g x| ≤ c * |x|`.

| Before | After |
|---|---|
| ⊢ G | ht : \|g t\| ≤ c \* \|t\| ⊢ G |

Pick `t` as the exact argument of `fl` in your goal: after `rw [fprod]` that is `x * fprod fl xs`.

### Inequalities with absolute values

**R8 · `calc a ≤ b := p` / `_ ≤ c := q`** changes the **goal list**: a chain of steps, each proved by its own
`:=` term (`by tac` is fine); `_` stands for the previous right side. With `?_` as the proofs the steps become
goals. Placeholders: `(a b c : ℝ)`. Write `calc _ ≤ b := …` to let Lean fill the first left side from the goal.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ a ≤ b`, `⊢ b ≤ c` |

**R9 · `abs_add_le a b`** **closes** the goal. Lemma: `|a + b| ≤ |a| + |b|` (triangle inequality).
Placeholders: `(a b : ℝ)`. Use it twice: once on `(θ + δ) + θ * δ`, once on `θ + δ`.

| Before | After |
|---|---|
| ⊢ \|a + b\| ≤ \|a\| + \|b\| | closed |

```lean-goal
⊢ |a + b| ≤ |a| + |b|
```

**R10 · `rw [abs_mul]`** changes the **goal**. Lemma: `|a * b| = |a| * |b|`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| ⊢ P \|a \* b\| | ⊢ P (\|a\| \* \|b\|) |

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R11 · `gcongr` on a sum** changes the **goal**: for `a + c ≤ b + c` it cancels the common summand `c` and
leaves `a ≤ b`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| ⊢ \|a + b\| + c ≤ \|a\| + \|b\| + c | ⊢ \|a + b\| ≤ \|a\| + \|b\| |

```lean-goal
⊢ |a + b| + c ≤ |a| + |b| + c
⊢ |a + b| ≤ |a| + |b|
```

**R12 · `gcongr` on a product** changes the **goal list**. `a * b ≤ c * d` needs `a ≤ c`, `b ≤ d`, `0 ≤ b`,
`0 ≤ c`. `gcongr` closes each one it can, by a hypothesis in the context or by `positivity` (which proves
`0 ≤ |b|`, `0 ≤ x ^ 2`, … from the shape of the term alone), and leaves the rest to you.
Placeholders: `(a b c d : ℝ) (hac : |a| ≤ c) (hbd : |b| ≤ d)`.

| Before | After |
|---|---|
| ⊢ \|a\| \* \|b\| ≤ c \* d | `⊢ 0 ≤ c` |

```lean-goal
⊢ |a| * |b| ≤ c * d
⊢ 0 ≤ c
```

In the problem `c` is `(1 + u) ^ xs.length - 1`: `positivity` cannot see that it is `≥ 0`, so this side goal
is yours. Get it from `hθ : |θ| ≤ c` with R13 and R14.

**R13 · `abs_nonneg a`** **closes** the goal. Lemma: `0 ≤ |a|`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| ⊢ 0 ≤ \|a\| | closed |

```lean-goal
⊢ 0 ≤ |a|
```

**R14 · `le_trans`** changes the **goal list**. Lemma: `a ≤ b → b ≤ c → a ≤ c`. Usually given both proofs:
`exact le_trans h₁ h₂`, which closes the goal. `apply le_trans (b := b)` leaves both as goals.
Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ a ≤ b`, `⊢ b ≤ c` |

### The power after one more element

**R15 · `rw [List.length_cons]`** changes the **goal**. Lemma: `(a :: l).length = l.length + 1`.
Placeholders: `(x : ℝ) (xs : List ℝ) (P : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (x :: xs).length` | `⊢ P (xs.length + 1)` |

**R16 · `rw [pow_succ]`** changes the **goal**. Lemma: `a ^ (n + 1) = a ^ n * a`. Placeholders: `(a : ℝ) (n : ℕ)`.
After R15 and R16 the bound you need reads `(1 + u) ^ xs.length * (1 + u) - 1`.

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

**R17 · `nlinarith`** **closes** a goal `≤`, `<`, `=` that follows by adding up hypotheses with nonnegative
coefficients. It multiplies everything out first and treats a product of unknowns (`A * v`, `|θ| * |δ|`,
`(1 + u) ^ n * u`) as one more unknown; it also multiplies pairs of hypotheses, which `linarith` never does.
It knows nothing about `|·|`, so state the triangle-inequality facts first (R8–R12). Placeholders:
`(s p q r A v : ℝ)` with `h1 : s ≤ p + q + r`, `hp : p ≤ A - 1`, `hq : q ≤ v`, `hr : r ≤ (A - 1) * v`.

| Before | After |
|---|---|
| `⊢ s ≤ A * (1 + v) - 1` | closed |

### The equation

**R18 · `rw [List.prod_cons]`** changes the **goal**. Lemma: `(a :: l).prod = a * l.prod`.
Placeholders: `(x : ℝ) (xs : List ℝ)`.

| Before | After |
|---|---|
| `⊢ P (x :: xs).prod` | `⊢ P (x * xs.prod)` |

After R4, `rw [hfx]`, `rw [hq]` and R18 both sides are products of `x`, `xs.prod`, `1 + θ`, `1 + δ`; `ring` closes
the identity `x * (p * (1 + θ)) * (1 + δ) = x * p * (1 + (θ + δ + θ * δ))`.

### Worked combinations (W1, W2, on objects that are not the exercise's)

**W1.** `dbl [] = 1`, `dbl (_ :: xs) = 2 * dbl xs`, claim `dbl xs = 2 ^ xs.length`. `nil`: `simp [dbl]` (R4, R3).
`cons`: `rw [dbl, ih, List.length_cons, pow_succ]` (R4, `rw [ih]`, R15, R16), then `ring`.

**W2: composing two additive errors.** From `∃ δ, |δ| ≤ u ∧ y = x + δ` and `∃ ε, |ε| ≤ v ∧ z = y + ε`, prove
`∃ θ, |θ| ≤ u + v ∧ z = x + θ`. Two `obtain`s (R6) give this context; `refine ⟨δ + ε, ?_, ?_⟩` (R2) gives the two
goals:

```lean-goal
⊢ |δ + ε| ≤ u + v
⊢ z = x + (δ + ε)
```

The first is a `calc` (R8): `abs_add_le` (R9), then `gcongr` (it finds `hδ`, `hε` in the context). The second is
`rw [hz, hy]`, then `ring`. The relative-error step of the exercise has the same shape, with one more term
`θ * δ` and the product bound R12.

---

## Part 2 · `fprod_abs_error`

Statement: `|fprod fl xs - xs.prod| ≤ ((1 + u) ^ xs.length - 1) * |xs.prod|`. It follows from Part 1: take its
`θ` (R7 with R6 on `fprod_error u fl hfl xs`), rewrite `fprod fl xs` away (`rw [h]`), and pull the absolute
value apart.

**R19 · `rw [show a = b by tac]`** changes the **goal**: it rewrites with an equation proved on the spot. `a` must
appear literally in the goal. Placeholders: `(a b s : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a * (b + s) - a * b)` | `⊢ P (a * s)` |

**R20 · `rw [mul_comm]`** changes the **goal**. Lemma: `a * b = b * a`. Without arguments it swaps the first
product it finds (reading left to right), and every copy of that same product. `rw [mul_comm a b]` picks one.
Placeholders: `(a b c : ℝ) (P : ℝ → ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (a * b) (c * a)` | `⊢ P (b * a) (c * a)` |

Then R12: `gcongr` reduces `|θ| * c ≤ e * c` to `|θ| ≤ e` and `0 ≤ c`; both are closed for you (`hθ` from the
context, `0 ≤ |xs.prod|` by `positivity`).

**W3.** The same three rewrites on another term: R19, R10, R20.

```lean-goal
⊢ |x * (2 + θ) - 2 * x| = |θ| * |x|
⊢ |x * θ| = |θ| * |x|
⊢ |x| * |θ| = |θ| * |x|
```

The last goal is closed by `rw` itself (both sides are now the same).

---

## Traps

- **The model makes `n` roundings, hardware makes `n - 1`.** `fprod fl [x] = fl (x * 1)` rounds even the last
  factor, so the bound is `(1 + u)ⁿ - 1`. A real product of `n` numbers rounds `n - 1` times; the same proof with
  `fprod fl [x] = x` gives `(1 + u)ⁿ⁻¹ - 1` (Higham's `γₙ₋₁ ≈ (n - 1) u`).
- `RelErr u fl` forces `0 ≤ u` (take any `x`: the `δ` has `0 ≤ |δ| ≤ u`), but `positivity` does not know that.
  The side goal `0 ≤ (1 + u) ^ xs.length - 1` from R12 comes from `hθ` instead: `le_trans (abs_nonneg _) hθ`.
- `nlinarith` does not know the triangle inequality or `|θ * δ| = |θ| * |δ|`. Prove
  `|θ + δ + θ * δ| ≤ |θ| + |δ| + |θ| * |δ|` and `|θ| * |δ| ≤ ((1 + u) ^ xs.length - 1) * u` as `have`s first.
- Before `nlinarith`, turn `(x :: xs).length` and the power `^ (n + 1)` into `xs.length` and `^ n * (1 + u)`
  (R15, R16). Otherwise `(1 + u) ^ (xs.length + 1)` is one more unknown unrelated to `(1 + u) ^ xs.length`.
- `rw [hfx]` needs `fl (x * fprod fl xs)` literally in the goal: unfold `fprod` first (R4), and obtain `hfx` from
  `hfl (x * fprod fl xs)` with exactly that argument.
- `induction xs` before `obtain`ing anything about `xs`: the IH must be about the tail, not a fixed list.
- `t1 ; t2` runs `t2` on the first goal only. After `refine ⟨_, ?_, ?_⟩`, focus each goal with `·`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on a list | `induction xs with \| nil => … \| cons x xs ih => …` | R1 |
| prove `∃ θ, A θ ∧ B θ` | `refine ⟨w, ?_, ?_⟩` or `exact ⟨w, p, q⟩` | R2 |
| empty-list facts | `simp` (`List.length_nil`, `pow_zero`, `abs_zero`, `List.prod_nil`) | R3, R5 |
| unfold `fprod` on `[]` / `x :: xs` | `simp [fprod]` / `rw [fprod]` | R4 |
| use `∃ θ, A θ ∧ B θ` | `obtain ⟨θ, hA, hB⟩ := h` | R6 |
| instance of `hfl` or of a theorem | `obtain ⟨δ, hδ, hfx⟩ := hfl t` | R7 |
| chain of inequalities | `calc _ ≤ b := p` / `_ ≤ c := q` | R8 |
| `\|a + b\| ≤ \|a\| + \|b\|` | `abs_add_le a b` | R9 |
| `\|a * b\| → \|a\| * \|b\|` | `rw [abs_mul]` | R10 |
| monotonicity of `+`, `*` | `gcongr` | R11, R12 |
| `0 ≤ c` from `\|θ\| ≤ c` | `le_trans (abs_nonneg _) hθ` | R13, R14 |
| `(x :: xs).length`, `a ^ (n + 1)` | `rw [List.length_cons, pow_succ]` | R15, R16 |
| linear combination of facts | `nlinarith` (or `linarith`) | R17 |
| `(x :: xs).prod` | `rw [List.prod_cons]` | R18 |
| rewrite with an ad-hoc identity | `rw [show a = b by ring]` | R19 |
| swap a product | `rw [mul_comm]` | R20 |
| ring identity | `ring` | |
| see the state | infoview | |
