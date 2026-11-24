# H086 · Grover's amplitude formula: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): functions, `if … then … else`, recursion and induction on
`Nat`, `rw`, `simp`, `exact`, `have`. **New here:** Mathlib's real numbers `ℝ` and the cast `ℕ → ℝ`,
`Real.sqrt`, `Real.sin`/`Real.cos`/`Real.arcsin`, finite sums `∑` over `Fin N`, and the Mathlib closers
`positivity`, `linarith`, `field_simp`, `linear_combination`, `push_cast`, `exact_mod_cast`.

The math. Write `θ = arcsin(1/√N)`, so `sin θ = 1/√N` and `cos θ = √(N−1)/√N`. A state of the form
"`a` at `m`, `b` at every other index" stays of that form under one Grover step, and `(a, b)` changes
linearly (milestone `step_form`). In the coordinates `a = sin φ`, `b = cos φ / √(N−1)` that linear map is the
rotation `φ ↦ φ + 2θ` (`rot_sin`, `rot_cos`). The start state `1/√N` everywhere is `φ = θ`, so after `k`
steps `φ = (2k+1)θ`: induction on `k`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` (or `Q`) is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. `G : Prop` is a goal the step does not touch.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid M]`
  is a requirement on `M` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin N` | the type `{0, 1, …, N−1}`; `m : Fin N` is the marked index |
| `Fin N → ℝ` | a real vector of length `N` (an amplitude vector); `v i` is its entry `i` |
| `↑N`, `↑k` | the natural number `N` cast into `ℝ`. In `Real.sqrt (N - 1)` the `N` is cast first, so `↑N - 1` is real subtraction (no truncation at 0) |
| `↑(k + 1)` | the cast of the natural number `k + 1`; `push_cast` turns it into `↑k + 1` (R36) |
| `√x` | `Real.sqrt x`, the nonnegative square root (Mathlib sets `√x = 0` for `x < 0`). The spec writes `Real.sqrt`, the infoview prints `√` |
| `√↑N`, `1 / √↑N` | `Real.sqrt` of the cast `↑N`: the real number `√N` and the start amplitude `1/√N` |
| `Real.sin φ`, `Real.cos φ` | sine and cosine `ℝ → ℝ` (radians); Lean prints the full names |
| `Real.arcsin x` | inverse sine, valued in `[−π/2, π/2]`; for `x ∉ [−1, 1]` it is a junk value, hence the side goals of R17. `Real.arcsin (1 / √↑N)` is the angle `θ` |
| `∑ j, v j` | `∑ j ∈ Finset.univ, v j`: the sum over all `j : Fin N` |
| `∑ i ∈ s, f i` | the sum over a finite set `s : Finset ι` |
| `Finset.univ` | the finite set of all elements of a finite type (`[Fintype ι]`) |
| `s.card`, `Fintype.card α` | number of elements of the finite set `s` / of the finite type `α` |
| `n • a` | `n : ℕ` times `a` as repeated addition (`a + ⋯ + a`); R10 turns it into `↑n * a` |
| `oracle m v`, `diffuse v` | the problem's oracle (negate entry `m`) and diffusion (`vᵢ ↦ 2·(∑ v)/N − vᵢ`) |
| `grover m k` | the state after `k` Grover steps, defined by recursion on `k` |
| `diffuse (oracle m fun i => …) i` | `diffuse (oracle m (fun i => …)) i`: Lean drops the parentheses around a `fun` that is the last argument |
| `case left`, `case right` | the two goals of `constructor` on `A ∧ B` |
| `case left.hx₁`, `case left.hx₂` | the two side goals `-1 ≤ x`, `x ≤ 1` that `apply Real.sin_arcsin` leaves (R17), named after the lemma's hypotheses |
| `case pos`, `case neg` | the two goals of `by_cases` / `split_ifs`: the condition holds / fails |
| `h✝` | an inaccessible hypothesis Lean named itself (from `split_ifs`); you cannot type it |
| `case zero`, `case succ` | base case and inductive step of `induction` |

---

## Part 1 · `step_form` (milestone)

Statement: applying the oracle and then the diffusion to "`a` at `m`, `b` elsewhere" gives
"`a(1 − 2/N) + 2(N−1)/N · b` at `m`, `−(2/N)a + (1 − 2/N)b` elsewhere". The key fact is the sum after the
oracle, `∑ j, oracle m (…) j = −a + (N−1)·b`: write each summand as a constant plus a spike at `m`.

### Functions and case splits

**R1 · `funext i`** changes the **goal and the context**: an equation of functions becomes an equation of
values at a new variable `i`. Placeholders: `{α β : Type} (f g : α → β)`.

| Before | After |
|---|---|
| `⊢ f = g` | `i : α ⊢ f i = g i` |

**R2 · `by_cases h : p`** changes the **goal list**: one goal becomes two, one with `h : p` and one with
`h : ¬p`. Placeholders: `(p G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h : p ⊢ G`, `h : ¬p ⊢ G` |

**R3 · `simp [h]` on an `if`** changes the **goal**: with `h : p` in hand, `simp` picks the `then` branch
(lemma `if_pos : p → (if p then x else y) = x`); with `h : ¬p`, the `else` branch (`if_neg`). Add the
definitions to unfold: `simp [oracle, h]`. Placeholders: `{α : Type} (p : Prop) [Decidable p] (x y : α)`
(`[Decidable p]`: Lean can evaluate `p`; `i = m` on `Fin N` qualifies).

| Before | After (`h : p`) | After (`h : ¬p`) |
|---|---|---|
| `⊢ Q (if p then x else y)` | `⊢ Q x` | `⊢ Q y` |

### Finite sums

All of R4–R10 can go into one `simp only [helper, R4, R5, R6, R7, R8, R9, R10]` (W1). Placeholders for the
sums: `{ι M : Type} [AddCommMonoid M] (s : Finset ι)`. `[AddCommMonoid M]` means `M` has `+` and `0` with
`+` commutative; `ℝ` qualifies.

**R4 · `Finset.sum_add_distrib`** changes the **goal**: `∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i`.
Placeholders: `(f g : ι → M)`. Lean renames the bound variable to `x`; that is only a name.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, (f i + g i))` | `⊢ P (∑ x ∈ s, f x + ∑ x ∈ s, g x)` |

**R5 · `Finset.sum_ite_eq'`** changes the **goal**: a sum that is `0` except at one index collapses,
`(∑ i ∈ s, if i = a then b i else 0) = if a ∈ s then b a else 0`. The primed version has the bound
variable on the **left** of `=` (`i = a`); unprimed `Finset.sum_ite_eq` is for `a = i`. Placeholders:
`[DecidableEq ι] (a : ι) (b : ι → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, if i = a then b i else 0)` | `⊢ P (if a ∈ s then b a else 0)` |

**R6 · `simp only [Finset.mem_univ, if_true]`** changes the **goal**: `Finset.mem_univ : a ∈ Finset.univ`
turns the guard into `True`, and `if_true : (if True then x else y) = x` drops the `if`. Placeholders:
`{ι M : Type} [Fintype ι] [DecidableEq ι] (a : ι) (x y : M)`.

| Before | After |
|---|---|
| `⊢ P (if a ∈ Finset.univ then x else y)` | `⊢ P x` |

**R7 · `Finset.sum_const`** changes the **goal**: `∑ _i ∈ s, c = s.card • c`. Placeholders: `(c : M)`.

| Before | After |
|---|---|
| `⊢ P (∑ _i ∈ s, c)` | `⊢ P (s.card • c)` |

**R8 · `Finset.card_univ`** changes the **goal**: `Finset.univ.card = Fintype.card α`. Placeholders:
`{α : Type} [Fintype α]`.

| Before | After |
|---|---|
| `⊢ P Finset.univ.card` | `⊢ P (Fintype.card α)` |

**R9 · `Fintype.card_fin`** changes the **goal**: `Fintype.card (Fin n) = n`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Fintype.card (Fin n))` | `⊢ P n` |

**R10 · `nsmul_eq_mul`** changes the **goal**: `n • a = ↑n * a`. Placeholders: `(n : ℕ) (a : ℝ)` (any
semiring works in place of `ℝ`).

| Before | After |
|---|---|
| `⊢ P (n • a)` | `⊢ P (↑n * a)` |

### Denominators `/ ↑N`

**R11 · `Fin.pos`** changes the **context**: `Fin.pos (i : Fin n) : 0 < n`. Any `m : Fin N` proves `0 < N`;
write `have := m.pos`. Placeholders: `(n : ℕ) (i : Fin n)`.

| Before | After |
|---|---|
| `⊢ G` | `hn : 0 < n ⊢ G` |

**R12 · `positivity`** **closes** goals `0 < e`, `0 ≤ e`, `e ≠ 0` by the shape of `e` (sums, products,
quotients, powers and square roots of positive things). For a bare variable such as `↑N` it needs a
hypothesis like `0 < N` in the context (R11). It does not do subtraction: `0 < ↑N - 1` is a `linarith` job.

**R13 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero, using
hypotheses `x ≠ 0` or `0 < x` from the context, and leaves an equation without `/`. Put those facts in the
context first. Placeholders: `(a b c x : ℝ) (hx : x ≠ 0)`. Its output order is its own (`x * b`, not `b * x`):
read the new goal before you continue.

| Before | After |
|---|---|
| `hx : x ≠ 0 ⊢ a / x + b = c` | `⊢ a + x * b = x * c` |

### Worked combination

**W1: a sum "constant plus one spike" over `Fin n`.** One `simp only` with R4–R10 closes

```lean-goal
⊢ ∑ j, (b + if j = j₀ then c else 0) = ↑n * b + c
```

In `step_form` the summands are not yet in this form: first prove the pointwise helper
`∀ j, oracle m (…) j = b + (if j = m then -a - b else 0)` (R2, R3), put it first in the `simp only` list,
and finish with `ring`.

---

## Part 2 · `sin_cos_theta` (milestone)

Statement: `sin (arcsin (1/√N)) = 1/√N` and `cos (arcsin (1/√N)) = √(N−1)/√N` for `N ≥ 2`.

**R14 · `exact_mod_cast h`** **closes** a goal that is `h` with casts inserted. Turn `hN : 2 ≤ N` (in `ℕ`)
into `(2 : ℝ) ≤ ↑N`, which `linarith` can use. Placeholders: `(n : ℕ) (h : 2 ≤ n)`.

| Before | After |
|---|---|
| `h : 2 ≤ n ⊢ 2 ≤ ↑n` | closed |

**R15 · `Real.one_le_sqrt`** changes the **goal**: `1 ≤ √x ↔ 1 ≤ x`, used with `rw`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ 1 ≤ √x` | `⊢ 1 ≤ x` |

**R16 · `linarith`** **closes** a linear equality or inequality over `ℝ` (or `<`, `≤` chains) that follows
from hypotheses by adding nonnegative multiples of them. It treats `√x`, `sin φ`, `x * y` as atoms.

**R17 · `apply Real.sin_arcsin`** changes the **goal list**. The lemma is
`-1 ≤ x → x ≤ 1 → sin (arcsin x) = x`; `apply` matches the conclusion and leaves the two bounds. For
`x = 1/√N`: the lower bound from `0 < 1/√N` (R12) and `linarith`; the upper from R18.

| Before | After |
|---|---|
| `⊢ Real.sin (Real.arcsin x) = x` | `⊢ -1 ≤ x`, `⊢ x ≤ 1` |

**R18 · `div_le_one`** changes the **goal**: `0 < b → (a / b ≤ 1 ↔ a ≤ b)`. Write
`rw [div_le_one (by positivity)]` to prove `0 < b` on the spot. Placeholders: `(a b : ℝ) (hb : 0 < b)`
(any ordered field).

| Before | After |
|---|---|
| `⊢ a / b ≤ 1` | `⊢ a ≤ b` |

**R19 · `Real.cos_arcsin`** changes the **goal**: `cos (arcsin x) = √(1 - x ^ 2)`, for every `x` (no side
goal). Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.cos (Real.arcsin x))` | `⊢ P √(1 - x ^ 2)` |

**R20 · `div_pow`** changes the **goal**: `(a / b) ^ n = a ^ n / b ^ n`. Placeholders: `(a b : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((a / b) ^ n)` | `⊢ P (a ^ n / b ^ n)` |

**R21 · `Real.sq_sqrt`** changes the **goal**: `0 ≤ x → √x ^ 2 = x`. Pass the side condition:
`Real.sq_sqrt (by linarith)`. Also the way to state the facts `√(N−1) ^ 2 = N − 1` and `√N ^ 2 = N` of Part 3.
Placeholders: `(x : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `⊢ P (√x ^ 2)` | `⊢ P x` |

**R22 · `one_pow`** changes the **goal**: `1 ^ n = 1`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (1 ^ n)` | `⊢ P 1` |

**R23 · `rw [show a = b by tac]`** changes the **goal**: rewrite with an equation you prove inline. Here
`1 − 1/x = (x − 1)/x`, proved by `field_simp` (R13), which needs `x ≠ 0`. In the exercise the context
holds `(2 : ℝ) ≤ ↑N`, from which `field_simp`'s side-condition prover gets `↑N ≠ 0` itself; if it does not,
add `(N : ℝ) ≠ 0` to the context. Placeholders: `(x : ℝ) (hx : x ≠ 0)`.

| Before | After |
|---|---|
| `⊢ P (1 - 1 / x)` | `⊢ P ((x - 1) / x)` |

**R24 · `Real.sqrt_div`** changes the **goal**: `0 ≤ x → ∀ y, √(x / y) = √x / √y`. Only the numerator needs
`0 ≤`: `Real.sqrt_div (by linarith)`. Placeholders: `(x y : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `⊢ P √(x / y)` | `⊢ P (√x / √y)` |

The cosine half is one `rw [R19, R20, R21, R22, R23, R24]` chain; the last rewrite leaves both sides equal,
so `rw` closes it.

---

## Part 3 · `rot_sin`, `rot_cos` (milestones)

Statements: with `θ = arcsin(1/√N)`, the new marked amplitude `sin φ (1 − 2/N) + 2(N−1)/N · cos φ/√(N−1)` is
`sin (φ + 2θ)`, and the new unmarked one is `cos (φ + 2θ)/√(N−1)`. Expand the right side, substitute
`sin θ`, `cos θ` (Part 2), clear denominators, and finish with the one nonlinear fact `√(N−1)^2 = N−1`.

**R25 · `obtain ⟨hs, hc⟩ := h`** changes the **context**: a conjunction `h : A ∧ B` becomes two hypotheses.
Use it on `sin_cos_theta hN`. Placeholders: `(A B G : Prop) (h : A ∧ B)`.

| Before | After |
|---|---|
| `h : A ∧ B ⊢ G` | `hs : A, hc : B ⊢ G` |

**R26 · `Real.sqrt_pos`** is the iff `0 < √x ↔ 0 < x`; `Real.sqrt_pos.mpr hx` is a proof of `0 < √x` from
`hx : 0 < x`. Changes the **context** when used in a `have`. `field_simp` (R13) needs `0 < √(N−1)` and
`0 < √N` in the context to clear those denominators. Placeholders: `(x : ℝ) (hx : 0 < x)`.

| Before | After |
|---|---|
| `⊢ G` | `h3 : 0 < √x ⊢ G` |

**R27 · `Real.sin_add`** changes the **goal**: `sin (x + y) = sin x * cos y + cos x * sin y`.
Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.sin (x + y))` | `⊢ P (Real.sin x * Real.cos y + Real.cos x * Real.sin y)` |

**R28 · `Real.cos_add`** changes the **goal**: `cos (x + y) = cos x * cos y - sin x * sin y`.

| Before | After |
|---|---|
| `⊢ P (Real.cos (x + y))` | `⊢ P (Real.cos x * Real.cos y - Real.sin x * Real.sin y)` |

**R29 · `Real.sin_two_mul`** changes the **goal**: `sin (2 * x) = 2 * sin x * cos x`.

| Before | After |
|---|---|
| `⊢ P (Real.sin (2 * x))` | `⊢ P (2 * Real.sin x * Real.cos x)` |

**R30 · `Real.cos_two_mul`** changes the **goal**: `cos (2 * x) = 2 * cos x ^ 2 - 1`. Use this form, not
`cos² − sin²`: then only `cos θ` appears, and after substituting `hc` the only root left to square is
`√(N−1)`.

| Before | After |
|---|---|
| `⊢ P (Real.cos (2 * x))` | `⊢ P (2 * Real.cos x ^ 2 - 1)` |

**R31 · `linear_combination e * h`** **closes** a goal `L = R` given `h : l = r` when
`L − R − e·(l − r)` is `0` by `ring`. `e` is any expression. Use it when `ring` fails only because it does
not know `h` (here `h1 : √(N−1) ^ 2 = N − 1`). To find `e`: expand `L − R`; it is a multiple of
`√(N−1)^2 − (N−1)`, and the multiplier is `e`. Placeholders: `(s x y : ℝ) (h : s ^ 2 = x)`.

| Before | After |
|---|---|
| `h : s ^ 2 = x ⊢ y * s ^ 2 + 1 = y * x + 1` | closed by `linear_combination y * h` |

### Worked combinations

**W2: rotation by a double angle.** `rw [Real.sin_add, Real.sin_two_mul, Real.cos_two_mul, hs, hc]` turns
`sin (φ + 2α)` into an expression in `sin φ`, `cos φ`, `s`, `c` (R27, R29, R30, then the two hypotheses).
In the exercise the next steps are `field_simp`, `rw [h2]`, `linear_combination`.

**W3: a root in the denominator.** For `x / √x = √x` with `h1 : √x ^ 2 = x` and `h3 : 0 < √x` in the
context, `field_simp` (R13) leaves

```lean-goal
⊢ x = √x ^ 2
```

and `linear_combination -h1` (R31) closes it.

---

## Part 4 · `grover_amplitude` (the spec theorem)

Statement: `grover m k` is "`sin ((2k+1)θ)` at `m`, `cos ((2k+1)θ)/√(N−1)` elsewhere". Induct on `k`; the
base case is Part 2, the step is `step_form` followed by `rot_sin`, `rot_cos`.

**R32 · `induction k with | zero => … | succ k ih => …`** changes the **goal list**: the base case
`k = 0` and the step, with the induction hypothesis `ih` for `k`. In the guide the alternatives are
`?_`, which leaves both goals open. Placeholders: `(Q : ℕ → Prop) (k : ℕ)`.

| Before | After |
|---|---|
| `⊢ Q k` | `⊢ Q 0`, `k : ℕ, ih : Q k ⊢ Q (k + 1)` |

**R33 · `simp only [f]` / `rw [f]`** on a function `f` defined by pattern matching changes the **goal**:
`f 0` or `f (k + 1)` becomes the right side of that clause. Here `seq c 0 = c`, `seq c (k + 1) = 2 * seq c k`
(`seq` is a guide definition, not the exercise's). `rw [f]` only fires on a literal `0` or `k + 1`.
Placeholders: `(c : ℝ) (k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (seq c 0)` | `⊢ P c` |
| `⊢ P (seq c (k + 1))` | `⊢ P (2 * seq c k)` |

**R34 · `simp only [Nat.cast_zero, mul_zero, zero_add, one_mul]`** changes the **goal**: the base case has
`(2 * ↑0 + 1) * θ`; `Nat.cast_zero : ((0 : ℕ) : ℝ) = 0`, then `2 * 0 = 0`, `0 + 1 = 1`, `1 * θ = θ`. Add
`hs, hc` to the same list to substitute `sin θ` and `cos θ`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((2 * ↑0 + 1) * x)` | `⊢ P x` |

**R35 · `split_ifs`** changes the **goal list**: a goal containing `if p then x else y` becomes one goal per
branch, with `h✝ : p` or `h✝ : ¬p`. Write `split_ifs with h` to name the hypothesis. Placeholders:
`{α : Type} (p : Prop) [Decidable p] (x y : α)`.

| Before | After |
|---|---|
| `⊢ Q (if p then x else y)` | `h✝ : p ⊢ Q x`, `h✝ : ¬p ⊢ Q y` |

**R36 · `push_cast`** changes the **goal**: casts move inward through `+`, `*`, numerals:
`↑(k + 1) = ↑k + 1`. Then `ring` can compare `(2(k+1)+1)θ` with `(2k+1)θ + 2θ`. Placeholders: `(k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑(k + 1)` | `⊢ P (↑k + 1)` |

**R37 · `rw [← hf]`** with `hf : ∀ φ, f φ = g (φ + c)` changes the **goal**: Lean finds an instance of
the right side `g (?φ + c)` in the goal, fixes `φ` by matching, and replaces it by the left side. This is how
`rw [← rot_sin hN, ← rot_cos hN]` turns `sin (φ + 2θ)` back into the step formula, and how
`rw [step_form]` finds its `a` and `b`. The goal must contain `φ + c` literally (as a sum), hence the
`have e : … = (2k+1)θ + 2θ` first. Placeholders: `(f g : ℝ → ℝ) (c x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (g (x + c))` | `⊢ P (f x)` |

### Worked combination

**W4: a closed form by induction.** `seq c k = 2 ^ k * c`: induct (R32); base case `simp only [seq, pow_zero,
one_mul]` (R33 plus clean-up lemmas in the R34 style); step `rw [seq, ih]` (R33, then the IH), then `ring`.
Starting goal:

```lean-goal
⊢ seq c k = 2 ^ k * c
```

---

## Traps

- `Real.sqrt (N - 1)` is `√(↑N - 1)`: real subtraction, so `0 ≤ ↑N - 1` comes from `(2 : ℝ) ≤ ↑N` by
  `linarith`, not from `omega`. Get `(2 : ℝ) ≤ ↑N` once with `exact_mod_cast hN` (R14).
- `field_simp` only clears a denominator it can prove nonzero from the context. State `0 < √(N - 1)`,
  `0 < √N` (R26) and, for `/ ↑N`, `(N : ℝ) ≠ 0` (R11, R12) **before** calling it.
- `field_simp` chooses its own normal form, often with `√N ^ 2` left over. `rw [h2]` with
  `h2 : √N ^ 2 = N`, then read the goal and find the multiplier of `h1` for `linear_combination` (R31).
- `Finset.sum_ite_eq` vs `Finset.sum_ite_eq'`: the primed one is for `if j = m` (bound variable on the left).
- `rw [e]` fails if `e`'s left side is not literally in the goal: after `rw [grover, ih, step_form]; funext i`
  the angle is `(2 * ↑(k + 1) + 1) * θ`, with the cast outside the `+ 1`. State `e` with exactly that
  left side and prove it by `push_cast; ring` (R36).
- `Real.arcsin x` is junk outside `[−1, 1]`: `Real.sin_arcsin` asks for both bounds (R17); `Real.cos_arcsin`
  holds everywhere (R19).
- The base case `grover m 0` unfolds with `simp only [grover]` (R33), giving `1 / √↑N` on the left. Its
  `else` branch is `√(↑N - 1) / √↑N / √(↑N - 1)`, which needs `field_simp` with `0 < √(N - 1)` in context.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| function equation → pointwise | `funext i` | R1 |
| case on `i = m` | `by_cases h : i = m` | R2 |
| resolve `if` with `h` | `simp [oracle, h]` | R3 |
| `∑ (f + g)` split | `Finset.sum_add_distrib` | R4 |
| `∑ if j = m then b j else 0` | `Finset.sum_ite_eq'`, then `Finset.mem_univ, if_true` | R5, R6 |
| `∑ j : Fin N, c = ↑N * c` | `Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul` | R7–R10 |
| `0 < N` from `m : Fin N` | `have := m.pos` | R11 |
| `0 < e`, `e ≠ 0` | `positivity` | R12 |
| clear denominators | `field_simp` (nonzero facts in context first) | R13 |
| `ℕ` fact → `ℝ` fact | `exact_mod_cast hN` | R14 |
| `1 ≤ √x` | `rw [Real.one_le_sqrt]` | R15 |
| linear arithmetic | `linarith` | R16 |
| `sin (arcsin x) = x` | `apply Real.sin_arcsin` | R17 |
| `a / b ≤ 1` | `rw [div_le_one (by positivity)]` | R18 |
| `cos (arcsin x)` | `Real.cos_arcsin` | R19 |
| `(a / b) ^ n`, `√x ^ 2`, `1 ^ n` | `div_pow`, `Real.sq_sqrt (by linarith)`, `one_pow` | R20–R22 |
| inline equation | `rw [show a = b by field_simp]` | R23 |
| `√(x / y)` | `Real.sqrt_div (by linarith)` | R24 |
| split `h : A ∧ B` | `obtain ⟨hs, hc⟩ := h` | R25 |
| `0 < √x` | `Real.sqrt_pos.mpr (by linarith)` | R26 |
| expand `sin`/`cos` of sums, doubles | `Real.sin_add`, `Real.cos_add`, `Real.sin_two_mul`, `Real.cos_two_mul` | R27–R30 |
| `ring` up to `h1 : √(N-1)^2 = N-1` | `linear_combination e * h1` | R31 |
| induction on `k` | `induction k with \| zero => … \| succ k ih => …` | R32 |
| unfold `grover m 0` / `grover m (k+1)` | `simp only [grover, …]` / `rw [grover]` | R33 |
| `(2 * ↑0 + 1) * θ → θ` | `simp only [Nat.cast_zero, mul_zero, zero_add, one_mul]` | R34 |
| split the `if` in the goal | `split_ifs` | R35 |
| `↑(k + 1) → ↑k + 1` | `push_cast` | R36 |
| rewrite backwards with a `∀` milestone | `rw [← rot_sin hN, ← rot_cos hN]` | R37 |
| see the state | infoview | |
