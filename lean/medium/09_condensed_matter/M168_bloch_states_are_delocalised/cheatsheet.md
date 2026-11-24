# M168 · Bloch states are delocalised: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's tight-binding chain
(`TightBindingChain`, its Hilbert space, the site states `|n⟩` and the Bloch states
`energyEigenstate`), Mathlib's complex inner product `⟪x, y⟫_ℂ`, finite sums `∑`, the complex
conjugate, and `Complex.exp`.

**The physics in one paragraph.** A chain of `N` sites with spacing `a`. The Hilbert space is `ℂ^N`
(`T.HilbertSpace`, physlib's `FiniteHilbertSpace (Fin T.N)`), with the orthonormal basis `|n⟩`
(`localizedState n`, "the electron sits on site `n`"). A Bloch state with wave number `k` is the plane
wave `ψ_k = ∑ₙ exp(i k n a) |n⟩`. Its amplitude on site `n` is `⟨n|ψ_k⟩ = exp(i k n a)`, a pure
phase, so `‖⟨n|ψ_k⟩‖ = 1` (Part 1) and `⟨ψ_k|ψ_k⟩ = ∑ₙ 1 = N` (Part 2).

## How to read an entry

Each entry is one tactic or one lemma used with `simp only`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal, including under a `∑`.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddGroup α]` is a
  requirement on `α` (a *type class*); each entry says which familiar types meet it.
- Inner-product entries use `{E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]`: `E` is a complex
  inner product space. `T.HilbertSpace` is one.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `T : TightBindingChain` | the chain's data: `T.N` sites (`T.N ≠ 0`), spacing `T.a > 0`, on-site energy `T.E0`, hopping `T.t` |
| `T.HilbertSpace` | `ℂ^(T.N)` with its standard inner product |
| `localizedState n` | the site state `\|n⟩` for `n : Fin T.N`; the notation `\|n⟩` is scoped, so the infoview prints the name |
| `T.QuantaWaveNumber` | the set of allowed wave numbers `2π/(a N) · (m − ⌊N/2⌋)`, a `Set ℝ` |
| `k : ↑T.QuantaWaveNumber` | `k` is an element of that set: a real number bundled with a proof it is allowed (a *subtype*) |
| `↑↑k` | `k` cast twice: subtype element → its real value → `ℂ` |
| `↑↑n` | `n : Fin T.N` cast twice: → `ℕ` → `ℂ` |
| `↑T.a`, `↑T.N` | the real `a` and the natural `N` cast into `ℂ` |
| `T.energyEigenstate k` | the Bloch state `∑ n, exp (I * k * n * a) • \|n⟩` |
| `⟪x, y⟫_ℂ` | the complex inner product, conjugate-linear in `x`, linear in `y` (physics convention `⟨x\|y⟩`) |
| `‖z‖` | the modulus of `z : ℂ`, a real number |
| `r • x` | scalar `r : ℂ` times vector `x` |
| `∑ i, f i` | the sum over all of a finite type (here `Fin T.N`); `∑ i ∈ s, f i` sums over a finite set `s` |
| `Finset.univ` | the set of all elements of a finite type |
| `Complex.I` | the imaginary unit `i` |
| `Complex.exp`, `Real.exp` | the complex and the real exponential |
| `z.re`, `z.im` | real and imaginary part of `z : ℂ` |
| `(starRingEnd ℂ) z` | Lean's name for the complex conjugate `conj z` |
| `if p then a else b` | `a` when `p` holds, else `b` (`p` must be decidable; equality on `Fin N` is) |
| `x`, `x_1`, `i` | bound variables `simp` invented for a sum's index (the definition calls it `n`) |
| `s.card • b`, `N • b` | `b` added to itself `s.card` (resp. `N`) times |

---

## Part 1 · `bloch_delocalized`

Statement: for every site `n`, `‖⟪|n⟩, ψ_k⟫_ℂ‖ = 1`. Unfold `ψ_k`, push the inner product through the
sum and the scalars, turn each `⟪|n⟩, |m⟩⟫` into an `if`, collapse the sum to its one surviving term
`exp (I * k * n * a)`, and show its modulus is `exp 0 = 1`.

### Unfold and push the inner product inside

**R1 · `simp only [TightBindingChain.energyEigenstate]`** changes the **goal**: the name of the Bloch state
is replaced by its body. Placeholders: `(T : TightBindingChain) (k : T.QuantaWaveNumber)`,
`P : T.HilbertSpace → Prop`.

| Before | After |
|---|---|
| `⊢ P (T.energyEigenstate k)` | `⊢ P (∑ n, Complex.exp (Complex.I * ↑↑k * ↑↑n * ↑T.a) • localizedState n)` |

**R2 · `inner_sum`** changes the **goal**: a sum in the right slot moves outside the inner product.
Lemma: `⟪x, ∑ i ∈ s, f i⟫_ℂ = ∑ i ∈ s, ⟪x, f i⟫_ℂ`. Placeholders: `{ι : Type} (s : Finset ι) (f : ι → E) (x : E)`.

| Before | After |
|---|---|
| `⊢ P ⟪x, ∑ i ∈ s, f i⟫_ℂ` | `⊢ P (∑ i ∈ s, ⟪x, f i⟫_ℂ)` |

**R3 · `inner_smul_right`** changes the **goal**: a scalar in the right slot comes out unchanged.
Lemma: `⟪x, r • y⟫_ℂ = r * ⟪x, y⟫_ℂ`. Placeholders: `(x y : E) (r : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ⟪x, r • y⟫_ℂ` | `⊢ P (r * ⟪x, y⟫_ℂ)` |

**R4 · `localizedState_orthonormal_eq_ite`** (physlib) changes the **goal**: orthonormality of the site
basis. Lemma: `⟨m|n⟩ = if m = n then 1 else 0`, where `⟨m|n⟩` is notation for
`⟪localizedState m, localizedState n⟫_ℂ`. Placeholders: `(T : TightBindingChain) (m n : Fin T.N)`. With
`open TightBindingChain` the short name works.

| Before | After |
|---|---|
| `⊢ P ⟪localizedState m, localizedState n⟫_ℂ` | `⊢ P (if m = n then 1 else 0)` |

### Collapse the sum

**R5 · `mul_ite`** changes the **goal**: a factor in front of an `if` moves into both branches.
Lemma: `(a * if p then b else c) = if p then a * b else a * c`. Placeholders:
`{α : Type} [Mul α] (p : Prop) [Decidable p] (a b c : α)`; `ℂ` qualifies.

| Before | After |
|---|---|
| `⊢ P (a * if p then b else c)` | `⊢ P (if p then a * b else a * c)` |

**R6 · `mul_one`, `mul_zero`** change the **goal**: `a * 1 = a`, `a * 0 = 0`. Placeholders:
`{α : Type} [MulZeroOneClass α] (a : α)` (`*` with `0` and `1`; `ℂ`, `ℝ`, `ℕ` qualify).

| Before | After |
|---|---|
| `⊢ P (if p then a * 1 else a * 0)` | `⊢ P (if p then a else 0)` |

**R7 · `Finset.sum_ite_eq`** changes the **goal**: a sum of a Kronecker delta keeps one term.
Lemma: `(∑ j ∈ s, if i = j then f j else 0) = if i ∈ s then f i else 0`. The summation variable `j`
must be on the **right** of `=`. Placeholders: `{ι β : Type} [DecidableEq ι] [AddCommMonoid β]
(s : Finset ι) (i : ι) (f : ι → β)`; `ι = Fin T.N`, `β = ℂ` qualify.

| Before | After |
|---|---|
| `⊢ P (∑ j ∈ s, if i = j then f j else 0)` | `⊢ P (if i ∈ s then f i else 0)` |

**R8 · `Finset.sum_ite_eq'`** changes the **goal**: the mirror of R7, summation variable on the **left**.
Lemma: `(∑ j ∈ s, if j = i then f j else 0) = if i ∈ s then f i else 0`. Same placeholders. Part 2 needs it
when all lemmas go into one `simp only` (W3).

| Before | After |
|---|---|
| `⊢ P (∑ j ∈ s, if j = i then f j else 0)` | `⊢ P (if i ∈ s then f i else 0)` |

**R9 · `Finset.mem_univ`, `if_true`** change the **goal**: `i ∈ Finset.univ` rewrites to `True`, and
`if True then a else b` to `a`. Placeholders: `{ι β : Type} [Fintype ι] [DecidableEq ι] (i : ι) (a b : β)`.

| Before | After |
|---|---|
| `⊢ P (if i ∈ Finset.univ then a else b)` | `⊢ P a` |

### The modulus of a phase

**R10 · `Complex.norm_exp`** changes the **goal**: the modulus of a complex exponential is the real
exponential of the real part. Lemma: `‖Complex.exp z‖ = Real.exp z.re`. Placeholders: `(z : ℂ)`,
`P : ℝ → Prop`.

| Before | After |
|---|---|
| `⊢ P ‖Complex.exp z‖` | `⊢ P (Real.exp z.re)` |

**R11 · `Complex.mul_re`** changes the **goal**: the real part of a product.
Lemma: `(z * w).re = z.re * w.re - z.im * w.im`. Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (z * w).re` | `⊢ P (z.re * w.re - z.im * w.im)` |

**R12 · `simp`** changes the **goal**: it computes the real part of `I` times real and natural casts down to
`0`. It uses R11, `Complex.mul_im`, `Complex.I_re : I.re = 0`, `Complex.I_im : I.im = 1`,
`Complex.ofReal_re : (↑r).re = r`, `Complex.ofReal_im : (↑r).im = 0`, `Complex.natCast_re`,
`Complex.natCast_im`, and ring clean-up (`zero_mul`, `sub_self`, …). Placeholders: `(x y : ℝ) (m : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Complex.I * ↑x * ↑m * ↑y).re` | `⊢ P 0` |

**R13 · `Real.exp_zero`** changes the **goal**: `Real.exp 0 = 1`.

| Before | After |
|---|---|
| `⊢ P (Real.exp 0)` | `⊢ P 1` |

So after R1–R9 the whole of Part 1 is `‖exp (I * ↑↑k * ↑↑n * ↑T.a)‖ = 1`, and `simp [Complex.norm_exp]`
does R10, R12, R13 in one call (W4 is the same on another phase).

---

## Part 2 · `bloch_norm_sq`

Statement: `⟪ψ_k, ψ_k⟫_ℂ = ↑T.N`. Now both slots hold a sum. Pull both sums out (R14, R2), both scalars
out (R15, R3), apply orthonormality (R4) and collapse the inner sum (R5–R9). Each remaining term is
`conj (exp z) * exp z` with `z = I * k * n * a`; turn it into `exp (conj z + z) = exp 0 = 1` (R16–R23),
then count (R24).

### Sum and scalar in the left slot

**R14 · `sum_inner`** changes the **goal**: the mirror of R2 for the left slot.
Lemma: `⟪∑ i ∈ s, f i, x⟫_ℂ = ∑ i ∈ s, ⟪f i, x⟫_ℂ`. Placeholders as R2.

| Before | After |
|---|---|
| `⊢ P ⟪∑ i ∈ s, f i, x⟫_ℂ` | `⊢ P (∑ i ∈ s, ⟪f i, x⟫_ℂ)` |

**R15 · `inner_smul_left`** changes the **goal**: a scalar in the left slot comes out **conjugated**
(the inner product is conjugate-linear in its first argument). Lemma:
`⟪r • x, y⟫_ℂ = (starRingEnd ℂ) r * ⟪x, y⟫_ℂ`. Placeholders: `(x y : E) (r : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ⟪r • x, y⟫_ℂ` | `⊢ P ((starRingEnd ℂ) r * ⟪x, y⟫_ℂ)` |

### Conjugates and exponentials

**R16 · `← Complex.exp_conj`** changes the **goal**: the conjugate moves inside the exponential.
Lemma: `Complex.exp (conj x) = conj (Complex.exp x)`, used right to left. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (Complex.exp z))` | `⊢ P (Complex.exp ((starRingEnd ℂ) z))` |

**R17 · `map_mul`** changes the **goal**: conjugation is multiplicative. Lemma: `f (x * y) = f x * f y` for any
multiplicative map `f`, here `f = starRingEnd ℂ`. Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (a * b))` | `⊢ P ((starRingEnd ℂ) a * (starRingEnd ℂ) b)` |

**R18 · `Complex.conj_I`** changes the **goal**: `conj I = -I`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) Complex.I)` | `⊢ P (-Complex.I)` |

**R19 · `Complex.conj_ofReal`, `map_natCast`** change the **goal**: casts of reals and naturals are their
own conjugates. Lemmas: `conj ↑r = ↑r` (`r : ℝ`) and `f ↑m = ↑m` for any ring map `f` (`m : ℕ`).
Placeholders: `(r : ℝ) (m : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) ↑r * (starRingEnd ℂ) ↑m)` | `⊢ P (↑r * ↑m)` |

**R20 · `neg_mul`** changes the **goal**: `-a * b = -(a * b)`. Placeholders:
`{α : Type} [Mul α] [HasDistribNeg α] (a b : α)` (a `*` that commutes with negation; `ℂ` qualifies). So
`conj (I * k * n * a) = -I * k * n * a` becomes `-(I * k * n * a)`.

| Before | After |
|---|---|
| `⊢ P (-a * b)` | `⊢ P (-(a * b))` |

**R21 · `← Complex.exp_add`** changes the **goal**: a product of exponentials becomes one exponential.
Lemma: `Complex.exp (x + y) = Complex.exp x * Complex.exp y`, used right to left. Placeholders: `(x y : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (Complex.exp x * Complex.exp y)` | `⊢ P (Complex.exp (x + y))` |

**R22 · `neg_add_cancel`, `add_neg_cancel`** change the **goal**: `-a + a = 0` and `a + -a = 0`.
Placeholders: `{α : Type} [AddGroup α] (a : α)`. Which one you need depends on the order of the factors `simp`
left: `conj (exp z) * exp z` gives `-z + z`, `exp z * conj (exp z)` gives `z + -z`.

| Before | After |
|---|---|
| `⊢ P (-a + a)` | `⊢ P 0` |
| `⊢ P (a + -a)` | `⊢ P 0` |

**R23 · `Complex.exp_zero`** changes the **goal**: `Complex.exp 0 = 1`.

| Before | After |
|---|---|
| `⊢ P (Complex.exp 0)` | `⊢ P 1` |

### Counting

**R24 · `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`, `nsmul_eq_mul`** change the **goal**: a
sum of `N` ones becomes `↑N * 1` (then R6). Lemmas: `∑ _x ∈ s, b = s.card • b`;
`Finset.univ.card = Fintype.card α`; `Fintype.card (Fin n) = n`; `n • a = ↑n * a`. Placeholders: `(N : ℕ)`.

| Before | After `Finset.sum_const` | After `Finset.card_univ` | After `Fintype.card_fin` | After `nsmul_eq_mul` |
|---|---|---|---|---|
| `⊢ P (∑ _x, 1)` | `⊢ P (Finset.univ.card • 1)` | `⊢ P (Fintype.card (Fin N) • 1)` | `⊢ P (N • 1)` | `⊢ P (↑N * 1)` |

`simp` applies R16–R24 by itself once you give it the two right-to-left lemmas, which it would never try on its
own: `simp [← Complex.exp_conj, ← Complex.exp_add]`.

### Worked combinations (W1–W5, on states that are not the exercise's)

**W1.** For any coefficients `c : Fin T.N → ℂ`, `⟪|m⟩, ∑ n, c n • |n⟩⟫_ℂ = c m`. R2, R3, R4 give

```lean-goal
⊢ (∑ x, c x * if m = x then 1 else 0) = c m
```

and R5, R6, R7, R9 close it.

**W2: left sum first.** `⟪∑ n, c n • |n⟩, ∑ n, c n • |n⟩⟫_ℂ`. After `simp only [sum_inner]` (R14), then
R15, R2, R3, R4 in one `simp only`, the `if` tests `x = x_1` with the inner summation variable `x_1` on the
right, so R7 applies:

```lean-goal
⊢ ∑ i, ⟪c i • localizedState i, ∑ n, c n • localizedState n⟫_ℂ = ∑ n, c n * (starRingEnd ℂ) (c n)
⊢ ∑ x, ∑ x_1, c x_1 * ((starRingEnd ℂ) (c x) * if x = x_1 then 1 else 0) = ∑ n, c n * (starRingEnd ℂ) (c n)
```

**W3: everything in one `simp only`.** Then `simp` pulls the **right** sum out first and the `if` comes out as
`x_1 = x`, summation variable on the left: R7 does nothing, R8 collapses it (and the goal closes).

```lean-goal
⊢ (∑ x, c x * ∑ x_1, (starRingEnd ℂ) (c x_1) * if x_1 = x then 1 else 0) = ∑ n, c n * (starRingEnd ℂ) (c n)
```

**W4.** `‖Complex.exp (↑x * Complex.I)‖ = 1` for `x : ℝ`: `simp [Complex.norm_exp]` (R10, R12, R13).

**W5.** `conj (exp (I x)) * exp (I x) = 1`, one family of rewrites per step: R16; R17, R18, R19, R20; R21;
R22, R23.

```lean-goal
⊢ (starRingEnd ℂ) (Complex.exp (Complex.I * ↑x)) * Complex.exp (Complex.I * ↑x) = 1
⊢ Complex.exp ((starRingEnd ℂ) (Complex.I * ↑x)) * Complex.exp (Complex.I * ↑x) = 1
⊢ Complex.exp (-(Complex.I * ↑x)) * Complex.exp (Complex.I * ↑x) = 1
⊢ Complex.exp (-(Complex.I * ↑x) + Complex.I * ↑x) = 1
```

---

## Traps

- `rw` cannot rewrite under a binder: inside `∑ n, …` the summand mentions the bound `n`, so
  `rw [inner_smul_right]` does not find the pattern. Use `simp only [...]`, which rewrites under binders.
- The inner product is conjugate-linear on the **left**: `inner_smul_left` produces `(starRingEnd ℂ) r`,
  `inner_smul_right` does not. Mixing them up gives a goal that is false.
- `Finset.sum_ite_eq` needs the summation variable on the right of `=`, `Finset.sum_ite_eq'` on the left. Which
  one you get depends on the order `simp` pulls the sums out (W2 vs W3). Give `simp` both, or use plain `simp`.
- `simp` never uses a lemma right to left unless you write `←`: without `← Complex.exp_add` it will not merge
  `exp x * exp y`, and without `← Complex.exp_conj` the conjugate stays outside the `exp`.
- `k` is not a real number but an element of a subtype; its value is `↑k`. In the goal it appears as `↑↑k`
  (then cast to `ℂ`). `Complex.ofReal_re` and `Complex.ofReal_im` handle that cast; nothing about `k`'s set
  membership is needed.
- `|n⟩` and `⟨m|n⟩` are scoped notations: they need `open TightBindingChain`, and the infoview prints
  `localizedState n` and `⟪localizedState m, localizedState n⟫_ℂ` instead.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold the Bloch state | `simp only [TightBindingChain.energyEigenstate]` | R1 |
| sum out of the right / left slot | `inner_sum` / `sum_inner` | R2, R14 |
| scalar out of the right / left slot | `inner_smul_right` / `inner_smul_left` (conjugates) | R3, R15 |
| `⟪\|m⟩, \|n⟩⟫` → Kronecker delta | `localizedState_orthonormal_eq_ite` | R4 |
| factor into an `if` | `mul_ite`, then `mul_one`, `mul_zero` | R5, R6 |
| collapse `∑ j, if i = j …` / `if j = i …` | `Finset.sum_ite_eq` / `Finset.sum_ite_eq'` | R7, R8 |
| `if i ∈ univ …` → its branch | `Finset.mem_univ, if_true` | R9 |
| `‖exp z‖` | `Complex.norm_exp` (`= Real.exp z.re`) | R10 |
| real part of `I * reals` | `simp` (`Complex.mul_re`, `I_re`, `ofReal_re`, …) | R11, R12 |
| `exp 0` | `Real.exp_zero` / `Complex.exp_zero` | R13, R23 |
| `conj (exp z)` → `exp (conj z)` | `← Complex.exp_conj` | R16 |
| conjugate of a product / `I` / casts | `map_mul`, `Complex.conj_I`, `Complex.conj_ofReal`, `map_natCast` | R17–R19 |
| `exp x * exp y` → `exp (x + y)` | `← Complex.exp_add` | R21 |
| `-a + a` / `a + -a` | `neg_add_cancel` / `add_neg_cancel` | R22 |
| `∑ _x : Fin N, 1` → `↑N` | `Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul` | R24 |
| finish after the inner-product step | `simp [Complex.norm_exp]` / `simp [← Complex.exp_conj, ← Complex.exp_add]` | |
| see the state | infoview | |
