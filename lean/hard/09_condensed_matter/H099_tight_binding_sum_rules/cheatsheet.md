# H099 · Tight-binding sum rules: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033: `rw`, `simp`, `have`, `intro`, `rcases`, `calc`, `omega`).
**New here:** Mathlib's complex numbers `ℂ` (`Complex.exp`, `Complex.I`, `.re`), real numbers cast into
`ℂ`, roots of unity (`IsPrimitiveRoot`), finite sums `∑` over `Fin N` and over `Finset.range N`, the
tactics `set`, `congr 1`, `push_cast`, `field_simp`, `ring_nf`, and physlib's `TightBindingChain`.

**The physics in one line.** A ring of `N` sites with spacing `a`, on-site energy `E0` and hopping `t`.
Its Bloch eigenstates have wavenumbers $k_n = \frac{2\pi}{aN}(n - m)$ for $n = 0, \dots, N-1$, with
$m = \lfloor N/2 \rfloor$ (so that $k_n$ lies in the Brillouin zone), and energies
$E(k) = E_0 - 2t\cos(ka)$. Write $\theta_n = k_n a = \frac{2\pi}{N}(n - m)$. Then

- $\sum_n E(k_n) = N E_0 - 2t \sum_n \cos\theta_n$ and
- $\sum_n (E(k_n) - E_0)^2 = 4t^2 \sum_n \cos^2\theta_n = 2Nt^2 + 2t^2 \sum_n \cos 2\theta_n$,

so both rules follow from the discrete Fourier orthogonality $\sum_n \cos(j\theta_n) = 0$ for $N \nmid j$
(milestone `sum_cos`), with $j = 1$ and $j = 2$. That in turn is the real part of a geometric sum
$e^{-2\pi i j m/N}\sum_{n<N} \zeta^n$ with $\zeta = e^{2\pi i j/N} \ne 1$ and $\zeta^N = 1$, which is $0$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G` with a function `g : T → G` means "any goal you can finish once you have `T`".
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Ring α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it; in this problem the
  values live in `ℕ`, `ℝ` or `ℂ`, and `ℝ`, `ℂ` meet every bracket used here.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `TightBindingChain` | physlib's structure with fields `N : ℕ` (sites), `a : ℝ` (spacing), `a_pos : 0 < a`, `E0 t : ℝ`, and an instance `NeZero N` (`N ≠ 0`) |
| `T.N`, `T.a`, `T.E0`, `T.t` | the fields of `T : TightBindingChain` |
| `T.QuantaWaveNumber` | a `Set ℝ`: the allowed wavenumbers `2π/(aN) · (n − ⌊N/2⌋)`, `n : Fin T.N` |
| `k : ↑T.QuantaWaveNumber` | an element of that set, as a type (a *subtype*): a pair `⟨x, proof x ∈ set⟩` |
| `↑k` (for such `k`), `(k : ℝ)` | its value `x : ℝ` (`Subtype.val k`) |
| `{x : ℝ \| 0 < x}` (R27) | set-builder notation: the set of reals with the property; used as a type it is the subtype above |
| `T.energyEigenvalue k` | `T.E0 - 2 * T.t * Real.cos (↑k * T.a)` (R31) |
| `Fin N` | `{0, …, N − 1}`; `(n : ℝ)` or `↑↑n` for `n : Fin N` is its value cast to `ℕ`, then to `ℝ` |
| `(T.N / 2 : ℕ)`, `↑(T.N / 2)` | natural-number division, rounded down (`⌊N/2⌋`), then cast to `ℝ` |
| `↑x` for `x : ℝ` in a complex goal | `x` cast into `ℂ` (`Complex.ofReal x`) |
| `↑n` for `n : ℕ` | `n` cast into `ℝ` or `ℂ` (`Nat.cast`); `↑1` is the cast of the natural `1`, not yet the numeral `1` |
| `Real.pi`, `↑Real.pi` | π, and π cast into `ℂ` |
| `Complex.I`, `Complex.exp z`, `z.re` | $i$, $e^z$, the real part of `z` |
| `IsPrimitiveRoot ζ k` | `ζ ^ k = 1`, and `ζ ^ l = 1` only when `k ∣ l` (ζ has order exactly `k`) |
| `∑ i, f i` | the sum of `f i` over all `i` of a finite type (here `Fin N`); short for `∑ i ∈ Finset.univ, f i` |
| `∑ i ∈ Finset.range n, f i` | the sum over the natural numbers `0, …, n − 1` |
| `s.card`, `Finset.univ.card`, `Fintype.card (Fin n)` | the number of elements of a finite set, of all of a type, of `Fin n` (that is `n`) |
| `n • a` | `n`-fold sum `a + ⋯ + a` (`n : ℕ`), the result of `Finset.sum_const` |
| `z : M := a ^ j` | a local definition made by `set`: `z` is a name for `a ^ j` |
| `x✝ : i ∈ Finset.univ` | an unnamed (`✝`) hypothesis, always true and unused |
| `hN : N > 0` | `0 < N`, printed with `>` |
| `inst✝ : Ring α` | a type-class assumption from a `[…]` binder |
| `case inl`, `case inr` | the two goals of `rcases … with … | …` (left and right disjunct) |
| `case h1`, `case h2` | the two hypotheses of a lemma used with `apply`, as goals (R29) |

---

## Part 1 · `sum_cos` (milestone)

Statement: for naturals `N m j` with `hj : ¬ N ∣ j`,
`∑ n : Fin N, Real.cos (2 * Real.pi * j / N * ((n : ℝ) - m)) = 0`. Proved once, used by Parts 3 and 4.

### Step 1: the case `N = 0`

**R1 · `rcases Nat.eq_zero_or_pos N with rfl | hN`** changes the **goal list**. `Nat.eq_zero_or_pos N :
N = 0 ∨ 0 < N`; the pattern `rfl` substitutes `N := 0` everywhere in the first goal, `hN` names the fact in
the second. Placeholders: `(P : ℕ → Prop) (N : ℕ)`.

| Before | After |
|---|---|
| `N : ℕ ⊢ P N` | `⊢ P 0`, `hN : N > 0 ⊢ P N` |

**R2 · `Fin.sum_univ_zero`** changes the **goal**: a sum over `Fin 0` has no terms, so it is `0`. `simp`
uses it by itself, so `· simp` closes the `N = 0` case. Placeholders:
`{β : Type} [AddCommMonoid β] (f : Fin 0 → β)` (β has `+` and `0`; `ℝ`, `ℂ` qualify).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P 0` |

### Step 2: the root of unity

**R3 · `h.ne'`** (`LT.lt.ne'`) changes the **context** when used in a `have`: from `h : 0 < n` it gives
`n ≠ 0` (the prime: the sides are flipped relative to `h.ne : 0 ≠ n`). Placeholders: `(n : ℕ) (h : 0 < n)`.

| Before | After |
|---|---|
| `⊢ G` | `hn : n ≠ 0 ⊢ G` |

**R4 · `Complex.isPrimitiveRoot_exp n hn`** changes the **context**. The lemma: `n ≠ 0 →
IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)) n`, i.e. $\omega = e^{2\pi i/n}$ has order
exactly `n`. Placeholders: `(n : ℕ) (hn : n ≠ 0)`.

| Before | After |
|---|---|
| `⊢ G` | `hω : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)) n ⊢ G` |

**R5 · `set z := e with hz`** changes the **context and the goal**: it adds a local definition `z := e`
and `hz : z = e`, and replaces every `e` in the goal and in the hypotheses by `z`. Here `e` is
`Complex.exp (2 * Real.pi * Complex.I / N) ^ j`. Placeholders: `{M : Type} [Monoid M] (a : M) (j : ℕ)`
(M has `*`, `1`, and so `^`).

| Before | After |
|---|---|
| `h : P (a ^ j) ⊢ P (a ^ j)` | `z : M := a ^ j, h : P z, hz : z = a ^ j ⊢ P z` |

### Step 3: `ζ ≠ 1` and `ζ ^ N = 1`

**R6 · `IsPrimitiveRoot.pow_eq_one_iff_dvd`** changes the **goal**. The lemma: `IsPrimitiveRoot ζ k →
∀ l, (ζ ^ l = 1 ↔ k ∣ l)`. With `ζ := ω ^ j` written as `ω ^ j`, `(hω.pow_eq_one_iff_dvd j).mp` turns
`ω ^ j = 1` into `N ∣ j`, which contradicts `hj`. Placeholders:
`{M : Type} [CommMonoid M] (ζ : M) (k l : ℕ) (hζ : IsPrimitiveRoot ζ k)` (`ℂ` qualifies).

| Before | After |
|---|---|
| `⊢ ζ ^ l = 1 → P` | `⊢ k ∣ l → P` |

**R7 · `pow_mul`** changes the **goal**. The lemma: `a ^ (m * n) = (a ^ m) ^ n`; `← pow_mul` merges two
powers, `pow_mul` splits them. Placeholders: `{M : Type} [Monoid M] (a : M) (m n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((a ^ m) ^ n)` | `⊢ P (a ^ (m * n))` |

**R8 · `mul_comm m n`** changes the **goal**: `m * n = n * m`. With both arguments it rewrites only that
product. Used to turn the exponent `j * N` into `N * j`, so that `pow_mul` gives `(ω ^ N) ^ j`.
Placeholders: `(m n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (m * n)` | `⊢ P (n * m)` |

**R9 · `IsPrimitiveRoot.pow_eq_one`** changes the **goal**: `IsPrimitiveRoot ζ k → ζ ^ k = 1`.
Placeholders: as R6.

| Before | After |
|---|---|
| `⊢ P (ζ ^ k)` | `⊢ P 1` |

**R10 · `one_pow`** changes the **goal**: `1 ^ n = 1`. Placeholders: `{M : Type} [Monoid M] (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (1 ^ n)` | `⊢ P 1` |

### Step 4: the geometric sum is `0`

**R11 · `geom_sum_mul x n`** changes the **context** (in a `have`). The lemma:
`(∑ i ∈ Finset.range n, x ^ i) * (x - 1) = x ^ n - 1`. Placeholders: `{α : Type} [Ring α] (x : α) (n : ℕ)`
(α has `+`, `-`, `*`; `ℂ` qualifies).

| Before | After |
|---|---|
| `⊢ G` | context gains `h : (∑ i ∈ Finset.range n, x ^ i) * (x - 1) = x ^ n - 1`; `⊢ G` |

**R12 · `rw [sub_self] at h`** changes the **context**: `sub_self : a - a = 0`, applied inside the
hypothesis `h` (not the goal). In the exercise `rw [hζN, sub_self] at h` first turns `ζ ^ N - 1` into
`1 - 1`, then into `0`. Placeholders: `{α : Type} [Ring α] (a s : α)`.

| Before | After |
|---|---|
| `h : s = a - a ⊢ s = 0` | `h : s = 0 ⊢ s = 0` |

**R13 · `mul_eq_zero.mp h`** changes the **context**. The lemma: `a * b = 0 ↔ a = 0 ∨ b = 0`, valid when
there are no zero divisors. Placeholders: `{α : Type} [MulZeroClass α] [NoZeroDivisors α] (a b : α)`
(`ℝ`, `ℂ` and every field qualify).

| Before | After |
|---|---|
| `⊢ G` | `h' : a = 0 ∨ b = 0 ⊢ G` |

**R14 · `h.resolve_right hB`** (`Or.resolve_right : A ∨ B → ¬B → A`) **closes** the goal `A`.
Placeholders: `(A B : Prop) (h : A ∨ B) (hB : ¬B)`.

| Before | After |
|---|---|
| `h : A ∨ B, hB : ¬B ⊢ A` | no goals |

**R15 · `sub_ne_zero`** changes the **goal**: `a - b ≠ 0 ↔ a ≠ b`. As a term, `sub_ne_zero.mpr hζ1 :
ζ - 1 ≠ 0` is the `¬B` that R14 needs. Placeholders: `{α : Type} [AddGroup α] (a b : α)`.

| Before | After |
|---|---|
| `⊢ a - b ≠ 0` | `⊢ a ≠ b` |

**W1** chains R11–R15 for a cube root of unity `z ≠ 1`, `z ^ 3 = 1`:

```lean-goal
⊢ ∑ i ∈ Finset.range 3, z ^ i = 0
```

with, after `have h := geom_sum_mul z 3` and `rw [hz3, sub_self] at h`,
`h : (∑ i ∈ Finset.range 3, z ^ i) * (z - 1) = 0`, closed by
`(mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hz1)`.

### Step 5: cosines → real part of a geometric sum (`calc`)

**R16 · `Complex.re_sum`** changes the **goal**: `(∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re` (the real part of a
sum is the sum of real parts). Placeholders: `{ι : Type} (s : Finset ι) (f : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, f i).re` | `⊢ P (∑ i ∈ s, (f i).re)` |

**R17 · `simp only [Complex.exp_ofReal_mul_I_re]`** changes the **goal**. The lemma:
`(Complex.exp (↑x * Complex.I)).re = Real.cos x` for `x : ℝ` (Euler). The terms sit under `∑`, so use
`simp only`, not `rw` (see R32). Placeholders: `{ι : Type} (s : Finset ι) (θ : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, (Complex.exp (↑(θ i) * Complex.I)).re)` | `⊢ P (∑ x ∈ s, Real.cos (θ x))` |

**R18 · `Finset.mul_sum`** changes the **goal**: `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`. Left to right it
moves the phase `exp (-(2πIj/N) m)` into the sum; right to left (`← Finset.mul_sum`) it pulls a constant
out (Parts 3, 4). Placeholders: `{ι α : Type} [NonUnitalNonAssocSemiring α] (s : Finset ι) (a : α)
(f : ι → α)` (α has `+`, `*`, distributivity; `ℝ`, `ℂ` qualify).

| Before | After |
|---|---|
| `⊢ P (a * ∑ i ∈ s, f i)` | `⊢ P (∑ i ∈ s, a * f i)` |

**R19 · `← Fin.sum_univ_eq_sum_range f n`** changes the **goal**. The lemma:
`∑ i : Fin n, f ↑i = ∑ i ∈ Finset.range n, f i`. Right to left it turns the `range` sum into the `Fin`
sum the goal has; give `f` explicitly (`fun n => … * ζ ^ n`), since Lean cannot guess it. Placeholders:
`{β : Type} [AddCommMonoid β] (f : ℕ → β) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ Finset.range n, f i)` | `⊢ P (∑ i, f ↑i)` |

**R20 · `congr 1`** changes the **goal**: `f a = f b` becomes `a = b`, peeling one function (here `.re` or
`Complex.exp`). If the new goal is a hypothesis, `congr 1` closes it by itself. Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ z.re = w.re` | `⊢ z = w` |
| `⊢ Complex.exp z = Complex.exp w` | `⊢ z = w` |

**R21 · `refine Finset.sum_congr rfl fun i _ => ?_`** changes the **goal and the context**: two sums over
the same set are equal if their terms are. Placeholders: `{ι M : Type} [Fintype ι] [AddCommMonoid M]
(f g : ι → M)`.

| Before | After |
|---|---|
| `⊢ ∑ i, f i = ∑ i, g i` | `i : ι, x✝ : i ∈ Finset.univ ⊢ f i = g i` |

**R22 · `← Complex.exp_nat_mul`** changes the **goal**. The lemma:
`Complex.exp (↑n * x) = Complex.exp x ^ n`; right to left a power of an exponential becomes one
exponential. Placeholders: `(x : ℂ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Complex.exp x ^ n)` | `⊢ P (Complex.exp (↑n * x))` |

**R23 · `← Complex.exp_add`** changes the **goal**. The lemma:
`Complex.exp (x + y) = Complex.exp x * Complex.exp y`. Placeholders: `(x y : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (Complex.exp x * Complex.exp y)` | `⊢ P (Complex.exp (x + y))` |

**R24 · `push_cast`** changes the **goal**: it pushes casts `↑` inward to the atoms (`↑(x * y - z)` →
`↑x * ↑y - ↑z`; a real cast of a natural cast `↑(↑n : ℝ) : ℂ` → `↑n`; `↑(2 : ℕ)` → `2`). After it, both
sides are polynomials in the same atoms and `ring` closes the exponent equation. Placeholders:
`(x y : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑(x * y - ↑n)` | `⊢ P (↑x * ↑y - ↑n)` |

**R25 · `simp`** **closes** `(a * 0).re = 0` (it uses `mul_zero`, then `Complex.zero_re : (0 : ℂ).re = 0`).
That is the last `calc` step after `rw [hgeom]`. Placeholders: `(a : ℂ)`.

| Before | After |
|---|---|
| `⊢ (a * 0).re = 0` | no goals |

**W3** runs R16–R17 and R22–R24 backwards on `cos (φ + nθ) = (e^{iφ} (e^{iθ})^n).re`:

```lean-goal
⊢ Real.cos (φ + ↑n * θ) = (Complex.exp (↑φ * Complex.I) * Complex.exp (↑θ * Complex.I) ^ n).re
⊢ (Complex.exp (↑(φ + ↑n * θ) * Complex.I)).re = (Complex.exp (↑φ * Complex.I + ↑n * (↑θ * Complex.I))).re
⊢ ↑(φ + ↑n * θ) * Complex.I = ↑φ * Complex.I + ↑n * (↑θ * Complex.I)
⊢ (↑φ + ↑n * ↑θ) * Complex.I = ↑φ * Complex.I + ↑n * (↑θ * Complex.I)
```

(after `rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_ofReal_mul_I_re]`, `congr 2`,
`push_cast`; then `ring`).

---

## Part 2 · `ka_eq` (milestone)

Statement: `(kOf T n : ℝ) * T.a = 2 * Real.pi / T.N * ((n : ℝ) - (T.N / 2 : ℕ))`, the angle
$\theta_n = k_n a$. Unfold `kOf`, then cancel `T.a`.

**R26 · `T.a_pos.ne'`** changes the **context**: `T.a_pos : 0 < T.a` is a field of the structure, and R3
turns it into `T.a ≠ 0`, which R28 needs. (Likewise `NeZero.pos T.N : 0 < T.N`.) Placeholders:
`(T : TightBindingChain)`.

| Before | After |
|---|---|
| `⊢ G` | `ha : T.a ≠ 0 ⊢ G` |

**R27 · `simp only [d]`** for a definition `d` whose value is `⟨x, proof⟩` in a subtype changes the
**goal**: it unfolds `d`, and the value `↑⟨x, proof⟩` reduces to `x`. In the guide
`half : {x : ℝ | 0 < x} := ⟨1 / 2, …⟩`.

| Before | After |
|---|---|
| `⊢ P ↑half` | `⊢ P (1 / 2)` |

**R28 · `field_simp`** changes the **goal**: it multiplies out every denominator whose `≠ 0` fact is in the
context (`ha`, and `↑T.N ≠ 0`, which it finds from `NeZero`), then normalises; here it closes the goal.
Placeholders: `(a b x : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)`.

| Before | After |
|---|---|
| `ha : a ≠ 0, hb : b ≠ 0 ⊢ x / (a * b) * a = x / b` | no goals |

---

## Part 3 · `band_sum_rule`

Statement: for `hN : 2 ≤ T.N`, `∑ n, T.energyEigenvalue (kOf T n) = T.N * T.E0`. Get `hcos` from Part 1
with `j = 1`, then one `simp only` and `ring`.

**R29 · `Nat.not_dvd_of_pos_of_lt`** produces `¬ n ∣ m` and changes the **goal list** when used with
`apply`. The lemma: `0 < m → m < n → ¬ n ∣ m`. In the exercise write it as a term,
`Nat.not_dvd_of_pos_of_lt one_pos (by omega)` (`one_pos : 0 < 1`, `two_pos : 0 < 2`; `omega` proves
`1 < T.N` from `hN`). Placeholders: `(N : ℕ) (hN : 4 ≤ N)`.

| Before | After |
|---|---|
| `⊢ ¬N ∣ 3` | `⊢ 0 < 3`, `⊢ 3 < N` |

**R30 · `simp only [Nat.cast_one, mul_one] at h`** changes the **context**: `Nat.cast_one : ↑1 = 1` and
`mul_one : x * 1 = x`. `sum_cos … 1 …` contains `2 * Real.pi * ↑1 / ↑T.N`; this turns it into
`2 * Real.pi / ↑T.N`, the form the energy has after `ka_eq`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `h : P (x * ↑1) ⊢ P x` | `h : P x ⊢ P x` |

**R31 · `TightBindingChain.energyEigenvalue`** changes the **goal** (`simp only` unfolds it, also under `∑`).
The definition: `T.energyEigenvalue k = T.E0 - 2 * T.t * Real.cos (↑k * T.a)`. Placeholders:
`(T : TightBindingChain) (k : T.QuantaWaveNumber)`.

| Before | After |
|---|---|
| `⊢ P (T.energyEigenvalue k)` | `⊢ P (T.E0 - 2 * T.t * Real.cos (↑k * T.a))` |

**R32 · `simp only [hfg]`** with `hfg : ∀ i, f i = g i` (such as `ka_eq`, `hcos`, `hterm`) changes the
**goal**, also under `∑`. `rw [hfg]` fails there with "Did not find an occurrence of the pattern f ?i":
the `i` under `∑` is a bound variable, which `rw` cannot instantiate. Placeholders:
`(N : ℕ) (f g : Fin N → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, Real.cos (f i))` | `⊢ P (∑ x, Real.cos (g x))` |

**R33 · `Finset.sum_sub_distrib`** changes the **goal**: `∑ i ∈ s, (f i - g i) = ∑ i ∈ s, f i - ∑ i ∈ s, g i`.
Placeholders: `{ι α : Type} [AddCommGroup α] (s : Finset ι) (f g : ι → α)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, (f i - g i))` | `⊢ P (∑ x ∈ s, f x - ∑ x ∈ s, g x)` |

**R34 · `Finset.sum_const`** changes the **goal**: a sum of a constant is `card • constant`,
`∑ _i ∈ s, c = s.card • c`. Placeholders: `{ι α : Type} [AddCommMonoid α] (s : Finset ι) (c : α)`.

| Before | After |
|---|---|
| `⊢ P (∑ _i ∈ s, c)` | `⊢ P (s.card • c)` |

**R35 · `Finset.card_univ`, then `Fintype.card_fin`** change the **goal**: `Finset.univ.card = Fintype.card ι`
and `Fintype.card (Fin n) = n`. Placeholders: `(n : ℕ)`.

| Before | After `rw [Finset.card_univ]` | After `rw [Fintype.card_fin]` |
|---|---|---|
| `⊢ P Finset.univ.card` | `⊢ P (Fintype.card (Fin n))` | `⊢ P n` |

**R36 · `nsmul_eq_mul`** changes the **goal**: `n • a = ↑n * a`, turning the repeated sum into a product
with the cast `↑n`. Placeholders: `(n : ℕ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (n • a)` | `⊢ P (↑n * a)` |

Then R18 right to left pulls `2 * T.t` out of `∑ (2 * T.t * cos …)`, and `hcos` (R32) replaces the
remaining sum by `0`. `ring` finishes `↑T.N * T.E0 - 2 * T.t * 0 = ↑T.N * T.E0`.

**W2** does the same on `∑ i, (c - 3 * f i)` with `hf : ∑ i, f i = 0`. One `simp only` with R33–R36,
`← Finset.mul_sum` and `hf` gives

```lean-goal
⊢ ↑n * c - 3 * 0 = ↑n * c
```

---

## Part 4 · `band_second_moment`

Statement: for `hN : 3 ≤ T.N`, `∑ n, (T.energyEigenvalue (kOf T n) - T.E0) ^ 2 = 2 * T.N * T.t ^ 2`. Get
`hcos` with `j = 2`, prove each term equals `2t² + 2t² cos(2θₙ)` (`hterm`), then sum as in Part 3.

**R37 · `rw [show A = B by ring]`** changes the **goal**: it rewrites with an identity proved on the
spot. `A` must appear literally in the goal, so copy it from the infoview (in `hterm`:
`(T.E0 - 2 * T.t * c - T.E0) ^ 2 = 4 * T.t ^ 2 * c ^ 2` with `c` the cosine). Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((x * y) ^ 2)` | `⊢ P (x ^ 2 * y ^ 2)` |

**R38 · `Real.cos_sq x`** changes the **goal**: `Real.cos x ^ 2 = 1 / 2 + Real.cos (2 * x) / 2`.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.cos x ^ 2)` | `⊢ P (1 / 2 + Real.cos (2 * x) / 2)` |

**R39 · `ring_nf`** **closes** an equation whose sides differ inside a function argument. It normalises
every subterm, so `Real.cos (2 * (a / b))` and `Real.cos (a * 2 / b)` get the same normal form. `ring`
treats `Real.cos (…)` as an opaque unknown, fails, and prints "Try this: ring_nf". In `hterm`, after R38
and `push_cast` (R24, turning `↑(2 : ℕ)` into `2`), the two cosines are `cos (2 * (2π/N · x))` and
`cos (2π · 2 / N · x)`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ c * Real.cos (2 * (a / b)) = Real.cos (a * 2 / b) * c` | no goals |

**R40 · `Finset.sum_add_distrib`** changes the **goal**: `∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i`.
Placeholders: `{ι α : Type} [AddCommMonoid α] (s : Finset ι) (f g : ι → α)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, (f i + g i))` | `⊢ P (∑ x ∈ s, f x + ∑ x ∈ s, g x)` |

Then `simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hcos, Finset.sum_const, …]` (R32, R40,
R18, R34–R36) leaves `2 * (↑T.N * T.t ^ 2) + 2 * T.t ^ 2 * 0 = 2 * ↑T.N * T.t ^ 2` for `ring`.

---

## Traps

- `T.N / 2 : ℕ` rounds down. The sum rules need `N ∤ j`: rule (1) fails for `N = 1` (`cos 0 = 1`), rule
  (2) for `N = 2` (`k a ∈ {−π, 0}`, so `cos² = 1` at both `k`). That is why the hypotheses are `2 ≤ T.N`
  and `3 ≤ T.N`, and why R29 needs `omega` with them.
- Keep the cast `(2 : ℕ)` in `hterm`'s angle: `sum_cos … 2 …` produces `2 * Real.pi * ↑2 / ↑T.N * …`,
  and R32 needs the term in `hterm` to match it literally. `push_cast` inside `hterm`'s proof removes the
  cast there, not in the statement.
- `rw` cannot rewrite under `∑` (R32): use `simp only [lemma]` for `ka_eq`, `energyEigenvalue`,
  `Complex.exp_ofReal_mul_I_re`, `hterm`.
- `Fin.sum_univ_eq_sum_range` right to left needs the function given explicitly (R19).
- `ring` does not look inside `Real.cos (…)` or `Complex.exp (…)`. Before `ring`, strip the function
  with `congr 1` (R20), or use `ring_nf` (R39).
- `set ζ := … with hζ` replaces the expression everywhere; to unfold it again, `rw [hζ]`.
- `IsPrimitiveRoot.pow_eq_one_iff_dvd` needs the exponent as an argument: `hω.pow_eq_one_iff_dvd j`.
- In `simp only [...] at hcos`, the `at hcos` changes the hypothesis, not the goal (R30).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `N = 0` / `0 < N` | `rcases Nat.eq_zero_or_pos N with rfl \| hN` | R1 |
| empty sum over `Fin 0` | `simp` | R2 |
| `0 < n` → `n ≠ 0` | `h.ne'` | R3 |
| `exp (2πi/n)` is a primitive root | `Complex.isPrimitiveRoot_exp n hn` | R4 |
| name a subterm | `set z := e with hz` | R5 |
| `ζ ^ l = 1 ↔ k ∣ l`, `ζ ^ k = 1` | `hζ.pow_eq_one_iff_dvd l`, `hζ.pow_eq_one` | R6, R9 |
| merge / split powers, `1 ^ n` | `rw [← pow_mul]` / `rw [pow_mul]`, `one_pow` | R7, R10 |
| swap one product | `rw [mul_comm m n]` | R8 |
| geometric sum identity | `have h := geom_sum_mul x n` | R11 |
| rewrite a hypothesis | `rw [sub_self] at h`, `simp only [...] at h` | R12, R30 |
| `a * b = 0`, `b ≠ 0` → `a = 0` | `(mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hb)` | R13–R15 |
| `.re` of a sum | `rw [Complex.re_sum]` | R16 |
| `(exp (↑x * I)).re` → `cos x` | `simp only [Complex.exp_ofReal_mul_I_re]` | R17 |
| constant into / out of a sum | `Finset.mul_sum` / `← Finset.mul_sum` | R18 |
| `range` sum ↔ `Fin` sum | `rw [← Fin.sum_univ_eq_sum_range f n]` | R19 |
| strip `.re` / `exp` | `congr 1` | R20 |
| sums equal termwise | `refine Finset.sum_congr rfl fun i _ => ?_` | R21 |
| merge exponentials | `rw [← Complex.exp_nat_mul, ← Complex.exp_add]` | R22, R23 |
| casts inward | `push_cast` | R24 |
| `T.a ≠ 0` | `T.a_pos.ne'` | R26 |
| unfold `kOf` | `simp only [kOf]` | R27 |
| clear denominators | `field_simp` | R28 |
| `¬ N ∣ j` from `j < N` | `Nat.not_dvd_of_pos_of_lt one_pos (by omega)` | R29 |
| unfold the energy | `simp only [TightBindingChain.energyEigenvalue]` | R31 |
| rewrite under `∑` | `simp only [h]` | R32 |
| split a sum | `Finset.sum_sub_distrib`, `Finset.sum_add_distrib` | R33, R40 |
| `∑ c` → `↑N * c` | `Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul` | R34–R36 |
| ad-hoc identity | `rw [show A = B by ring]` | R37 |
| `cos² x` | `rw [Real.cos_sq]` | R38 |
| algebra inside `cos (…)` | `ring_nf` | R39 |
| plain algebra | `ring` | TACTIC_STATES |
