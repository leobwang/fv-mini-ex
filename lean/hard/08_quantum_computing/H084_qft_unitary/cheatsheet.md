# H084 · The quantum Fourier transform is unitary: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `intro`, `exact`, `rw`, `simp`, `have`, `ext`,
`ring`, `norm_num`; `Fin n`. Matrices `Matrix n n ℂ`, `Matrix.mul_apply` and the unitary group are
explained again here (they first appear in M126).
**New here:** Mathlib's complex exponential `Complex.exp` and conjugation `starRingEnd ℂ`, primitive roots
of unity (`IsPrimitiveRoot`), finite sums over `Fin N` and over `Finset.range N`, the geometric-sum formula,
and the casts `ℕ → ℝ → ℂ`.

**The maths.** Fix `N ≥ 1` and the primitive `N`-th root of unity `ζ = e^{2πi/N}`: `ζ^N = 1` and
`ζ^m ≠ 1` for `0 < m < N`. The QFT matrix is `F j k = ζ^{jk} / √N` for `j, k ∈ {0, …, N−1}`.
Unitarity `F F* = 1` (`F*` = conjugate transpose) reads, entry `(j, l)`:
`(F F*)_{jl} = (1/N) ∑ₖ ζ^{jk} · conj(ζ^{lk})`. Since `|ζ| = 1`, `conj ζ = ζ⁻¹`, so the sum is
`∑ₖ rᵏ` with `r = ζ^j ζ^{−l}`.

- `j = l`: `r = 1`, the sum is `N`, the entry is `1`.
- `j ≠ l`: `r^N = (ζ^N)^j (ζ^N)^{−l} = 1`, and `r ≠ 1` (else `ζ^j = ζ^l` with `j, l < N`, so `j = l`).
  The geometric sum `∑_{k<N} rᵏ = (r^N − 1)/(r − 1) = 0`.

The three MILESTONES are exactly these steps: `exp_eq_zeta_pow` (`e^{2πim/N} = ζ^m`), `conj_zeta`
(`conj ζ = ζ⁻¹`), `root_orthogonality` (the sum is `N·[j = l]`).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G`, `Q` are arbitrary goals; a hypothesis `g : T → G` only shows what the new
  fact is for.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommMonoid M]` is
  a requirement on `M` (a *type class*); `ℂ` meets every one used here (`Monoid`, `CommMonoid`,
  `DivisionMonoid`, `GroupWithZero`, `DivisionRing`, `AddGroup`, `AddCommMonoid`). `[Fintype n]` says `n`
  is finite (so `∑ j, …` over `n` makes sense); `[DecidableEq n]` says `=` on `n` can be tested (so
  `if i = j then …` makes sense). `Fin N` has both.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `cexp z` | `Complex.exp z`, the complex exponential `e^z` |
| `I` | `Complex.I`, the imaginary unit `i` |
| `↑Real.pi` | `π : ℝ` cast into `ℂ` |
| `↑N`, `↑m` (in `ℂ`) | the natural number `N` cast into `ℂ` (`Nat.cast`) |
| `↑j`, `↑k` (`j k : Fin N`) | the value of `j : Fin N` as a natural number in `{0, …, N−1}` (`Fin.val`) |
| `↑(↑j * ↑k)` | the product `j·k` computed in `ℕ`, then cast into `ℂ`; the spec writes it `((j : ℕ) * (k : ℕ) : ℕ)` |
| `↑↑N` | `N : ℕ` cast into `ℝ`, then into `ℂ` (push it to one cast with R57) |
| `↑√↑N` | `Real.sqrt (↑N : ℝ)`, a real number, cast into `ℂ` |
| `(starRingEnd ℂ) z` | the complex conjugate `conj z`, as a ring map; the lemmas `map_mul`, `map_pow`, … apply to it |
| `star z`, `star M` | for `z : ℂ`: `conj z` again (R48 converts); for a matrix: the conjugate transpose `M*` (R45) |
| `IsPrimitiveRoot ζ k` | `ζ ^ k = 1`, and `ζ ^ l = 1 → k ∣ l`: `ζ` has order exactly `k` |
| `ζ : ℂ := cexp a` | a local definition made by `set` (R14): `ζ` unfolds to `cexp a` |
| `ζ : ℂ := ⋯` | the same local definition, its body elided inside a nested `have … := by` |
| `a⁻¹`, `(↑N)⁻¹` | the inverse `1 / a` in `ℂ`; `ζ⁻¹ ^ n` is `(ζ⁻¹)ⁿ` |
| `∀ x ∈ s, f x = g x` | `∀ x, x ∈ s → f x = g x`: introduce it with `intro x hx` (R52) |
| `∑ k, f k` (`k : Fin N`) | sum over all `k : Fin N` (the Finset `Finset.univ`) |
| `∑ i ∈ Finset.range n, f i` | sum over `i = 0, 1, …, n − 1` in `ℕ` |
| `s.card`, `n • a` | the number of elements of a Finset; `a + ⋯ + a` (`n` copies) |
| `of f`, `of f i j` | `Matrix.of f`, the matrix with entry `f i j` at `(i, j)` |
| `1 j l` | entry `(j, l)` of the identity matrix (R56) |
| `unitaryGroup n ℂ` | the unitary matrices: `U * star U = 1` (R41) |
| `case pos`, `case neg` | the two branches after `split_ifs` (R22) |
| `x`, `x_1` in `∑ x, …` | a bound variable Lean renamed; the name does not matter |
| `h✝`, `a✝`, `inst✝` | inaccessible names made by a tactic (`inst✝` is a type-class argument); you cannot type them |

---

## Part 1 · `exp_eq_zeta_pow` (MILESTONE 1)

Statement: `exp (2πi·m/N) = (exp (2πi/N))^m` for natural `m, N`. Used in Part 3 at `m = j·k` and `m = l·k`.

**R1 · `rw [← Complex.exp_nat_mul]`** changes the **goal**. The lemma is
`Complex.exp_nat_mul (x : ℂ) (n : ℕ) : cexp (↑n * x) = cexp x ^ n`; right to left it turns a power of an
exponential into one exponential. Placeholders: `(x : ℂ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (cexp x ^ n)` | `⊢ P (cexp (↑n * x))` |

**R2 · `congr 1`** changes the **goal**: `f a = f b` becomes `a = b` (one function application removed from
both sides). It closes the new goal itself when it is `rfl` or a hypothesis. Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ cexp a = cexp b` | `⊢ a = b` |

**R3 · `ring`** **closes** an identity of fields: `x / y` is read as `x * y⁻¹`, and `y⁻¹`, `I`, `↑Real.pi`, `↑m`
are unknowns. So `2 * ↑π * I * ↑m / ↑N = ↑m * (2 * ↑π * I / ↑N)` is `ring`. It cannot cancel `↑N * (↑N)⁻¹`
(that needs `↑N ≠ 0`, R58), and this goal does not need it.

**W1** (on `π i / 3`):

```lean-goal
⊢ cexp (↑Real.pi * I * ↑m / 3) = cexp (↑Real.pi * I / 3) ^ m
⊢ cexp (↑Real.pi * I * ↑m / 3) = cexp (↑m * (↑Real.pi * I / 3))
⊢ ↑Real.pi * I * ↑m / 3 = ↑m * (↑Real.pi * I / 3)
```

---

## Part 2 · `conj_zeta` (MILESTONE 2)

Statement: `conj (exp (2πi/N)) = (exp (2πi/N))⁻¹`. Used in Part 3 to turn `conj (ζ ^ m)` into `ζ⁻¹ ^ m`.
Route: `conj (e^x) = e^{conj x}` and `(e^x)⁻¹ = e^{−x}`, so it suffices that `conj (2πi/N) = −2πi/N`.

**R4 · `rw [← Complex.exp_conj]`** changes the **goal**. The lemma is
`Complex.exp_conj (x : ℂ) : cexp ((starRingEnd ℂ) x) = (starRingEnd ℂ) (cexp x)`; right to left it moves the
conjugation inside the exponential. Placeholders: `(x : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (cexp x))` | `⊢ P (cexp ((starRingEnd ℂ) x))` |

**R5 · `rw [← Complex.exp_neg]`** changes the **goal**. The lemma is `Complex.exp_neg (x : ℂ) : cexp (-x) = (cexp x)⁻¹`.
Placeholders: `(x : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (cexp x)⁻¹` | `⊢ P (cexp (-x))` |

Then R2 strips `cexp`. R6–R11 are applied by one `simp [Complex.conj_ofReal, map_div₀, map_ofNat]` (R7, R10,
R11 are already simp lemmas). Each changes the **goal** and pushes `conj = starRingEnd ℂ` one step inward.
Placeholders: `(a b : ℂ) (r : ℝ) (n : ℕ)`.

**R6 · `map_div₀`**: `f (a / b) = f a / f b` for any map `f` of fields (here `f = starRingEnd ℂ`).

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (a / b))` | `⊢ P ((starRingEnd ℂ) a / (starRingEnd ℂ) b)` |

**R7 · `map_mul`**: `f (a * b) = f a * f b`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (a * b))` | `⊢ P ((starRingEnd ℂ) a * (starRingEnd ℂ) b)` |

**R8 · `map_ofNat`**: `f 2 = 2` for any numeral `≥ 2` (`0` and `1` are `map_zero`, `map_one`). Use it with
`simp only`, not `rw`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) 2)` | `⊢ P 2` |

**R9 · `Complex.conj_ofReal`**: `conj ↑r = ↑r` for a real `r`; here `r = Real.pi`, and in Part 4
`r = Real.sqrt ↑N`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) ↑r)` | `⊢ P ↑r` |

**R10 · `Complex.conj_I`**: `conj I = -I`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) I)` | `⊢ P (-I)` |

**R11 · `map_natCast`**: `f ↑n = ↑n` for `n : ℕ`; here `n = N`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) ↑n)` | `⊢ P ↑n` |

**W2** (on `π i / 3`): R4 and R5 in one `rw`, then R2, then the `simp`, then R3.

```lean-goal
⊢ (starRingEnd ℂ) (cexp (↑Real.pi * I / 3)) = (cexp (↑Real.pi * I / 3))⁻¹
⊢ cexp ((starRingEnd ℂ) (↑Real.pi * I / 3)) = cexp (-(↑Real.pi * I / 3))
⊢ (starRingEnd ℂ) (↑Real.pi * I / 3) = -(↑Real.pi * I / 3)
⊢ -(↑Real.pi * I) / 3 = -(↑Real.pi * I / 3)
```

---

## Part 3 · `root_orthogonality` (MILESTONE 3)

Statement: for `j l : Fin N`,
`∑ k : Fin N, exp (2πi·jk/N) · conj (exp (2πi·lk/N)) = if j = l then N else 0`. Used in Part 4. Uses
Parts 1 and 2.

### Setting up: `N ≠ 0`, the name `ζ`, facts about `ζ`

**R12 · `rintro rfl`** changes the **goal and the context**. `n ≠ 0` is `n = 0 → False`; `rintro rfl` introduces
the equation and substitutes `0` for `n` everywhere. Placeholders: `(n : ℕ) (P : ℕ → Prop)`.

| Before | After |
|---|---|
| `hP : P n ⊢ n ≠ 0` | `hP : P 0 ⊢ False` |

**R13 · `exact j.elim0`** **closes** any goal when `j : Fin 0` is in the context (`Fin 0` is empty).
`Fin.elim0 : Fin 0 → C` for every `C`. After R12 with `n = N`, your `j : Fin N` has become `j : Fin 0`.

| Before | After |
|---|---|
| `j : Fin 0 ⊢ C` | no goals |

**R14 · `set x := e with hx`** changes the **context and the goal**: it adds the local definition `x := e`
and `hx : x = e`, and replaces every `e` in the goal and context by `x`. Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (cexp a * b)` | `ζ : ℂ := cexp a, hζ : ζ = cexp a ⊢ P (ζ * b)` |

**R15 · `Complex.isPrimitiveRoot_exp`** changes the **context**. The lemma is
`Complex.isPrimitiveRoot_exp (n : ℕ) (h0 : n ≠ 0) : IsPrimitiveRoot (cexp (2 * ↑Real.pi * I / ↑n)) n`.
Placeholders: `(n : ℕ) (hn : n ≠ 0)`. After R14 the root prints as `ζ`, and `IsPrimitiveRoot ζ N` is accepted
for it (`ζ` unfolds).

| Before | After |
|---|---|
| `⊢ G` | `hprim : IsPrimitiveRoot (cexp (2 * ↑Real.pi * I / ↑n)) n ⊢ G` |

**R16 · `hprim.ne_zero hk`** changes the **context**. The lemma is
`IsPrimitiveRoot.ne_zero : IsPrimitiveRoot ζ k → k ≠ 0 → ζ ≠ 0`. Placeholders: `(ζ : ℂ) (k : ℕ)`.

| Before | After |
|---|---|
| `hprim : IsPrimitiveRoot ζ k ⊢ G` | `hne : ζ ≠ 0 ⊢ G` |

### Every term as a power of one number `r`

**R17 · `simp only [h]`** with `h : ∀ m, f m = g m` changes the **goal**: it rewrites inside `∑ k, …` (and
any `fun k => …`), where `rw [h]` fails because `k` is bound. Placeholders: `(f g : ℕ → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ k, f ↑k)` | `⊢ P (∑ x, g ↑x)` |

**R18 · `map_pow`**: `f (a ^ n) = f a ^ n` changes the **goal**. With R17 and the two MILESTONES restated for
`ζ` (`hpow`, `hconj`), `simp only [hpow, map_pow, hconj]` turns the summand into
`ζ ^ (↑j * ↑x) * ζ⁻¹ ^ (↑l * ↑x)`. Placeholders: `(a : ℂ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (a ^ n))` | `⊢ P ((starRingEnd ℂ) a ^ n)` |

**R19 · `mul_pow`**: `(a * b) ^ n = a ^ n * b ^ n` changes the **goal**. Placeholders:
`{M : Type} [CommMonoid M] (a b : M) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((a * b) ^ n)` | `⊢ P (a ^ n * b ^ n)` |

**R20 · `pow_mul`**: `a ^ (m * n) = (a ^ m) ^ n` changes the **goal**; `← pow_mul` folds back. Placeholders:
`{M : Type} [Monoid M] (a : M) (m n : ℕ)`. To regroup `ζ ^ (j * k) = (ζ ^ j) ^ k` the exponent must already
be `j * k` in `ℕ`, which is why the spec casts the product `↑(↑j * ↑k)` and not each factor.

| Before | After `rw [pow_mul]` |
|---|---|
| `⊢ P (a ^ (m * n))` | `⊢ P ((a ^ m) ^ n)` |
| `⊢ P ((a ^ m) ^ n)` | `⊢ P (a ^ (m * n))` (after `rw [← pow_mul]`) |

**R21 · `rw [Fin.sum_univ_eq_sum_range f n]`** changes the **goal**: a sum over `k : Fin n` of `f ↑k` becomes a
sum over `k ∈ range n`, where `geom_sum_eq` (R38) applies. The lemma is
`Fin.sum_univ_eq_sum_range (f : ℕ → β) (n : ℕ) : ∑ i, f ↑i = ∑ i ∈ Finset.range n, f i`.
Placeholders: `{β : Type} [AddCommMonoid β] (f : ℕ → β) (n : ℕ)`. **Give `f` explicitly**: for the summand
`r ^ ↑k` write `(fun k => r ^ k)` (W3); Lean does not find `f` on its own.

| Before | After |
|---|---|
| `⊢ P (∑ i, f ↑i)` | `⊢ P (∑ i ∈ Finset.range n, f i)` |

### The two cases

**R22 · `split_ifs with h`** changes the **goal list and the context**: a goal containing `if c then a else b`
becomes two goals, one with `h : c` and `a`, one with `h : ¬c` and `b` (cases `pos`, `neg`). Without `with h`
the hypothesis is the inaccessible `h✝`. Placeholders: `(c : Prop) [Decidable c] (a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (if c then a else b)` | `h : c ⊢ P a`, `h : ¬c ⊢ P b` |

**Case `j = l`.**

**R23 · `subst h`** changes the **context and the goal**: with `h : a = b` and `b` a variable, `b` is replaced
by `a` everywhere and `h` disappears. Placeholders: `{α : Type} (a b : α)`. Here: `h : j = l`.

| Before | After |
|---|---|
| `h : a = b ⊢ P a b` | `⊢ P a a` |

Now the summand is `(ζ ^ ↑j * ζ⁻¹ ^ ↑j) ^ i`, and `simp [mul_inv_cancel₀ (pow_ne_zero _ hne)]` closes the
goal. It uses R24, R25, R26, then `one_pow` and R27–R29 (W5).

**R24 · `inv_pow`**: `a⁻¹ ^ n = (a ^ n)⁻¹` changes the **goal**. It is a simp lemma, so after any `simp`
you see `(ζ ^ n)⁻¹`, never `ζ⁻¹ ^ n`. Placeholders: `{α : Type} [DivisionMonoid α] (a : α) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (a⁻¹ ^ n)` | `⊢ P (a ^ n)⁻¹` |

**R25 · `pow_ne_zero n ha`** changes the **context**: `a ≠ 0 → a ^ n ≠ 0`. Placeholders: `(a : ℂ) (n : ℕ)`.
Pass it as an argument, `pow_ne_zero _ hne`, with `_` for the exponent.

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ G` | `han : a ^ n ≠ 0 ⊢ G` |

**R26 · `mul_inv_cancel₀ ha`**: `a ≠ 0 → a * a⁻¹ = 1` changes the **goal**. Placeholders:
`{G : Type} [GroupWithZero G] (a : G) (ha : a ≠ 0)` (`G` has `*`, `⁻¹`, `0`, and `a * a⁻¹ = 1` for `a ≠ 0`).

| Before | After |
|---|---|
| `⊢ P (a * a⁻¹)` | `⊢ P 1` |

**R27 · `Finset.sum_const`**: a sum of a constant, `∑ _x ∈ s, c = s.card • c`, changes the **goal**.
Placeholders: `{ι β : Type} [AddCommMonoid β] (s : Finset ι) (c : β)`.

| Before | After |
|---|---|
| `⊢ P (∑ _x ∈ s, c)` | `⊢ P (s.card • c)` |

**R28 · `Finset.card_range`**: `(range n).card = n` changes the **goal**. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Finset.range n).card` | `⊢ P n` |

**R29 · `nsmul_eq_mul`**: `n • a = ↑n * a` changes the **goal**. Placeholders: `(n : ℕ) (a : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (n • a)` | `⊢ P (↑n * a)` |

**W5**: `simp` alone proves `∑ i ∈ Finset.range n, (1 : ℂ) ^ i = n` with these:

```lean-goal
⊢ ∑ i ∈ Finset.range n, 1 ^ i = ↑n
```

**Case `j ≠ l`.** Name `r := ζ ^ ↑j * ζ⁻¹ ^ ↑l` with R14 (`hr : r = …`). Prove `r ^ N = 1` and `r ≠ 1`, then
use R38–R40 (W4).

`hrN : r ^ N = 1`: `rw [hr]`, R19, R20 (`←`, twice), R24, R30 (twice), R20 (twice), R31; then `simp` closes
`1 ^ ↑j * (1 ^ ↑l)⁻¹ = 1`.

**R30 · `rw [mul_comm a b]`** changes the **goal**: only the product `a * b` is swapped, other products stay.
Here it turns the exponent `↑j * N` into `N * ↑j` so that R20 gives `(ζ ^ N) ^ ↑j`. Placeholders: `(a b c : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (a * b) (c * a)` | `⊢ P (b * a) (c * a)` |

**R31 · `rw [hprim.pow_eq_one]`** changes the **goal**: `IsPrimitiveRoot.pow_eq_one : IsPrimitiveRoot ζ k → ζ ^ k = 1`.
Placeholders: `(ζ : ℂ) (k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (ζ ^ k)` | `⊢ P 1` |

`hr1 : r ≠ 1`: `intro h1`, then R32 makes the goal `j = l`; get `ζ ^ ↑j = ζ ^ ↑l` from `h1` by R33 (with `hr`
and R24) and R34; finish with R37 applied to R35 (bounds from R36).

**R32 · `apply h`** with `h : ¬A` changes the **goal**: `False` becomes `A` (`¬A` is `A → False`). Here
`h : ¬j = l`. Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `h : ¬A ⊢ False` | `⊢ A` |

**R33 · `rw [e] at h`** changes the **context**: it rewrites hypothesis `h`; the goal stays. Placeholders:
`(a : ℂ) (n : ℕ) (Q : ℂ → Prop)`, here with `e = inv_pow`.

| Before | After |
|---|---|
| `h : Q (a⁻¹ ^ n) ⊢ Q (a ^ n)⁻¹` | `h : Q (a ^ n)⁻¹ ⊢ Q (a ^ n)⁻¹` |

**R34 · `(mul_inv_eq_one₀ hb).mp h`** changes the **context**. The lemma is
`mul_inv_eq_one₀ : b ≠ 0 → (a * b⁻¹ = 1 ↔ a = b)`; `.mp` is the `→` direction of `↔`. Placeholders:
`{G : Type} [GroupWithZero G] (a b : G) (hb : b ≠ 0)`. Here `b = ζ ^ ↑l`, `hb = pow_ne_zero _ hne` (R25).

| Before | After |
|---|---|
| `h : a * b⁻¹ = 1 ⊢ Q` | `hab : a = b ⊢ Q` |

**R35 · `hprim.pow_inj hi hj H`** changes the **context**. The lemma is
`IsPrimitiveRoot.pow_inj : IsPrimitiveRoot ζ k → i < k → j < k → ζ ^ i = ζ ^ j → i = j` (powers below the
order are distinct). Placeholders: `(ζ : ℂ) (k i j : ℕ)`.

| Before | After |
|---|---|
| `H : ζ ^ i = ζ ^ j ⊢ Q` | `hij : i = j ⊢ Q` |

**R36 · `i.isLt`** changes the **context**: `Fin.isLt (i : Fin n) : ↑i < n`. Placeholders: `(n : ℕ) (i : Fin n)`.

| Before | After |
|---|---|
| `⊢ Q` | `hi : ↑i < n ⊢ Q` |

**R37 · `Fin.ext`** changes the **goal**: `Fin.ext : ↑a = ↑b → a = b`, so an equation in `Fin n` becomes one
of natural numbers. As a term: `Fin.ext (hprim.pow_inj j.isLt l.isLt this)`. Placeholders: `(a b : Fin n)`.

| Before | After |
|---|---|
| `⊢ a = b` | `⊢ ↑a = ↑b` |

**R38 · `rw [geom_sum_eq hx]`** changes the **goal**. The lemma is
`geom_sum_eq : x ≠ 1 → ∀ n, ∑ i ∈ Finset.range n, x ^ i = (x ^ n - 1) / (x - 1)`. Placeholders:
`{K : Type} [DivisionRing K] (x : K) (hx : x ≠ 1) (n : ℕ)` (`K` a field such as `ℂ`).

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ Finset.range n, x ^ i)` | `⊢ P ((x ^ n - 1) / (x - 1))` |

**R39 · `sub_self`**: `a - a = 0`; **R40 · `zero_div`**: `0 / a = 0`. Both change the **goal**. Placeholders:
`{α : Type} [AddGroup α] (a : α)`; `{K : Type} [DivisionRing K] (a : K)`.

| Before | After |
|---|---|
| `⊢ P (a - a)` | `⊢ P 0` |
| `⊢ P (0 / a)` | `⊢ P 0` |

**W4** (any `r` with `r ^ n = 1`, `r ≠ 1`): R38, `rw [hrn]`, R39, R40.

```lean-goal
⊢ ∑ i ∈ Finset.range n, r ^ i = 0
⊢ (r ^ n - 1) / (r - 1) = 0
⊢ (1 - 1) / (r - 1) = 0
⊢ 0 / (r - 1) = 0
```

**W3** (R21 with an explicit function; `rw` closes it by `rfl`):

```lean-goal
⊢ ∑ k, r ^ ↑k = ∑ k ∈ Finset.range n, r ^ k
```

---

## Part 4 · `qft_unitary`

Statement: `qft N ∈ Matrix.unitaryGroup (Fin N) ℂ`. Membership becomes `qft N * star (qft N) = 1` (R41), then
entries `(j, l)`. Each entry is `(√N)⁻¹ · (√N)⁻¹ · (the sum of Part 3)`, so Part 3 and `(√N)⁻¹ ^ 2 = N⁻¹`
finish it.

**R41 · `rw [Matrix.mem_unitaryGroup_iff]`** changes the **goal**: membership becomes an equation.
Placeholders: `{n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ M ∈ unitaryGroup n ℂ` | `⊢ M * star M = 1` |

After `ext j l` (TACTIC_STATES) the goal is `(qft N * star (qft N)) j l = 1 j l`.

**R42 · `(Fin.pos i).ne'`** changes the **context**: `Fin.pos (i : Fin n) : 0 < n` (an element exists, so
`n > 0`), and `.ne'` turns `0 < n` into `n ≠ 0`. Placeholders: `(n : ℕ) (i : Fin n)`.

| Before | After |
|---|---|
| `⊢ Q` | `hn : n ≠ 0 ⊢ Q` |

**R43 · `Nat.cast_ne_zero.mpr hn`** changes the **context**: `Nat.cast_ne_zero : (↑n : ℂ) ≠ 0 ↔ n ≠ 0`; `.mpr` is
`←`. Placeholders: `(n : ℕ) (hn : n ≠ 0)`. State the type: `have hN : (N : ℂ) ≠ 0 := …`.

| Before | After |
|---|---|
| `hn : n ≠ 0 ⊢ Q` | `hc : ↑n ≠ 0 ⊢ Q` |

R44–R49 and R9 go into one `simp only [Matrix.mul_apply, Matrix.star_apply, qft, Matrix.of_apply, …]` that
writes the entry as a sum of explicit scalars. Each changes the **goal**.

**R44 · `Matrix.mul_apply`**: `(M * N) i k = ∑ j, M i j * N j k`. Placeholders:
`{n : Type} [Fintype n] (M N : Matrix n n ℂ) (i k : n)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R45 · `Matrix.star_apply`**: `star M i j = star (M j i)`: the conjugate transpose, entrywise.
Placeholders: `{n : Type} (M : Matrix n n ℂ) (i j : n)`.

| Before | After |
|---|---|
| `⊢ P (star M i j)` | `⊢ P (star (M j i))` |

**R46 · `Matrix.of_apply`**: `Matrix.of f i j = f i j`; after unfolding `qft` (`simp only [qft]`) the matrix is
`of (fun j k => …)`, and this evaluates it. Placeholders: `{n : Type} (f : n → n → ℂ) (i j : n)`.

| Before | After |
|---|---|
| `⊢ P (of f i j)` | `⊢ P (f i j)` |

**R47 · `star_mul'`**: `star (a * b) = star a * star b` (for commutative `*`; `star_mul` is the reversed
noncommutative version). Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star (a * b))` | `⊢ P (star a * star b)` |

**R48 · `RCLike.star_def`**: on `ℂ`, `star = starRingEnd ℂ`, so `star a` prints as `(starRingEnd ℂ) a` and the
`map_…` lemmas apply. Use it with `simp only`. Placeholders: `(a : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star a)` | `⊢ P ((starRingEnd ℂ) a)` |

**R49 · `map_inv₀`**: `f a⁻¹ = (f a)⁻¹`; with R9 it turns `conj (↑√↑N)⁻¹` into `(↑√↑N)⁻¹`. Placeholders: `(a : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) a⁻¹)` | `⊢ P ((starRingEnd ℂ) a)⁻¹` |

After this `simp only` the goal is a sum `∑ x, (↑√↑N)⁻¹ * cexp (…) * ((↑√↑N)⁻¹ * (starRingEnd ℂ) (cexp (…))) = 1 j l`.

**R50 · `trans b`** changes the **goal list**: `a = c` becomes `a = b` and `b = c`, for a middle term `b` you
write out. Here `b` is `(Real.sqrt N : ℂ)⁻¹ ^ 2 * ∑ k : Fin N, <the summand of Part 3>`. Placeholders:
`(a b c : ℂ)`.

| Before | After |
|---|---|
| `⊢ a = c` | `⊢ a = b`, `⊢ b = c` |

**R51 · `Finset.mul_sum`**: `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i` changes the **goal** (a constant moves into a
sum; `←` pulls it out). Placeholders: `{ι : Type} (s : Finset ι) (f : ι → ℂ) (a : ℂ)`. A sum over all of
`Fin N` is the case `s = Finset.univ`.

| Before | After |
|---|---|
| `⊢ P (a * ∑ i ∈ s, f i)` | `⊢ P (∑ i ∈ s, a * f i)` |

**R52 · `Finset.sum_congr rfl`** changes the **goal**: two sums over the same Finset are equal if their
summands are. The lemma is `Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`. As a
term in the exercise: `Finset.sum_congr rfl fun k _ => by ring`. Placeholders: `{ι : Type} (s : Finset ι) (f g : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ ∑ i ∈ s, f i = ∑ i ∈ s, g i` | `⊢ ∀ x ∈ s, f x = g x` |

**W6** (R51 on the right side, R52, then `ring` per summand):

```lean-goal
⊢ ∑ k ∈ s, c * f k * (c * g k) = c ^ 2 * ∑ k ∈ s, f k * g k
⊢ ∑ k ∈ s, c * f k * (c * g k) = ∑ i ∈ s, c ^ 2 * (f i * g i)
⊢ ∀ x ∈ s, c * f x * (c * g x) = c ^ 2 * (f x * g x)
⊢ c * f k * (c * g k) = c ^ 2 * (f k * g k)
```

On the second goal, `rw [root_orthogonality]` (MILESTONE 3), then the `√` clean-up R24, R53, R54 (W7), then R56.

**R53 · `rw [← Complex.ofReal_pow]`** changes the **goal**. The lemma is `Complex.ofReal_pow : ↑(x ^ n) = ↑x ^ n`;
right to left it moves `^` inside the real cast so a real lemma can apply. Placeholders: `(x : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (↑x ^ n)` | `⊢ P ↑(x ^ n)` |

**R54 · `rw [Real.sq_sqrt hx]`** changes the **goal**: `Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x`. Placeholders:
`(x : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `⊢ P (√x ^ 2)` | `⊢ P x` |

**R55 · `Nat.cast_nonneg n`** changes the **context**: `0 ≤ (↑n : ℝ)`; it is the `hx` of R54 at `x = ↑N`.
Write it as `Real.sq_sqrt (Nat.cast_nonneg N)`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ Q` | `hn : 0 ≤ ↑n ⊢ Q` |

**W7** (`x : ℝ`, `hx : 0 ≤ x`; the last `rw` closes the goal by `rfl`):

```lean-goal
⊢ (↑√x)⁻¹ ^ 2 = (↑x)⁻¹
⊢ (↑√x ^ 2)⁻¹ = (↑x)⁻¹
⊢ (↑(√x ^ 2))⁻¹ = (↑x)⁻¹
```

**R56 · `Matrix.one_apply`**: `(1 : Matrix n n ℂ) i j = if i = j then 1 else 0` changes the **goal**.
Placeholders: `{n : Type} [DecidableEq n] (i j : n)`.

| Before | After |
|---|---|
| `⊢ P (1 i j)` | `⊢ P (if i = j then 1 else 0)` |

The goal is now `((↑↑N)⁻¹ * if j = l then ↑N else 0) = if j = l then 1 else 0`. R22 splits it; the `j ≠ l` goal
`(↑↑N)⁻¹ * 0 = 0` is `simp`.

**R57 · `push_cast`** changes the **goal**: it moves casts toward the leaves and merges a cast of a cast
`((↑n : ℝ) : ℂ)` into `(↑n : ℂ)`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑↑n` | `⊢ P ↑n` |

**R58 · `inv_mul_cancel₀ ha`**: `a ≠ 0 → a⁻¹ * a = 1` changes the **goal** (or closes `a⁻¹ * a = 1` with
`exact`). Placeholders: `{G : Type} [GroupWithZero G] (a : G) (ha : a ≠ 0)`. Here `a = ↑N`, `ha = hN`.

| Before | After |
|---|---|
| `⊢ P (a⁻¹ * a)` | `⊢ P 1` |

---

## Traps

- Mathlib's `ZMod.dft` (notation `𝓕`) acts on functions `ZMod N → E`, not on this matrix; connecting it to the
  statement is as much work as the direct proof. Only `dft_dft` is banned.
- After `set ζ := … with hζ`, rewriting with a MILESTONE as stated produces `cexp (2 * ↑Real.pi * I / ↑N) ^ m`,
  not `ζ ^ m`: `set` only abbreviates what is already in the goal. The goal then mixes two spellings of the same
  number, and syntactic steps (`simp only [hconj]`, `set r := ζ ^ ↑j * …`) can miss the `cexp` one. Restate the
  MILESTONES with `ζ` first; the `have` is accepted because `ζ` unfolds:
  `have hpow : ∀ m : ℕ, cexp (2 * ↑Real.pi * I * ↑m / ↑N) = ζ ^ m := exp_eq_zeta_pow N`.
- `rw [h]` cannot rewrite under `∑ k, …`; use `simp only [h]` (R17) with `h` quantified over `k`.
- Do not `push_cast` the exponent `↑(↑j * ↑k)`: it splits into `↑↑j * ↑↑k`, and MILESTONE 1 (stated for one
  `↑m` with `m : ℕ`) no longer matches.
- `simp` writes `ζ⁻¹ ^ n` as `(ζ ^ n)⁻¹` (R24). Facts you feed it should use `(ζ ^ n)⁻¹`, or apply R24 yourself.
- `Fin.sum_univ_eq_sum_range` needs its function explicitly (R21).
- The infoview prints casts as `↑j`, which does not say the target type. In a `have` or `set` you type, write
  `(j : ℕ)` and `(N : ℂ)`: `ζ ^ (↑j * ↑k)` typed literally fails with `failed to synthesize HPow ℂ (Fin N) _`.
- `N = 0`: `Fin 0` is empty, so `N ≠ 0` comes from the index `j` you already have (R12, R13 or R42); never
  try to prove it outright.
- Two spellings of conjugation: `star z` and `(starRingEnd ℂ) z`. The `map_…` lemmas need the second (R48).
- `↑↑N` (ℕ → ℝ → ℂ) and `↑N` (ℕ → ℂ) are different terms: `inv_mul_cancel₀ hN` with `hN : (N : ℂ) ≠ 0` needs
  `push_cast` first (R57).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `exp x ^ n → exp (n * x)` | `rw [← Complex.exp_nat_mul]` | R1 |
| `exp a = exp b → a = b` | `congr 1` | R2 |
| field identity (with `/`) | `ring` | R3 |
| `conj (exp x) → exp (conj x)` / `(exp x)⁻¹ → exp (-x)` | `rw [← Complex.exp_conj, ← Complex.exp_neg]` | R4, R5 |
| push `conj` inward | `simp [Complex.conj_ofReal, map_div₀, map_ofNat]` | R6–R11 |
| `N ≠ 0` from `j : Fin N` | `rintro rfl; exact j.elim0` or `(Fin.pos j).ne'` | R12, R13, R42 |
| name a subterm | `set ζ := e with hζ` | R14 |
| `exp (2πi/n)` is a primitive root | `Complex.isPrimitiveRoot_exp n hn` | R15 |
| root ≠ 0 / `ζ ^ k = 1` / powers below `k` distinct | `hprim.ne_zero hk` / `hprim.pow_eq_one` / `hprim.pow_inj hi hj H` | R16, R31, R35 |
| rewrite under `∑` | `simp only [h]` | R17 |
| `conj (a ^ n)`, `conj a⁻¹`, `star (a * b)` | `map_pow`, `map_inv₀`, `star_mul'` | R18, R49, R47 |
| regroup powers | `mul_pow`, `pow_mul`, `← pow_mul`, `inv_pow`, `mul_comm a b` | R19, R20, R24, R30 |
| `Fin n` sum → `range n` sum | `rw [Fin.sum_univ_eq_sum_range (fun k => …) n]` | R21 |
| split an `if` | `split_ifs with h` | R22 |
| use `h : j = l` | `subst h` | R23 |
| `a * a⁻¹ = 1`, `a⁻¹ * a = 1` | `mul_inv_cancel₀ ha`, `inv_mul_cancel₀ ha` | R26, R58 |
| `a ^ n ≠ 0` | `pow_ne_zero _ ha` | R25 |
| sum of a constant | `simp` (`Finset.sum_const`, `Finset.card_range`, `nsmul_eq_mul`) | R27–R29 |
| from `False` to `A` with `h : ¬A` | `apply h` | R32 |
| rewrite a hypothesis | `rw [e] at h` | R33 |
| `a * b⁻¹ = 1 → a = b` | `(mul_inv_eq_one₀ hb).mp h` | R34 |
| `Fin` equality from values | `Fin.ext`, bounds `j.isLt` | R37, R36 |
| geometric sum | `rw [geom_sum_eq hr1, hrN, sub_self, zero_div]` | R38–R40 |
| unitary → equation | `rw [Matrix.mem_unitaryGroup_iff]` | R41 |
| `(N : ℂ) ≠ 0` | `Nat.cast_ne_zero.mpr hn` | R43 |
| expand a product entry | `simp only [Matrix.mul_apply, Matrix.star_apply, qft, Matrix.of_apply, star_mul', RCLike.star_def, map_inv₀, Complex.conj_ofReal]` | R44–R49, R9 |
| choose the middle term | `trans b` | R50 |
| move a constant into / out of a sum | `rw [Finset.mul_sum]` / `rw [← Finset.mul_sum]` | R51 |
| equal summands | `Finset.sum_congr rfl fun k _ => by ring` | R52 |
| `(√N)⁻¹ ^ 2 → N⁻¹` | `rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]` | R24, R53–R55 |
| identity entry → `if` | `rw [Matrix.one_apply]` | R56 |
| `↑↑N → ↑N` | `push_cast` | R57 |
| see the state | infoview | |
