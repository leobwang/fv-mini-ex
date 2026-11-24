# H085 · Qudit one-time pad (Weyl twirl): cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's integers mod `d` (`ZMod d`,
`.val`), matrices indexed by a finite type with entries in `ℂ` (`Matrix.of`, `ᴴ`, `•`, `trace`),
finite sums (`∑ x, …`, `Finset.range`), complex conjugation (`star`, `starRingEnd ℂ`), the complex
exponential and primitive roots of unity (`IsPrimitiveRoot`), bijections (`Equiv`), and the tactics
`subst`, `obtain`, `set`, `congr`, `simp_rw`, `split_ifs`, `by_cases`, `field_simp`, `simpa`.

**The math.** Fix `d ≥ 1`, index the basis of $\mathbb C^d$ by $j \in \mathbb Z_d$ (integers mod $d$),
and let $\omega = e^{2\pi i/d}$. For $a, b \in \mathbb Z_d$ the Weyl operator $W_{a,b} = X^aZ^b$ has
entries $(W_{a,b})_{ij} = [i = j + a]\,\omega^{b\,j}$ (one nonzero entry per row and column; $[\cdot]$ is
1 if true, else 0). For any $d\times d$ matrix $\rho$:

1. $(W\rho W^\dagger)_{ik} = \omega^{b(i-a)}\,\overline{\omega^{b(k-a)}}\,\rho_{i-a,\,k-a}$ (milestone `weyl_conj_apply`;
   $W^\dagger$ is the conjugate transpose, $\overline z$ the complex conjugate).
2. $\sum_{b \in \mathbb Z_d} f(b) = \sum_{k=0}^{d-1} f(k)$ when $b$ is read as its representative in $\{0,\dots,d-1\}$
   (milestone `zmod_sum_range`).
3. $\sum_b \omega^{bx}\,\overline{\omega^{by}} = \sum_{k<d} r^k$ with $r = \omega^{x}\omega^{-y}$; this is $d$ if $x = y$
   ($r = 1$), and $(r^d - 1)/(r - 1) = 0$ otherwise ($r \ne 1$ because $\omega$ is primitive, $r^d = 1$)
   (milestone `clock_sum`).
4. $\sum_a \rho_{i-a,\,i-a} = \operatorname{tr}\rho$, since $a \mapsto i - a$ is a bijection of $\mathbb Z_d$ (milestone `shift_sum`).
5. So $\frac1{d^2}\sum_{a,b} (W\rho W^\dagger)_{ik} = \frac1{d^2}\sum_a [i-a = k-a]\, d\, \rho_{i-a,k-a}$, which is
   $\frac{d\operatorname{tr}\rho}{d^2}$ if $i = k$ and $0$ otherwise: the matrix $(\operatorname{tr}\rho/d)\, I$ (`weyl_twirl`).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves alone.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommMonoid α]`
  is a requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ZMod d` | integers mod `d`, a commutative ring. For a literal `d = n + 1` it is `Fin (n + 1)`; for a variable `d` Lean cannot see that (`ZMod 0` is `ℤ`) |
| `[NeZero d]`, `inst✝ : NeZero d` | the instance "`d ≠ 0`" (so `ZMod d` is finite); `NeZero.ne d : d ≠ 0` extracts it. `inst✝` is an unnamed instance |
| `b.val` | `ZMod.val b : ℕ`, the representative of `b` in `{0, …, d-1}` |
| `↑d`, `↑k` | the natural number `d` cast into `ℂ` (and `↑i` for `i : Fin n` is `i.val : ℕ`) |
| `ω d`, `cexp (2 * ↑Real.pi * I / ↑d)` | $\omega = e^{2\pi i/d}$; `cexp` is `Complex.exp`, `I` is `Complex.I`, `↑Real.pi` is π cast into `ℂ` |
| `Matrix (ZMod d) (ZMod d) ℂ` | `d × d` complex matrices with rows and columns indexed by `ZMod d` |
| `of f i j`, `Matrix.of f` | the matrix whose `(i, j)` entry is `f i j` (R6) |
| `M i j` | entry in row `i`, column `j` |
| `Mᴴ` | conjugate transpose: `Mᴴ i j = star (M j i)` (R5) |
| `star z`, `(starRingEnd ℂ) z` | both the complex conjugate $\overline z$; Mathlib's conjugation lemmas use the second form (R13) |
| `c • M` | scalar `c` times every entry of `M` |
| `1` (a matrix) | the identity matrix; `1 i j = if i = j then 1 else 0` (R48) |
| `∑ x, f x` | sum over every element of a finite type (`Finset.univ`) |
| `∑ k ∈ Finset.range d, f k` | $\sum_{k=0}^{d-1} f(k)$ |
| `x_1` | a bound variable renamed to avoid a clash with `x` |
| `ρ.trace` | `Matrix.trace ρ = ∑ i, ρ i i` (R43) |
| `IsPrimitiveRoot ζ k` | `ζ ^ k = 1` and `ζ ^ l = 1` only for `k ∣ l` (`∣` is "divides") (R16) |
| `z⁻¹`, `(ω d ^ y.val)⁻¹` | the multiplicative inverse `1 / z` (Mathlib sets `0⁻¹ = 0`) |
| `Finset.univ`, `a ∈ Finset.univ` | the finite set of all elements of a finite type; membership is always true (R12) |
| `Finset.range d` | the finite set `{0, 1, …, d-1}` of natural numbers |
| `e : ι ≃ κ`, `Equiv.subLeft a` | a bijection with its inverse; `Equiv.subLeft a` is `x ↦ a - x` (R41, R42) |
| `r : ℂ := e` | a local definition made by `set` (R23): `r` stands for `e` |
| `case pos`, `case neg` | the two goals of `split_ifs` / `by_cases`: condition true, condition false |

---

## Part 1 · `weyl_conj_apply` (milestone)

Statement: `(weyl a b * ρ * (weyl a b)ᴴ) i k = ω d ^ (b.val * (i - a).val) * starRingEnd ℂ (ω d ^ (b.val * (k - a).val)) * ρ (i - a) (k - a)`.
Both matrix products become sums over `ZMod d`; in each sum only one term survives.

**R1 · `constructor`** on `A ↔ B` changes the **goal list**: prove both directions. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R2 · `subst h`** changes the **context** and the **goal**: for `h : x = e` with `x` a local variable not
occurring in `e`, it replaces `x` by `e` everywhere and removes `x` and `h`. Placeholders:
`{G : Type} [AddCommGroup G] (x j a : G)`; `ZMod d` meets `[AddCommGroup G]`.

| Before | After |
|---|---|
| `h : x = j + a ⊢ P x j` | `⊢ P (j + a) j` |

**R3 · `ring`** **closes** an identity of commutative rings, here in `ZMod d`. Placeholders: `{d : ℕ} (j a : ZMod d)`.

| Before | After |
|---|---|
| `⊢ j = j + a - a` | closed |

**R4 · `Matrix.mul_apply`** changes the **goal**: $(MN)_{ik} = \sum_j M_{ij}N_{jk}$. Placeholders:
`{n : Type} [Fintype n] (M N : Matrix n n ℂ) (i k : n)`; `ZMod d` with `[NeZero d]` meets `[Fintype n]`.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R5 · `Matrix.conjTranspose_apply`** changes the **goal**: `Mᴴ i j = star (M j i)`. Placeholders:
`{n : Type} (M : Matrix n n ℂ) (i j : n)`.

| Before | After |
|---|---|
| `⊢ P (Mᴴ i j)` | `⊢ P (star (M j i))` |

**R6 · `Matrix.of_apply`** changes the **goal**: `Matrix.of f i j = f i j`. To get there from `weyl a b`,
unfold the name first: `simp only [weyl, of_apply]`. Placeholders: `{n : Type} (f : n → n → ℂ) (i j : n)`.

| Before | After |
|---|---|
| `⊢ P (of f i j)` | `⊢ P (f i j)` |

**R7 · `simp only [h]`** with `h : ∀ x, p x ↔ q x` changes the **goal**: it rewrites the condition of an
`if`, also under a `∑`. This is how `i = j + a` becomes `j = i - a`, the shape R11 needs. Placeholders:
`{α : Type} (p q : α → Prop) [DecidablePred p] [DecidablePred q] (u v : ℂ) (x : α)`.

| Before | After |
|---|---|
| `⊢ P (if p x then u else v)` | `⊢ P (if q x then u else v)` |

**R8 · `simp only [ite_mul, zero_mul]`** changes the **goal**: a factor moves into the `if`. Lemma
`ite_mul : (if c then a else b) * x = if c then a * x else b * x`. Placeholders:
`(c : Prop) [Decidable c] (a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((if c then a else 0) * b)` | `⊢ P (if c then a * b else 0)` |

**R9 · `simp only [mul_ite, mul_zero]`** changes the **goal**: the mirror image of R8. Placeholders as R8.

| Before | After |
|---|---|
| `⊢ P (b * if c then a else 0)` | `⊢ P (if c then b * a else 0)` |

**R10 · `simp only [apply_ite (star : ℂ → ℂ), star_zero]`** changes the **goal**: `star` moves into the `if`.
Lemma `apply_ite f : f (if c then x else y) = if c then f x else f y`; name `f`, or `simp` cannot guess it.
Placeholders: `(c : Prop) [Decidable c] (a : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star (if c then a else 0))` | `⊢ P (if c then star a else 0)` |

**R11 · `Finset.sum_ite_eq'`** changes the **goal**: a sum with one possibly nonzero term collapses.
Lemma `(∑ x ∈ s, if x = a then f x else 0) = if a ∈ s then f a else 0` (unprimed version: `a = x`).
Placeholders: `{ι : Type} [Fintype ι] [DecidableEq ι] (a : ι) (f : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, if x = a then f x else 0)` | `⊢ P (if a ∈ Finset.univ then f a else 0)` |

**R12 · `simp only [Finset.mem_univ, if_true]`** changes the **goal**: `a ∈ Finset.univ` is `True`, so the `if`
takes its first branch. Placeholders: `{ι : Type} [Fintype ι] [DecidableEq ι] (a : ι) (u v : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (if a ∈ Finset.univ then u else v)` | `⊢ P u` |

**R13 · `RCLike.star_def`** changes the **goal**: `star = starRingEnd ℂ` (on `ℂ`; `RCLike` covers `ℝ` and `ℂ`).
Use it so that conjugation lemmas such as R24 apply; `simp [RCLike.star_def]` then also applies R24 by itself.
Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star z)` | `⊢ P ((starRingEnd ℂ) z)` |

After R13 the two sides differ only by the order of factors: `ring`.

**W4: collapsing a sum** (R8, R11, R12 on `∑ x, (if x = a then f x else 0) * g x`):

```lean-goal
⊢ ∑ x, (if x = a then f x else 0) * g x = f a * g a
⊢ (∑ x, if x = a then f x * g x else 0) = f a * g a
⊢ (if a ∈ Finset.univ then f a * g a else 0) = f a * g a
```

---

## Part 2 · `zmod_sum_range` (milestone)

Statement: `∑ b : ZMod d, f b.val = ∑ k ∈ Finset.range d, f k` for `f : ℕ → ℂ`. Mathlib has this for
`Fin n` (R15); `ZMod (n + 1)` is `Fin (n + 1)` by definition, so make `d` a successor first (R14).

**R14 · `obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)`** changes the
**context**: `d` is replaced by `n + 1` everywhere. `Nat.exists_eq_succ_of_ne_zero : n ≠ 0 → ∃ k, n = k.succ`;
the pattern `rfl` substitutes at once (as R2). Placeholders: `(d : ℕ) [NeZero d]`.

| Before | After |
|---|---|
| `inst✝ : NeZero d ⊢ P d` | `n : ℕ, inst✝ : NeZero (n + 1) ⊢ P (n + 1)` |

**R15 · `Fin.sum_univ_eq_sum_range`** changes the **goal**: `∑ i : Fin n, f ↑i = ∑ i ∈ Finset.range n, f i`.
Placeholders: `(f : ℕ → ℂ) (n : ℕ)`. In the milestone, use it with `exact Fin.sum_univ_eq_sum_range f (n + 1)`:
the goal has `ZMod (n + 1)` and `b.val`, which are the same as `Fin (n + 1)` and `↑b` only after unfolding,
and `exact` unfolds while `rw` does not (W1).

| Before | After |
|---|---|
| `⊢ P (∑ i, f ↑i)` | `⊢ P (∑ i ∈ Finset.range n, f i)` |

**W1.** For the literal modulus `4`, `exact Fin.sum_univ_eq_sum_range f 4` closes
`∑ b : ZMod 4, f b.val = ∑ k ∈ Finset.range 4, f k` directly.

---

## Part 3 · `clock_sum` (milestone)

Statement: `∑ b : ZMod d, ω d ^ (b.val * x.val) * starRingEnd ℂ (ω d ^ (b.val * y.val)) = if x = y then (d : ℂ) else 0`.
Plan: `conj ω = ω⁻¹`, so every term is `r ^ b.val` with `r = ω ^ x.val * (ω ^ y.val)⁻¹`; then Part 2 and a
geometric sum.

### Facts about `ω`

**R16 · `Complex.isPrimitiveRoot_exp`** is a **term** (here added to the **context** with `have`):
`Complex.isPrimitiveRoot_exp n (hn : n ≠ 0) : IsPrimitiveRoot (cexp (2 * ↑π * I / ↑n)) n`. Since `ω d` unfolds
to that exponential, `have hp : IsPrimitiveRoot (ω d) d := Complex.isPrimitiveRoot_exp d (NeZero.ne d)` is
accepted. Placeholders: `(n : ℕ) (hn : n ≠ 0)`.

| Before | After |
|---|---|
| `⊢ G` | `hp : IsPrimitiveRoot (cexp (2 * ↑Real.pi * I / ↑n)) n ⊢ G` |

**R17 · `IsPrimitiveRoot.ne_zero`** is a **term**: `hp.ne_zero (hk : k ≠ 0) : ζ ≠ 0`. Placeholders:
`(ζ : ℂ) (k : ℕ) (hp : IsPrimitiveRoot ζ k)`.

| Before | After |
|---|---|
| `⊢ ζ ≠ 0` | closed by `exact hp.ne_zero hk` |

**R18 · `unfold D`** changes the **goal**: a defined name is replaced by its body (here `unfold ω`).
Placeholders: `D` defined by `noncomputable def D (t : ℝ) : ℂ := Complex.exp (t * Complex.I)`.

| Before | After |
|---|---|
| `⊢ P (D t)` | `⊢ P (cexp (↑t * I))` |

**R19 · `rw [← Complex.exp_conj]`** changes the **goal**. Lemma `Complex.exp_conj : cexp (conj x) = conj (cexp x)`,
used right to left. Placeholders: `(x : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (cexp x))` | `⊢ P (cexp ((starRingEnd ℂ) x))` |

**R20 · `rw [← Complex.exp_neg]`** changes the **goal**. Lemma `Complex.exp_neg : cexp (-x) = (cexp x)⁻¹`.
Placeholders: `(x : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (cexp x)⁻¹` | `⊢ P (cexp (-x))` |

**R21 · `congr 1`** changes the **goal**: `f a = f b` becomes `a = b` (sufficient, not equivalent).
It closes the new goal itself when it is a hypothesis or `rfl`. Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ cexp a = cexp b` | `⊢ a = b` |

**R22 · `simp [map_ofNat]`** changes the **goal**: the conjugate is pushed through `*` and `/`, real and
natural casts are fixed (`Complex.conj_ofReal`, `map_natCast`), `conj I = -I` (`Complex.conj_I`), and `map_ofNat`
fixes the numeral `2`. Placeholders: `(r : ℝ) (n : ℕ)`. What remains is `-(u) / v = -(u / v)`: `ring`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (2 * ↑r * I / ↑n))` | `⊢ P (-(2 * ↑r * I) / ↑n)` |

**W3: `conj (cexp (t * I)) = (cexp (t * I))⁻¹`** by R19, R20, R21, then `simp`:

```lean-goal
⊢ (starRingEnd ℂ) (cexp (↑t * I)) = (cexp (↑t * I))⁻¹
⊢ cexp ((starRingEnd ℂ) (↑t * I)) = cexp (-(↑t * I))
⊢ (starRingEnd ℂ) (↑t * I) = -(↑t * I)
```

### Turning every term into `r ^ b.val`

**R23 · `set r := e with hr`** changes the **goal** and the **context**: every `e` becomes `r`, and the context
gains `r : ℂ := e` and `hr : r = e`. Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (a * b⁻¹)` | `r : ℂ := a * b⁻¹, hr : r = a * b⁻¹ ⊢ P r` |

**R24 · `rw [map_pow]`** changes the **goal**: `conj (a ^ n) = conj a ^ n` (any ring hom commutes with powers).
Placeholders: `(a : ℂ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (a ^ n))` | `⊢ P ((starRingEnd ℂ) a ^ n)` |

**R25 · `rw [mul_pow]`** changes the **goal**: `(a * b) ^ n = a ^ n * b ^ n`. Placeholders:
`{α : Type} [CommMonoid α] (a b : α) (n : ℕ)`; `ℂ` qualifies.

| Before | After |
|---|---|
| `⊢ P ((a * b) ^ n)` | `⊢ P (a ^ n * b ^ n)` |

**R26 · `rw [inv_pow]`** changes the **goal**: `a⁻¹ ^ n = (a ^ n)⁻¹`. Placeholders:
`{α : Type} [DivisionMonoid α] (a : α) (n : ℕ)`; `ℂ` qualifies.

| Before | After |
|---|---|
| `⊢ P (a⁻¹ ^ n)` | `⊢ P (a ^ n)⁻¹` |

**R27 · `rw [← pow_mul]`** changes the **goal**. Lemma `pow_mul : a ^ (m * n) = (a ^ m) ^ n`; `←` merges two
powers, plain `rw [pow_mul]` splits one. Placeholders: `{α : Type} [Monoid α] (a : α) (m n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((a ^ m) ^ n)` | `⊢ P (a ^ (m * n))` |

**R28 · `rw [mul_comm m]`** changes the **goal**: the first product whose left factor is `m` is turned around.
`mul_comm a b : a * b = b * a`; fixing `a` chooses which product. Placeholders: `(m n k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (m * n + k * n)` | `⊢ P (n * m + k * n)` |

**R29 · `simp_rw [h]`** changes the **goal**: it rewrites with `h : ∀ i, f i = g i` under the binder of a `∑`,
where `rw [h]` fails. Placeholders: `{ι : Type} [Fintype ι] (f g : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (∑ x, g x)` |

### The two cases

**R30 · `split_ifs with h`** changes the **goal list**: the goal containing `if c then a else b` splits into
the `c` case and the `¬c` case. Placeholders: `(c : Prop) [Decidable c] (a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (if c then a else b)` | `h : c ⊢ P a`, `h : ¬c ⊢ P b` |

In the case `h : x = y`, `subst h` (R2) makes both exponents equal, so `r = ω ^ x.val * (ω ^ x.val)⁻¹`.

**R31 · `rw [mul_inv_cancel₀ ha]`** changes the **goal**: `a ≠ 0 → a * a⁻¹ = 1`. Placeholders: `(a : ℂ) (ha : a ≠ 0)`.
In the exercise `simp [hr, hne]` finds it (with `pow_ne_zero`, R35, from `hne`).

| Before | After |
|---|---|
| `⊢ P (a * a⁻¹)` | `⊢ P 1` |

**R32 · `simp`** on a sum of ones changes the **goal**: `∑ k ∈ Finset.range n, 1 ^ k` becomes `↑n`
(`one_pow`, `Finset.sum_const`, `Finset.card_range`, `nsmul_eq_mul`). Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (∑ k ∈ Finset.range n, 1 ^ k)` | `⊢ P ↑n` |

**R33 · `intro h`** on `a ≠ b` changes the **context** and the **goal**: `a ≠ b` is `a = b → False`.
Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ a ≠ b` | `h : a = b ⊢ False` |

**R34 · `rw [mul_inv_eq_one₀ hb] at h`** changes the **context**. Lemma
`mul_inv_eq_one₀ (hb : b ≠ 0) : a * b⁻¹ = 1 ↔ a = b`; `rw` with an `↔` replaces one proposition by the other.
Placeholders: `(a b : ℂ) (hb : b ≠ 0)`. In the exercise `hb` is `pow_ne_zero _ hne` (R35).

| Before | After |
|---|---|
| `h : a * b⁻¹ = 1 ⊢ G` | `h : a = b ⊢ G` |

**R35 · `pow_ne_zero n ha`** is a **term**: `a ≠ 0 → a ^ n ≠ 0`. Placeholders: `(a : ℂ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ a ^ n ≠ 0` | closed by `exact pow_ne_zero n ha` |

**R36 · `hp.pow_inj hi hj h`** is a **term** (`IsPrimitiveRoot.pow_inj`): for a primitive `k`-th root `ζ`,
`i < k → j < k → ζ ^ i = ζ ^ j → i = j`. Placeholders: `(ζ : ℂ) (k i j : ℕ) (hp : IsPrimitiveRoot ζ k)`.

| Before | After |
|---|---|
| `⊢ i = j` | closed by `exact hp.pow_inj hi hj h` |

**R37 · `ZMod.val_lt x`** is a **term**: `x.val < n` for `x : ZMod n` with `[NeZero n]`. It supplies `hi`, `hj` of R36.

| Before | After |
|---|---|
| `⊢ x.val < n` | closed by `exact ZMod.val_lt x` |

**R38 · `ZMod.val_injective n h`** is a **term**: `x.val = y.val → x = y`. `Function.Injective f` means
`∀ a b, f a = f b → a = b`, with `a b` implicit. Chain: `ZMod.val_injective _ (hp.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h1)`.

| Before | After |
|---|---|
| `⊢ x = y` | closed by `exact ZMod.val_injective n h` |

**R39 · `rw [hp.pow_eq_one]`** changes the **goal**: `IsPrimitiveRoot.pow_eq_one : ζ ^ k = 1`. To use it on
`(ω ^ x.val) ^ d`, first reorder the exponent with R27, R28, R27 (forward) into `(ω ^ d) ^ x.val`.
Placeholders: `(ζ : ℂ) (k : ℕ) (hp : IsPrimitiveRoot ζ k)`.

| Before | After |
|---|---|
| `⊢ P (ζ ^ k)` | `⊢ P 1` |

**R40 · `rw [geom_sum_eq hx]`** changes the **goal**. Lemma
`geom_sum_eq (hx : x ≠ 1) (n : ℕ) : ∑ i ∈ range n, x ^ i = (x ^ n - 1) / (x - 1)` (in a field such as `ℂ`).
Placeholders: `(x : ℂ) (hx : x ≠ 1) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ Finset.range n, x ^ i)` | `⊢ P ((x ^ n - 1) / (x - 1))` |

**W2: the geometric sum of a primitive root `ζ ≠ 1` vanishes** (R40, R39, then `simp` closes `(1 - 1) / _ = 0`):

```lean-goal
⊢ ∑ i ∈ Finset.range k, ζ ^ i = 0
⊢ (ζ ^ k - 1) / (ζ - 1) = 0
⊢ (1 - 1) / (ζ - 1) = 0
```

---

## Part 4 · `shift_sum` (milestone)

Statement: `∑ a, ρ (i - a) (i - a) = ρ.trace`. Reindex by the bijection `a ↦ i - a`.

**R41 · `Equiv.sum_comp`** changes the **goal**: `∑ i, g (e i) = ∑ i, g i` for a bijection `e : ι ≃ κ`.
Placeholders: `{ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (g : κ → ℂ)`. In the milestone, give `e` and
`g` explicitly and close with `exact` (W5): the goal matches `g (e a)` for `g := fun j => ρ j j` only after
unfolding R42 and R43, which `exact` does and `rw` does not.

| Before | After |
|---|---|
| `⊢ P (∑ i, g (e i))` | `⊢ P (∑ i, g i)` |

**R42 · `Equiv.subLeft_apply`** changes the **goal**: `(Equiv.subLeft a) x = a - x`. Placeholders:
`{G : Type} [AddGroup G] (a x : G)`; `ZMod d` qualifies.

| Before | After |
|---|---|
| `⊢ P ((Equiv.subLeft a) x)` | `⊢ P (a - x)` |

**R43 · `simp only [Matrix.trace, Matrix.diag]`** changes the **goal**: `M.trace` is by definition
`∑ i, M.diag i` and `M.diag i = M i i`. Placeholders: `{n : Type} [Fintype n] (M : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P M.trace` | `⊢ P (∑ x, M x x)` |

**W5.** `exact Equiv.sum_comp (Equiv.subLeft a) g` closes `∑ x, g (a - x) = ∑ x, g x` over `ZMod 5`.

---

## Part 5 · `weyl_twirl`

Statement: `(1 / (d : ℂ) ^ 2) • ∑ a, ∑ b, weyl a b * ρ * (weyl a b)ᴴ = (ρ.trace / d) • 1`. Work entrywise
(`ext i k`, as in `TACTIC_STATES.md`, with indices in `ZMod d`), then use the four milestones.

**R44 · `Nat.cast_ne_zero.mpr hn`** is a **term**: `Nat.cast_ne_zero : (↑n : R) ≠ 0 ↔ n ≠ 0` (in `ℂ`, `ℝ`, any
characteristic-zero ring); `.mpr` uses it right to left. Gives the `hd : (d : ℂ) ≠ 0` that R51 needs.

| Before | After |
|---|---|
| `⊢ ↑n ≠ 0` | closed by `exact Nat.cast_ne_zero.mpr hn` |

**R45 · `simp only [Matrix.smul_apply, smul_eq_mul]`** changes the **goal**: an entry of `c • M` becomes
`c * M i j`. Placeholders: `{n : Type} (c : ℂ) (M : Matrix n n ℂ) (i j : n)`.

| Before | After |
|---|---|
| `⊢ P ((c • M) i j)` | `⊢ P (c * M i j)` |

**R46 · `Matrix.sum_apply`** changes the **goal**: `(∑ c ∈ s, g c) i j = ∑ c ∈ s, g c i j`. Placeholders:
`{n ι : Type} [Fintype ι] (g : ι → Matrix n n ℂ) (i j : n)`.

| Before | After |
|---|---|
| `⊢ P ((∑ c, g c) i j)` | `⊢ P (∑ c, g c i j)` |

**R47 · `rw [← Finset.sum_mul]`** changes the **goal**: a common right factor leaves the sum. Lemma
`Finset.sum_mul : (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`. In the exercise this isolates
`∑ b, ω … * conj (ω …)`, the left side of `clock_sum`. Placeholders: `{ι : Type} [Fintype ι] (f : ι → ℂ) (a : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i * a)` | `⊢ P ((∑ i, f i) * a)` |

**R48 · `Matrix.one_apply`** changes the **goal**: `(1 : Matrix n n α) i j = if i = j then 1 else 0`.
Placeholders: `{n : Type} [DecidableEq n] (i j : n)`.

| Before | After |
|---|---|
| `⊢ P (1 i j)` | `⊢ P (if i = j then 1 else 0)` |

After one `simp only` with R45, R46, milestone 1, R47, milestone 3 and R48, the entry goal of the exercise is
`1 / ↑d ^ 2 * ∑ x, (if i - x = k - x then ↑d else 0) * ρ (i - x) (k - x) = ρ.trace / ↑d * if i = k then 1 else 0`.

**R49 · `by_cases h : c`** changes the **goal list**: one copy of the goal with `h : c`, one with `h : ¬c`.
Placeholders: `(c G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h : c ⊢ G`, `h : ¬c ⊢ G` |

Case `i = k`: `subst` (R2); `if_true` fires because `i - x = i - x` simplifies to `True`.

**R50 · `rw [← Finset.mul_sum]`** changes the **goal**: a common left factor leaves the sum. Lemma
`Finset.mul_sum : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`. Then milestone 4 turns the sum into the trace.
Placeholders: `{ι : Type} [Fintype ι] (f : ι → ℂ) (a : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, a * f i)` | `⊢ P (a * ∑ i, f i)` |

**R51 · `field_simp`** **closes** (or multiplies out the denominators of) an equation in a field, using the
`x ≠ 0` hypotheses in the context for the denominators. Placeholders: `(x y : ℂ) (hx : x ≠ 0)`.

| Before | After |
|---|---|
| `⊢ 1 / x ^ 3 * (x * y) = y / x ^ 2 * 1` | closed |

Case `i ≠ k`: first `have this : ∀ a : ZMod d, ¬ (i - a = k - a)` (R33 for the `¬`, then R52).

**R52 · `simpa using h`** **closes** the goal: it simplifies `h` and the goal with the same `simp` set and
closes the goal with the result. Here `simp` uses `sub_left_inj : a - b = c - b ↔ a = c`. Placeholders:
`{G : Type} [AddCommGroup G] (x y a : G) (h : x - a = y - a)`.

| Before | After |
|---|---|
| `⊢ x = y` | closed |

**R53 · `rw [if_neg hc]`** changes the **goal**: with `hc : ¬c`, `if c then a else b` becomes `b`.
`simp [this, hik]` does this inside the `∑` and then removes `0 * x`, `∑ x, 0` and `x * 0`.
Placeholders: `(c : Prop) [Decidable c] (hc : ¬c) (a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (if c then a else b)` | `⊢ P b` |

---

## Traps

- `ZMod d` is not `Fin d` for a variable `d`: Lean cannot unfold `ZMod d` until `d` has the form `n + 1`. Use
  R14 first, then close with `exact`, not `rw` (R15, W1).
- `Finset.sum_ite_eq'` wants `x = a` with the summation variable on the left; `weyl` gives `i = j + a`.
  Rewrite the condition to `j = i - a` first (R7 with a `∀ x j` iff proved by R1, `intro`, R2, R3).
- `star z` and `(starRingEnd ℂ) z` are the same conjugate, but `rw` and `simp` lemmas are stated for one form.
  R13 turns `star` into `starRingEnd ℂ`.
- `rw [h]` cannot rewrite under `∑ b, …` when `h : ∀ b, …`; use `simp_rw [h]` (R29).
- `rw [hp.pow_eq_one]` needs `ω ^ d` literally; `(ω ^ x.val) ^ d` must first become `(ω ^ d) ^ x.val` (R27, R28).
- A `have` belongs to one proof: `hd`, `hp`, `hne` must be proved inside the theorem that uses them.
- `set` keeps `r` as a local definition: `simp` sees through it only when you also pass `hr`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove an `↔` | `constructor` | R1 |
| use `h : x = e` | `subst h` | R2 |
| identity in `ZMod d` | `ring` | R3 |
| entries of `M * N`, `Mᴴ`, `Matrix.of f` | `simp only [mul_apply, conjTranspose_apply, name, of_apply]` | R4, R5, R6 |
| change an `if` condition | `simp only [h]` with `h : ∀ x j, _ ↔ _` | R7 |
| move factors / `star` into an `if` | `ite_mul, zero_mul, mul_ite, mul_zero, apply_ite (star : ℂ → ℂ), star_zero` | R8–R10 |
| collapse `∑ x, if x = a then f x else 0` | `Finset.sum_ite_eq', Finset.mem_univ, if_true` | R11, R12 |
| `star` → `starRingEnd ℂ` | `simp [RCLike.star_def]` | R13 |
| make `d` a successor | `obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)` | R14 |
| `Fin` sum → `range` sum | `exact Fin.sum_univ_eq_sum_range f (n + 1)` | R15 |
| `ω` is a primitive root, nonzero | `Complex.isPrimitiveRoot_exp d (NeZero.ne d)`, `hp.ne_zero` | R16, R17 |
| `conj (cexp x) = (cexp x)⁻¹` for imaginary `x` | `unfold`, `rw [← Complex.exp_conj, ← Complex.exp_neg]`, `congr 1`, `simp [map_ofNat]`, `ring` | R18–R22 |
| name a subterm | `set r := e with hr` | R23 |
| power algebra | `map_pow, mul_pow, inv_pow, ← pow_mul, mul_comm m` | R24–R28 |
| rewrite under `∑` | `simp_rw [h]` | R29 |
| split on an `if` in the goal | `split_ifs with h` | R30 |
| `a * a⁻¹`, `∑ 1 ^ k` | `simp [hr, hne]` | R31, R32 |
| prove `≠` | `intro h` | R33 |
| `a * b⁻¹ = 1` → `a = b` | `rw [mul_inv_eq_one₀ (pow_ne_zero _ hne)] at h` | R34, R35 |
| equal powers → equal `ZMod` | `ZMod.val_injective _ (hp.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h)` | R36–R38 |
| `ζ ^ k = 1`, geometric sum | `rw [hp.pow_eq_one]`, `rw [geom_sum_eq hr1]` | R39, R40 |
| reindex by `a ↦ i - a` | `exact Equiv.sum_comp (Equiv.subLeft i) g` | R41–R43 |
| `(d : ℂ) ≠ 0` | `Nat.cast_ne_zero.mpr (NeZero.ne d)` | R44 |
| entries of `c • M`, `∑ M`, `1` | `Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, one_apply` | R45, R46, R48 |
| pull a factor out of `∑` | `← Finset.sum_mul`, `← Finset.mul_sum` | R47, R50 |
| case split on `i = k` | `by_cases hik : i = k` | R49 |
| clear denominators | `field_simp` | R51 |
| `i - a = k - a → i = k` | `simpa using h` | R52 |
| drop a false `if` | `rw [if_neg hc]` / `simp [hc]` | R53 |
| see the state | infoview | |
