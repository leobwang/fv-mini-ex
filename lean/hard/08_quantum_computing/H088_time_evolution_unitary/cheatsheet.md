# H088 · Time evolution: exp(−iθX/2) and unitarity: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). M126 (the Hadamard gate) helps: it introduces 2×2
matrices, `ext`/`fin_cases` and `simp [names, Matrix.mul_apply, Fin.sum_univ_two]`, which are repeated
here as R2–R6. **New here:** Mathlib's matrix exponential `NormedSpace.exp`, units `αˣ` (invertible
elements), diagonal matrices, conjugate transposes of scalar multiples, Hermitian matrices, `Commute`,
the unitary group, and the complex `cexp`, `cos`, `sin`.

**The math.** For a square matrix $A$, $e^A = \sum_{k \ge 0} A^k / k!$ (Lean: `NormedSpace.exp A`).

1. $X = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ is diagonalised by $V = \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$,
   with $V^{-1} = \tfrac12 V$: $\;cX = V \operatorname{diag}(c, -c)\, V^{-1}$ for every $c \in \mathbb C$
   (milestones `HU` = $V$ as a unit, `diag_conj`).
2. $e^{VAV^{-1}} = V e^{A} V^{-1}$ (R23), and $e^{\operatorname{diag}(v)} = \operatorname{diag}(e^{v_0}, e^{v_1})$
   (R12–R14, milestone `exp_diag`).
3. With $c = -i\theta/2$: $e^{c} = \cos\frac\theta2 - i\sin\frac\theta2$ and $e^{-c} = \cos\frac\theta2 + i\sin\frac\theta2$
   (Euler, R26). Multiplying out $V \operatorname{diag}(e^c, e^{-c}) V^{-1}$ gives entries
   $\frac{e^c + e^{-c}}2 = \cos\frac\theta2$ on the diagonal and $\frac{e^c - e^{-c}}2 = -i\sin\frac\theta2$
   off it: that is $R_x(\theta)$ (`time_evolution`).
4. For Hermitian $H$ ($H^\dagger = H$) and real $t$, $A = -itH$ has $A^\dagger = \overline{(-it)}\,H = itH = -A$
   (milestone `star_gen`). So $U = e^A$ has $U^\dagger = e^{A^\dagger} = e^{-A}$ (R32) and, because $A$ commutes
   with $-A$, $UU^\dagger = e^{A}e^{-A} = e^{A + (-A)} = e^0 = 1$ (R33–R36, `evolution_unitary`).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves alone.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it. `{m : Type} [Fintype m]
  [DecidableEq m]` is an index type for square matrices: finite (so sums and `exp` make sense), with decidable
  `=` (needed for `1` and `diagonal`). `Fin 2` and `Fin 3` qualify.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix m m ℂ`, `Matrix (Fin 2) (Fin 2) ℂ` | square complex matrices with rows and columns indexed by `m` (here `Fin 2 = {0, 1}`) |
| `!![a, b; c, d]`, `![a, b]` | the 2×2 matrix with rows `a b` and `c d`; the vector `(a, b)` (a function `Fin 2 → α`) |
| `M i j` | the entry in row `i`, column `j`, counted from 0 |
| `c • M` | scalar `c` times every entry of `M` |
| `diagonal v` | the matrix with `v i` at `(i, i)` and `0` elsewhere |
| `v ᵥ* M` | row vector `v` times matrix `M`: $(vM)_j = \sum_i v_i M_{ij}$ (R10) |
| `∑ j, f j` | the sum of `f j` over every `j` of the (finite) index type, here `Fin 2` (R4, R5) |
| `2⁻¹` | the inverse `1 / 2`; `simp` writes `1 / 2` this way |
| `-a * b`, `-↑t * I` | `(-a) * b`: unary minus binds tighter than `*`, so `-↑t * I` is $(-t)\,i$ (R28) |
| `NormedSpace.exp A` | the exponential series $\sum_k A^k/k!$; it also applies to vectors (entrywise, R13) and to `ℂ` |
| `cexp z`, `cos z`, `sin z` | `Complex.exp`, `Complex.cos`, `Complex.sin` of a complex `z` (`open Complex` shortens the names) |
| `Real.cos x`, `↑x` | the real cosine; `x : ℝ` cast into `ℂ`. `↑(Real.cos x)` becomes `cos ↑x` under `simp` (R29) |
| `I` | `Complex.I`, the imaginary unit |
| `αˣ`, `(Matrix m m ℂ)ˣ` | the *units* of `α`: an element together with a two-sided inverse (R1) |
| `↑U`, `↑U⁻¹` | for `U : αˣ`, the element itself and its inverse, as elements of `α` (coercions) |
| `{ val := a, inv := b, val_inv := h₁, inv_val := h₂ }` | the unit built from `a`, its inverse `b`, and the proofs `a * b = 1`, `b * a = 1` (R8, R9) |
| `Mᴴ` | conjugate transpose $M^\dagger$: `Mᴴ i j = star (M j i)` |
| `star c`, `(starRingEnd ℂ) z` | the complex conjugate $\bar c$; the second is how `conj z` prints (R19) |
| `M.IsHermitian` | `Mᴴ = M`; for `hM : M.IsHermitian`, `hM.eq : Mᴴ = M` (R16) |
| `Commute A B` | `A * B = B * A` (R33) |
| `unitaryGroup m ℂ` | the unitary matrices, `M * star M = 1` (R30) |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases` |
| `i : Fin (Nat.succ 0).succ` | `i : Fin 2`, printed this way after `funext` on a `![a, b]` |
| `case «0».«1»` | the goal for entry (0, 1) |
| `case e_a` | the goal `congr 1` leaves for the argument that differs (here the scalar, R18) |
| `inst✝ : Fintype n` | an unnamed instance hypothesis from a `[Fintype n]` binder: `n` is a finite type |

---

## Part 1 · `HU`

`HU` is `!![1, 1; 1, -1]` packaged as a unit with inverse `(1 / 2 : ℂ) • !![1, 1; 1, -1]`. The two `sorry`s are
the proofs `val * inv = 1` and `inv * val = 1`; each is a 2×2 matrix equation.

**R1 · `refine ⟨a, b, ?_, ?_⟩`** changes the **goal list**: building a unit `αˣ` leaves one goal per proof
field. In the term `⟨a, b, sorry, sorry⟩` of the exercise, replace each `sorry` by `by …`; inside it you see the
same goal. Placeholders: `{α : Type} [Monoid α] (a b : α)` (α has an associative `*` with `1`; matrices do).

| Before | After |
|---|---|
| `⊢ αˣ` | `⊢ a * b = 1`, `⊢ b * a = 1` |

**R2 · `ext i j`** changes the **goal and the context**. It uses `Matrix.ext`: two matrices are equal when
every entry is. Placeholders: `{α : Type} (M N : Matrix (Fin 2) (Fin 2) α)`.

| Before | After |
|---|---|
| `⊢ M = N` | `i j : Fin 2 ⊢ M i j = N i j` |

**R3 · `fin_cases i`** changes the **goal list and the context**: `i` leaves the context, and there is one goal
for each value `0, 1`. Placeholders: `(P : Fin 2 → Prop)`. Use `fin_cases i <;> fin_cases j` for all four entries.

| Before | After |
|---|---|
| `i : Fin 2 ⊢ P i` | `⊢ P ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩)` |

**R4 · `Matrix.mul_apply`** changes the **goal**: an entry of a product becomes a sum over the middle index,
$(MN)_{ik} = \sum_j M_{ij} N_{jk}$. Placeholders: `{α : Type} [Mul α] [AddCommMonoid α]` (`ℂ` qualifies),
`(M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R5 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms. Placeholders:
`{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R6 · `simp` on an entry of a scaled literal** changes the **goal**: `simp` reads off the entry of `!![…]`
(`Matrix.of_apply`, `Matrix.cons_val_…`) and turns `•` into `*` (`Matrix.smul_apply`, `smul_eq_mul`). It also
writes `1 / 2` as `2⁻¹`. Placeholders: `(c a b d e : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((c • !![a, b; d, e]) 0 1)` | `⊢ P (c * b)` |

**R7 · `norm_num`** **closes** a goal made of numerals, `⁻¹` and `/` included, such as `3⁻¹ + 3⁻¹ + 3⁻¹ = 1`.
After `simp [Matrix.mul_apply, Fin.sum_univ_two]`, each entry of `HU`'s proof fields is such a goal (or is
already closed).

---

## Part 2 · `diag_conj`

Statement: `c • X = ↑HU * diagonal ![c, -c] * ↑HU⁻¹`, a 2×2 matrix equation. Reduce it to entries (R2, R3),
then `simp` with `X`, `HU`, R4, R5 and R10, then R11.

**R8 · `Units.val_mk`** changes the **goal**: the element of a unit built with `⟨a, b, h₁, h₂⟩` is `a`.
Statement: `↑(⟨a, b, h₁, h₂⟩ : αˣ) = a`. `simp [HU]` applies it by itself. Placeholders:
`{α : Type} [Monoid α] (a b : α) (h₁ : a * b = 1) (h₂ : b * a = 1)`.

| Before | After |
|---|---|
| `⊢ P ↑{ val := a, inv := b, val_inv := h₁, inv_val := h₂ }` | `⊢ P a` |

**R9 · `Units.inv_mk`, then R8** changes the **goal**: the inverse of `⟨a, b, h₁, h₂⟩` is `⟨b, a, h₂, h₁⟩`, whose
element is `b`. `simp [HU]` applies both. Same placeholders as R8.

| Before | After |
|---|---|
| `⊢ P ↑{ val := a, inv := b, val_inv := h₁, inv_val := h₂ }⁻¹` | `⊢ P b` |

**R10 · `Matrix.vecMul_diagonal`** changes the **goal**: a row vector times a diagonal matrix, read at index `x`,
is `v x * w x`. Statement: `(v ᵥ* diagonal w) x = v x * w x`. `simp` rewrites an entry of `M * diagonal w * N`
into this `ᵥ*` form and stops there unless you pass this lemma (W4). Placeholders: `(v w : Fin 2 → ℂ) (x : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P ((v ᵥ* diagonal w) x)` | `⊢ P (v x * w x)` |

**R11 · `ring`** **closes** an equation that holds in every commutative ring. Numerals such as `2⁻¹` are fine;
`I`, `cos x`, `sin x` are treated as unknowns (so it knows neither `I * I = -1` nor `cos² + sin² = 1`).
Example: `(a + b) * 2⁻¹ + (a - b) * 2⁻¹ = a`.

---

## Part 3 · `exp_diag`

Statement: `NormedSpace.exp (diagonal v) = diagonal (fun i => cexp (v i))`. Three rewrites: R12 → R13 → R14.

**R12 · `rw [Matrix.exp_diagonal]`** changes the **goal**. Statement: `exp (diagonal v) = diagonal (exp v)`,
where `exp v` is the exponential of the vector `v`. Placeholders: `{m : Type} [Fintype m] [DecidableEq m] (v : m → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (NormedSpace.exp (diagonal v))` | `⊢ P (diagonal (NormedSpace.exp v))` |

**R13 · `rw [Pi.exp_def]`** changes the **goal**: the exponential of a vector is the vector of exponentials.
Statement: `exp x = fun i => exp (x i)`. Placeholders: `{m : Type} [Fintype m] (v : m → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (NormedSpace.exp v)` | `⊢ P fun i => NormedSpace.exp (v i)` |

**R14 · `simp only [← Complex.exp_eq_exp_ℂ]`** changes the **goal**: the scalar `NormedSpace.exp` on `ℂ` becomes
`cexp`. Statement: `Complex.exp_eq_exp_ℂ : cexp = NormedSpace.exp`, used right to left. Use `simp only`, not
`rw`: the occurrence sits under `fun i =>`, where `rw` cannot reach. Placeholders: `{m : Type} (v : m → ℂ)`.

| Before | After |
|---|---|
| `⊢ P fun i => NormedSpace.exp (v i)` | `⊢ P fun i => cexp (v i)` |

---

## Part 4 · `star_gen`

Statement: `((-(t : ℂ) * I) • H)ᴴ = -((-(t : ℂ) * I) • H)` for Hermitian `H`: the generator is anti-Hermitian.
Pull `ᴴ` through the scalar (R15), drop it from `H` (R16), move the outer `-` onto the scalar (R17), compare
scalars (R18), and let `simp` compute the conjugate (R22).

**R15 · `rw [Matrix.conjTranspose_smul]`** changes the **goal**. Statement: `(c • M)ᴴ = star c • Mᴴ`.
Placeholders: `{m : Type} (c : ℂ) (M : Matrix m m ℂ)`.

| Before | After |
|---|---|
| `⊢ P (c • M)ᴴ` | `⊢ P (star c • Mᴴ)` |

**R16 · `rw [hM.eq]`** changes the **goal**. For `hM : M.IsHermitian`, `hM.eq : Mᴴ = M`. Placeholders:
`{m : Type} (M : Matrix m m ℂ) (hM : M.IsHermitian)`.

| Before | After |
|---|---|
| `⊢ P Mᴴ` | `⊢ P M` |

**R17 · `rw [← neg_smul]`** changes the **goal**. Statement: `neg_smul : -c • M = -(c • M)`; right to left it
moves the minus sign onto the scalar. Placeholders: `{m : Type} (c : ℂ) (M : Matrix m m ℂ)`.

| Before | After |
|---|---|
| `⊢ P (-(c • M))` | `⊢ P (-c • M)` |

**R18 · `congr 1`** changes the **goal**: both sides are `_ • M`, so it suffices that the scalars agree. It closes
any part it can by `rfl` or an assumption. Placeholders: `{m : Type} (c d : ℂ) (M : Matrix m m ℂ)`.

| Before | After |
|---|---|
| `⊢ c • M = d • M` | `⊢ c = d` |

**R19 · `rw [Complex.star_def]`** changes the **goal**: `star z` on `ℂ` is the conjugate `(starRingEnd ℂ) z`.
Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star z)` | `⊢ P ((starRingEnd ℂ) z)` |

**R20 · `rw [map_mul]`** changes the **goal**: conjugation is a ring map, so $\overline{zw} = \bar z\,\bar w$.
Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (z * w))` | `⊢ P ((starRingEnd ℂ) z * (starRingEnd ℂ) w)` |

**R21 · `rw [Complex.conj_ofReal, Complex.conj_I]`** changes the **goal**: $\bar r = r$ for real `r`, and
$\bar i = -i$. Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) ↑r * (starRingEnd ℂ) I)` | `⊢ P (↑r * -I)` |

**R22 · `simp`** **closes** a scalar `star` goal built from `↑r`, `I`, `-`, `*`, such as
`star (↑r * I) = -(↑r * I)`. It applies R19–R21 together with `star_neg`, `star_mul'`, `mul_neg`, `neg_neg`.

---

## Part 5 · `time_evolution`

Statement: `NormedSpace.exp ((-(θ / 2 : ℂ) * I) • X) = Rx θ`. Uses milestones `HU`, `diag_conj`, `exp_diag`.
After `rw [diag_conj, Matrix.exp_units_conj, exp_diag]` the left side is `↑HU * diagonal (fun i => cexp (![c, -c] i)) * ↑HU⁻¹`
with `c = -(↑θ / 2) * I`. State the two phases as cos/sin in a `have` **before** any `simp` (Traps), rewrite with
it, then compare entries.

**R23 · `rw [Matrix.exp_units_conj]`** changes the **goal**: the exponential commutes with conjugation by a unit,
$e^{UAU^{-1}} = Ue^AU^{-1}$. Statement: `exp (↑U * A * ↑U⁻¹) = ↑U * exp A * ↑U⁻¹`. Placeholders:
`{m : Type} [Fintype m] [DecidableEq m] (U : (Matrix m m ℂ)ˣ) (A : Matrix m m ℂ)`. In source code write the
coercions with their type, `(U : Matrix m m ℂ)` and `(↑U⁻¹ : Matrix m m ℂ)` (Traps).

| Before | After |
|---|---|
| `⊢ P (NormedSpace.exp (↑U * A * ↑U⁻¹))` | `⊢ P (↑U * NormedSpace.exp A * ↑U⁻¹)` |

**R24 · `funext i`** changes the **goal and the context**: two functions are equal when they agree at every `i`.
Placeholders: `(f g : Fin 2 → ℂ)`.

| Before | After |
|---|---|
| `⊢ f = g` | `i : Fin 2 ⊢ f i = g i` |

**R25 · `simp only [Fin.zero_eta, Matrix.cons_val_zero]`** (index 0) and
**`simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]`** (index 1) change the **goal**: after
`fin_cases`, they turn the printed index into `0` or `1` and read off the entry of `![a, b]`. Placeholders:
`{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (![a, b] ((fun i => i) ⟨0, ⋯⟩))` | `⊢ P a` |
| `⊢ P (![a, b] ((fun i => i) ⟨1, ⋯⟩))` | `⊢ P b` |

**R26 · `rw [Complex.exp_mul_I]`** changes the **goal**: Euler's formula $e^{ix} = \cos x + i \sin x$.
Statement: `cexp (x * I) = cos x + sin x * I`. The argument must have the shape `_ * I` (R28 gets it there).
Placeholders: `(x : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (cexp (x * I))` | `⊢ P (cos x + sin x * I)` |

**R27 · `simp only [Complex.cos_neg, Complex.sin_neg]`** changes the **goal**: `cos` is even, `sin` is odd.
Statements: `cos (-x) = cos x`, `sin (-x) = -sin x`. Placeholders: `(x : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (cos (-x) + sin (-x) * I)` | `⊢ P (cos x + -sin x * I)` |

**R28 · `simp only [neg_mul, neg_neg]`** changes the **goal**: `neg_mul : -a * b = -(a * b)` and
`neg_neg : -(-a) = a` cancel a double sign. Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (-(-a * b))` | `⊢ P (a * b)` |

**R29 · `rw [Complex.ofReal_cos, Complex.ofReal_sin]`** changes the **goal**: the cast of a real cosine is the
complex cosine of the cast, `↑(Real.cos x) = cos ↑x` (same for `sin`). `simp` applies these by itself, which is how
the `Real.cos` entries of `Rx θ` meet the `cos (↑θ / 2)` of the phases. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑(Real.cos x) * ↑(Real.sin x))` | `⊢ P (cos ↑x * sin ↑x)` |

---

## Part 6 · `evolution_unitary`

Statement: `NormedSpace.exp ((-(t : ℂ) * I) • H) ∈ Matrix.unitaryGroup n ℂ` for Hermitian `H`. Uses milestone
`star_gen`. Write `A` for the generator `(-(t : ℂ) * I) • H`. The whole proof is one `rw [...]` chain:
R30, R31, R32, `star_gen H hH t`, R34 (with R33), R35, R36.

**R30 · `rw [Matrix.mem_unitaryGroup_iff]`** changes the **goal**: membership becomes `M * star M = 1`.
Placeholders: `{m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ)`.

| Before | After |
|---|---|
| `⊢ M ∈ unitaryGroup m ℂ` | `⊢ M * star M = 1` |

**R31 · `rw [Matrix.star_eq_conjTranspose]`** changes the **goal**: `star M` of a matrix is `Mᴴ`.
Placeholders: `{m : Type} (M : Matrix m m ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star M)` | `⊢ P Mᴴ` |

**R32 · `rw [← Matrix.exp_conjTranspose]`** changes the **goal**. Statement: `exp Aᴴ = (exp A)ᴴ`; right to left
it moves `ᴴ` inside the exponential. Placeholders: `{m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ)`.

| Before | After |
|---|---|
| `⊢ P (NormedSpace.exp A)ᴴ` | `⊢ P (NormedSpace.exp Aᴴ)` |

**R33 · `(Commute.refl A).neg_right`** changes the **context** (as a `have`) or is passed directly as an argument
to R34. `Commute.refl A : Commute A A`, and `Commute.neg_right : Commute a b → Commute a (-b)`.
Placeholders: `{m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hc : Commute A (-A) ⊢ G` |

**R34 · `rw [← Matrix.exp_add_of_commute _ _ hc]`** changes the **goal**. Statement:
`Commute A B → exp (A + B) = exp A * exp B` (false without `Commute` for matrices). Right to left it merges a
product of exponentials. Placeholders: `{m : Type} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ) (hc : Commute A B)`.

| Before | After |
|---|---|
| `⊢ P (NormedSpace.exp A * NormedSpace.exp B)` | `⊢ P (NormedSpace.exp (A + B))` |

**R35 · `rw [add_neg_cancel]`** changes the **goal**. Statement: `a + -a = 0`. Placeholders: `{m : Type} (A : Matrix m m ℂ)`.

| Before | After |
|---|---|
| `⊢ P (A + -A)` | `⊢ P 0` |

**R36 · `rw [NormedSpace.exp_zero]`** changes the **goal**: $e^0 = 1$. If this is the last step, `rw` closes the
resulting `1 = 1` by `rfl`. Placeholders: `{m : Type} [Fintype m] [DecidableEq m]`.

| Before | After |
|---|---|
| `⊢ P (NormedSpace.exp 0)` | `⊢ P 1` |

---

## Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: conjugation, then a diagonal exponential, on `Fin 3`** (R23, R12, R13, R14). The goal after each `rw`:

```lean-goal
⊢ NormedSpace.exp (↑U * diagonal v * ↑U⁻¹) = (↑U * diagonal fun i => cexp (v i)) * ↑U⁻¹
⊢ ↑U * NormedSpace.exp (diagonal v) * ↑U⁻¹ = (↑U * diagonal fun i => cexp (v i)) * ↑U⁻¹
⊢ ↑U * diagonal (NormedSpace.exp v) * ↑U⁻¹ = (↑U * diagonal fun i => cexp (v i)) * ↑U⁻¹
⊢ (↑U * diagonal fun i => NormedSpace.exp (v i)) * ↑U⁻¹ = (↑U * diagonal fun i => cexp (v i)) * ↑U⁻¹
```

R14 then closes it.

**W2: the phases `e^{+ix}`, `e^{−ix}` as cos/sin** (R24, R3, R25 with R26, R28 reversed, R27, R11). Index 0 is
closed by the first `simp only`. Index 1 needs `← neg_mul` to put `-(x * I)` in the shape `(-x) * I` for R26:

```lean-goal
⊢ cexp (![x * I, -(x * I)] ((fun i => i) ⟨1, ⋯⟩)) = ![cos x + sin x * I, cos x - sin x * I] ((fun i => i) ⟨1, ⋯⟩)
⊢ cos (-x) + sin (-x) * I = cos x - sin x * I
⊢ cos x + -sin x * I = cos x - sin x * I
```

**W3: `exp (-A) * exp A = 1` for any square matrix** (R34 with `(Commute.refl A).neg_left`, `neg_add_cancel`, R36):

```lean-goal
⊢ NormedSpace.exp (-A) * NormedSpace.exp A = 1
⊢ NormedSpace.exp (-A + A) = 1
⊢ NormedSpace.exp 0 = 1
```

**W4: `simp` stops at `v ᵥ* diagonal w`.** `U2` is `!![1, 1; 0, 1]` as a unit with inverse `!![1, -1; 0, 1]`.
After `ext i j; fin_cases i <;> fin_cases j <;> simp [U2, Matrix.mul_apply, Fin.sum_univ_two]`, the entries read

```lean-goal
⊢ (![1, 1] ᵥ* diagonal ![a, b]) 0 = a
⊢ -(![1, 1] ᵥ* diagonal ![a, b]) 0 + (![1, 1] ᵥ* diagonal ![a, b]) 1 = b - a
⊢ (![0, 1] ᵥ* diagonal ![a, b]) 0 = 0
⊢ -(![0, 1] ᵥ* diagonal ![a, b]) 0 + (![0, 1] ᵥ* diagonal ![a, b]) 1 = b
```

`simp [Matrix.vecMul_diagonal]` (R10) evaluates them and leaves `⊢ -a + b = b - a`, which `ring` closes. Better:
put R10 in the first `simp` call.

---

## Traps

- With `open Complex`, a bare `exp` is the scalar `Complex.exp` (`cexp`): `exp A` for a matrix `A` does not
  type-check. Write `NormedSpace.exp`.
- Use `Matrix.exp_add_of_commute` (R34). The generic `NormedSpace.exp_add_of_commute` does not rewrite on
  matrices.
- Write coercions of units with their type: `(U : Matrix m m ℂ) * A * (↑U⁻¹ : Matrix m m ℂ)`. A bare `U * A`
  fails with `failed to synthesize HMul (Matrix m m ℂ)ˣ (Matrix m m ℂ) ?`.
- `Commute.refl _` cannot guess its matrix: write the generator out, `Commute.refl ((-(t : ℂ) * I) • H)`.
- In `time_evolution`, a `simp` straight after `rw [diag_conj, Matrix.exp_units_conj, exp_diag]` reshapes the
  phases (`-(-(↑θ / 2) * I)` and friends) before Euler's formula can fire. Prove the phase vector as a `have` first
  (R24, R3, R25–R28; W2), `rw` with it, and only then compare entries.
- `rw` cannot rewrite under `fun i =>`; use `simp only [...]` (R14).
- `simp` leaves products with `diagonal` as `v ᵥ* diagonal w` (W4): pass `Matrix.vecMul_diagonal` (R10).
- `Matrix.exp_neg` also gives `(exp A)⁻¹ = exp (-A)`, but needs the inverse of a matrix; the `Commute` route
  (R33–R36) avoids it.
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases`, use `<;>` or `all_goals`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| build a unit's proof fields | `⟨a, b, by …, by …⟩` / `refine ⟨a, b, ?_, ?_⟩` | R1 |
| matrix equation → 4 entries | `ext i j; fin_cases i <;> fin_cases j` | R2, R3 |
| entries of products | `simp [names, Matrix.mul_apply, Fin.sum_univ_two]` | R4–R6 |
| numeric goal / ring identity | `norm_num` / `ring` | R7, R11 |
| unfold `↑HU`, `↑HU⁻¹` | `simp [HU]` (`Units.val_mk`, `Units.inv_mk`) | R8, R9 |
| `(v ᵥ* diagonal w) x → v x * w x` | `Matrix.vecMul_diagonal` in the `simp` set | R10 |
| `exp (diagonal v)` → `diagonal (fun i => cexp (v i))` | `rw [Matrix.exp_diagonal, Pi.exp_def]; simp only [← Complex.exp_eq_exp_ℂ]` | R12–R14 |
| `(c • M)ᴴ → star c • Mᴴ` | `rw [Matrix.conjTranspose_smul]` | R15 |
| `Mᴴ → M` for Hermitian `M` | `rw [hM.eq]` | R16 |
| `-(c • M) → -c • M` | `rw [← neg_smul]` | R17 |
| compare the scalars of `c • M = d • M` | `congr 1` | R18 |
| conjugate of a complex expression | `simp` (`Complex.star_def`, `map_mul`, `Complex.conj_ofReal`, `Complex.conj_I`) | R19–R22 |
| `exp (U A U⁻¹) → U exp A U⁻¹` | `rw [Matrix.exp_units_conj]` | R23 |
| equality of vectors pointwise | `funext i; fin_cases i` | R24, R3 |
| entry of `![a, b]` after `fin_cases` | `simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]` | R25 |
| `cexp (x * I) → cos x + sin x * I` | `rw [Complex.exp_mul_I]` | R26 |
| `cos (-x)`, `sin (-x)` | `simp only [Complex.cos_neg, Complex.sin_neg]` | R27 |
| `-(-a * b) → a * b` | `simp only [neg_mul, neg_neg]` | R28 |
| `↑(Real.cos x) → cos ↑x` | `Complex.ofReal_cos`, `Complex.ofReal_sin` (`simp` does it) | R29 |
| unitary → equation with `ᴴ` | `rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]` | R30, R31 |
| `(exp A)ᴴ → exp Aᴴ` | `rw [← Matrix.exp_conjTranspose]` | R32 |
| `exp A * exp (-A) → exp (A + -A)` | `rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl A).neg_right)]` | R33, R34 |
| `A + -A → 0`, `exp 0 → 1` | `rw [add_neg_cancel, NormedSpace.exp_zero]` | R35, R36 |
| see the state | infoview | |
