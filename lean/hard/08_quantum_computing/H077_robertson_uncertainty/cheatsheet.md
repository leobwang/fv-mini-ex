# H077 · Robertson's uncertainty relation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `apply`, `rw`, `simp`, `have`,
`show`, `unfold`, `calc`; `ring` from [`TACTIC_STATES.md`](../../../TACTIC_STATES.md). **New here:** Mathlib's finite-dimensional linear
algebra over `ℂ` (vectors `n → ℂ`, `Matrix n n ℂ`, `⬝ᵥ`, `*ᵥ`, `ᵥ*`, `•`, `ᴴ`, `IsHermitian`), complex
conjugation and real parts, the norm `‖·‖`, `EuclideanSpace` with its inner product, `abel`,
`nlinarith`, and `calc` with `≤` steps.

**The physics, in symbols.** `n` is a finite index set, so states are vectors `ψ : n → ℂ` (a finite-
dimensional Hilbert space ℂⁿ). Write $\langle x, y\rangle = \sum_i \overline{x_i}\, y_i$ (Lean:
`star x ⬝ᵥ y`; conjugate-linear in `x`). A matrix $A$ is *Hermitian* when $A^\dagger = A$, where
$A^\dagger$ (Lean `Aᴴ`) is the conjugate transpose. For a unit vector ($\langle\psi,\psi\rangle = 1$):
$\langle A\rangle = \langle\psi, A\psi\rangle$ (`ev ψ A`), $\mathrm{Var}(A) = \mathrm{Re}(\langle A^2\rangle - \langle A\rangle^2)$
(`var ψ A`). Robertson: $|\langle AB - BA\rangle|^2 \le 4\,\mathrm{Var}(A)\,\mathrm{Var}(B)$, i.e.
$\sigma_A\sigma_B \ge \tfrac12|\langle[A,B]\rangle|$ with $\sigma = \sqrt{\mathrm{Var}}$.
Proof: let $a = \langle A\rangle$, $b = \langle B\rangle$ (both real), $A' = A - a\,I$, $B' = B - b\,I$ (both
Hermitian). Then $[A', B'] = [A, B]$, $\mathrm{Var}(A) = \langle A'\psi, A'\psi\rangle$, and with
$z = \langle A'\psi, B'\psi\rangle$:
$\langle\psi, [A',B']\psi\rangle = z - \bar z = 2i\,\mathrm{Im}\,z$, so
$|z - \bar z|^2 = 4(\mathrm{Im}\,z)^2 \le 4|z|^2 \le 4\langle A'\psi,A'\psi\rangle\langle B'\psi,B'\psi\rangle$
(Cauchy–Schwarz).

The reference solution splits this into the four milestones plus five helper lemmas, named in the
skeletons: F1 `ev_real` ($a$ is real), F2 `shift_herm` ($A'$ is Hermitian), F3 `conj_dot`
($\overline{\langle x,y\rangle} = \langle y,x\rangle$), F4 `comm_ev` ($\langle\psi,[A,B]\psi\rangle = z - \bar z$),
F5 `norm_sub_conj` ($|z-\bar z|^2 \le 4|z|^2$).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop` for the type `α` in question). The step changes only
  the part inside `P (…)`, wherever it sits in a larger goal. `G : Prop` is a goal the step leaves alone.
- `ι` is any finite index type (`{ι : Type} [Fintype ι]`); in the exercise it is `n`. Vectors are
  `v w x y : ι → ℂ`, matrices `M N : Matrix ι ι ℂ`, scalars `c s t : ℂ`, reals `r : ℝ`.
- A bracket such as `[Ring α]` is a requirement on `α` (a *type class*); `ℂ` and `Matrix ι ι ℂ` meet
  every one used here. `[DecidableEq ι]` is needed whenever the identity matrix `1` appears.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `n → ℂ`, `Matrix n n ℂ` | a vector in ℂⁿ; an n×n complex matrix (`n` a finite type, `[Fintype n]`) |
| `v ⬝ᵥ w` | `dotProduct v w = ∑ i, v i * w i`, **no** conjugation (R15) |
| `∑ i, f i` | the sum of `f i` over every `i` of the finite type (`Finset.univ`) |
| `star v` (vector) | entrywise complex conjugate, so `star x ⬝ᵥ y` is ⟨x, y⟩ |
| `M *ᵥ v`, `v ᵥ* M` | matrix times column vector; row vector times matrix |
| `v ⬝ᵥ M *ᵥ w` | `v ⬝ᵥ (M *ᵥ w)`: `*ᵥ` and `ᵥ*` bind tighter than `⬝ᵥ` |
| `v ᵥ* M ⬝ᵥ w` | `(v ᵥ* M) ⬝ᵥ w` |
| `M *ᵥ N *ᵥ v` | `M *ᵥ (N *ᵥ v)` |
| `c • M`, `c • M *ᵥ v` | scalar times matrix; `c • (M *ᵥ v)` |
| `v ⬝ᵥ c • w`, `↑r * v ⬝ᵥ w` | `v ⬝ᵥ (c • w)`; `↑r * (v ⬝ᵥ w)` |
| `1`, `a • 1` (matrices) | the identity matrix; `a·I` |
| `Mᴴ` | conjugate transpose: `Mᴴ i j = conj (M j i)` |
| `P (c • M)ᴴ`, `P (↑r).re` | `P ((c • M)ᴴ)`, `P ((↑r).re)`: postfix `ᴴ` and `.re` bind tightest |
| `M.IsHermitian` | `Mᴴ = M` (R19) |
| `(starRingEnd ℂ) z` | Lean's name for the complex conjugate `conj z`; on `ℂ`, `star z` is the same thing |
| `↑r` | the real number `r : ℝ` cast into `ℂ` |
| `z.re`, `z.im`, `↑z.re` | real and imaginary parts (real numbers); the real part cast back into `ℂ` |
| `‖z‖`, `Complex.normSq z` | the modulus of `z`; its square `re² + im²` (R38, R39) |
| `EuclideanSpace ℂ n` | ℂⁿ with the ℓ² inner product and norm |
| `WithLp.toLp 2 x`, `y.ofLp` | wrap a plain vector into `EuclideanSpace`; unwrap it again |
| `inner ℂ x y` | the inner product ⟨x, y⟩ of `EuclideanSpace` (conjugate-linear in `x`); also printed `⟪x, y⟫_ℂ` |
| `RCLike.re` | the real part on `ℝ` or `ℂ` (`RCLike 𝕜`: 𝕜 is ℝ or ℂ); `simp` turns it into `.re` |
| `ev ψ M`, `var ψ M` | the exercise's ⟨ψ, Mψ⟩ and Re(⟨M²⟩ − ⟨M⟩²) |
| `inst✝ : Fintype n` | an unnamed instance hypothesis; ignore it |

---

## Part 1 · `herm_move` (milestone)

Statement: for Hermitian `A`, `star x ⬝ᵥ (A *ᵥ y) = star (A *ᵥ x) ⬝ᵥ y`, i.e. ⟨x, Ay⟩ = ⟨Ax, y⟩. One
`rw` with R1, R2, R3 makes both sides `star x ᵥ* A ⬝ᵥ y`, and `rw` closes the goal with `rfl`.

**R1 · `rw [Matrix.star_mulVec]`** changes the **goal**. The lemma is
`star (M *ᵥ v) = star v ᵥ* Mᴴ`: conjugating a column `Mv` gives the row `v̄ M†`. Placeholders:
`(M : Matrix ι ι ℂ) (v : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star (M *ᵥ v))` | `⊢ P (star v ᵥ* Mᴴ)` |

**R2 · `rw [hM.eq]`** changes the **goal**. `hM.eq` is `Matrix.IsHermitian.eq hM : Mᴴ = M`.
Placeholders: `(M : Matrix ι ι ℂ) (hM : M.IsHermitian)`.

| Before | After |
|---|---|
| `⊢ P Mᴴ` | `⊢ P M` |

**R3 · `rw [Matrix.dotProduct_mulVec]`** changes the **goal**. The lemma is
`v ⬝ᵥ (M *ᵥ w) = (v ᵥ* M) ⬝ᵥ w` (associativity of row · matrix · column). Placeholders:
`(M : Matrix ι ι ℂ) (v w : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ M *ᵥ w)` | `⊢ P (v ᵥ* M ⬝ᵥ w)` |

---

## Part 2 · `comm_shift` (milestone)

Statement: `(A - a • 1) * (B - b • 1) - (B - b • 1) * (A - a • 1) = A * B - B * A`. Put R4–R11 into one
`simp only [...]`: it expands both products into sums of `A * B`, `a • B`, `b • A`, `(a * b) • 1`. Then
R12 cancels. Placeholders for R4–R5: `{α : Type} [Ring α] (a b c : α)` (`α = Matrix ι ι ℂ` here); for
R6–R10: `(s t : ℂ) (M N : Matrix ι ι ℂ)`.

**R4 · `sub_mul`** changes the **goal**: `(a - b) * c = a * c - b * c`.

| Before | After |
|---|---|
| `⊢ P ((a - b) * c)` | `⊢ P (a * c - b * c)` |

**R5 · `mul_sub`** changes the **goal**: `a * (b - c) = a * b - a * c`.

| Before | After |
|---|---|
| `⊢ P (a * (b - c))` | `⊢ P (a * b - a * c)` |

**R6 · `smul_mul_assoc`** changes the **goal**: `(s • M) * N = s • (M * N)`.

| Before | After |
|---|---|
| `⊢ P (s • M * N)` | `⊢ P (s • (M * N))` |

**R7 · `mul_smul_comm`** changes the **goal**: `M * (s • N) = s • (M * N)`.

| Before | After |
|---|---|
| `⊢ P (M * s • N)` | `⊢ P (s • (M * N))` |

**R8 · `one_mul`, `mul_one`** change the **goal**: `1 * M = M`, `M * 1 = M` (`1` is the identity
matrix). Placeholders: `[DecidableEq ι] (M N : Matrix ι ι ℂ)`, `P` of two arguments.

| Before | After |
|---|---|
| `⊢ P (1 * M) (N * 1)` | `⊢ P M N` |

**R9 · `smul_sub`** changes the **goal**: `s • (M - N) = s • M - s • N`.

| Before | After |
|---|---|
| `⊢ P (s • (M - N))` | `⊢ P (s • M - s • N)` |

**R10 · `smul_smul`** changes the **goal**: `s • t • M = (s * t) • M` (`•` groups to the right).

| Before | After |
|---|---|
| `⊢ P (s • t • M)` | `⊢ P ((s * t) • M)` |

**R11 · `mul_comm t s`** changes the **goal**: `t * s = s * t`, only for these two arguments. In a
`simp only`, a bare `mul_comm` is applied as an ordered rewrite in whatever order `simp` prefers;
`mul_comm b a` says exactly which pair to swap: it turns the `(b * a) • 1` from one product into the
`(a * b) • 1` of the other. Placeholders: `(s t : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (t * s)` | `⊢ P (s * t)` |

**R12 · `abel`** **closes** an equation that holds in every commutative additive group: it treats
`M * N`, `s • N`, … as atoms and cancels `+`/`-`. (`ring` does not apply: matrix `*` is not commutative.)
Placeholders: `(M N K : Matrix ι ι ℂ)`.

| Before | After |
|---|---|
| `⊢ M - (N - K) - (M - N) = K` | no goals |

---

## Part 3 · `var_eq` (milestone)

Statement: for Hermitian `A` and unit `ψ`,
`var ψ A = (star (A' *ᵥ ψ) ⬝ᵥ (A' *ᵥ ψ)).re` with `A' = A - ((ev ψ A).re : ℂ) • 1`. First prove F1
(`((ev ψ A).re : ℂ) = ev ψ A`) with R13–R17 and F2 (`A'.IsHermitian`) with R18–R21; then expand with
R22–R27 and finish with R28–R29.

### F1: the expectation value is real

**R13 · `apply Complex.conj_eq_iff_re.mp`** changes the **goal**. The lemma is
`Complex.conj_eq_iff_re : conj z = z ↔ ↑z.re = z`; `.mp` is its left-to-right direction, so `apply`
leaves the left side as the goal. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ ↑z.re = z` | `⊢ (starRingEnd ℂ) z = z` |

**R14 · `unfold d at h ⊢`** changes the **goal and the context**: the defined name `d` is replaced by its
body in `h` and in the goal (`⊢` names the goal). `unfold ev`, `unfold var`, `unfold ev at h ⊢` in the
exercise. Placeholders: `def cube (z : ℂ) : ℂ := z * z * z`, `(P Q : ℂ → Prop) (hz : P (cube z))`.

| Before | After |
|---|---|
| `hz : P (cube z) ⊢ Q (cube z)` | `hz : P (z * z * z) ⊢ Q (z * z * z)` |

**R15 · `simp only [dotProduct]`** changes the **goal**: `v ⬝ᵥ w` becomes its defining sum
`∑ i, v i * w i`. Placeholders: `(v w : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ w)` | `⊢ P (∑ i, v i * w i)` |

**R16 · `simp`** changes the **goal**: it pushes the conjugate into a sum and a product
(`map_sum`, `map_mul`), and simplifies `conj (conj a) = a` and `star v i = conj (v i)`. Then
`simp [mul_comm]` closes `conj (star x ⬝ᵥ y) = star y ⬝ᵥ x`: so `simp [dotProduct, mul_comm]` proves F3
in one call. Placeholders: `(f g : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (∑ i, f i * g i))` | `⊢ P (∑ x, (starRingEnd ℂ) (f x) * (starRingEnd ℂ) (g x))` |

**R17 · `rw [show a = b by tac]`** changes the **goal**: it rewrites with an equation you state and prove
on the spot, without a separate `have`. In F1: `rw [show starRingEnd ℂ (star ψ ⬝ᵥ (A *ᵥ ψ)) =
star (A *ᵥ ψ) ⬝ᵥ ψ by simp [dotProduct, mul_comm]]`. Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (a * b)` | `⊢ P (b * a)` |

### F2: the shifted matrix is Hermitian

**R18 · `apply hM.sub`** changes the **goal**. `Matrix.IsHermitian.sub :
M.IsHermitian → N.IsHermitian → (M - N).IsHermitian`; with `hM` given, the goal becomes the second
hypothesis. Term form: `hM.sub hN`. Placeholders: `(M N : Matrix ι ι ℂ) (hM : M.IsHermitian)`.

| Before | After |
|---|---|
| `⊢ (M - N).IsHermitian` | `⊢ N.IsHermitian` |

**R19 · `unfold Matrix.IsHermitian`** changes the **goal**: `M.IsHermitian` is by definition `Mᴴ = M`.
(`simp [Matrix.IsHermitian, …]` does the same inside a `simp`.)

| Before | After |
|---|---|
| `⊢ M.IsHermitian` | `⊢ Mᴴ = M` |

**R20 · `rw [Matrix.conjTranspose_smul]`** changes the **goal**. The lemma is `(c • M)ᴴ = star c • Mᴴ`.
Placeholders: `(c : ℂ) (M : Matrix ι ι ℂ)`.

| Before | After |
|---|---|
| `⊢ P (c • M)ᴴ` | `⊢ P (star c • Mᴴ)` |

**R21 · `Matrix.conjTranspose_one`, then `simp`**: `1ᴴ = 1` changes the **goal**; `simp` then **closes** it
with `Complex.conj_ofReal : conj ↑r = ↑r` (the conjugate of a real number is itself; `star` on `ℂ` is
`conj`). Placeholders: `[DecidableEq ι] (r : ℝ)`.

| Before | After `rw [Matrix.conjTranspose_one]` | After `simp` |
|---|---|---|
| `⊢ star ↑r • 1ᴴ = ↑r • 1` | `⊢ star ↑r • 1 = ↑r • 1` | no goals |

### The variance

After `rw [← herm_move _ F2]` the right side is `star ψ ⬝ᵥ A' *ᵥ A' *ᵥ ψ`; R22 merges the two
products. Then `unfold var` and one `simp only` with R4–R8, R23–R27 and `hψ` expand everything into
`ev`-shaped pieces.

**R22 · `rw [Matrix.mulVec_mulVec]`** changes the **goal**. The lemma is `M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v`.
Right to left (`rw [← Matrix.mulVec_mulVec]`) it splits a product, as in F4. Placeholders:
`(M N : Matrix ι ι ℂ) (v : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (M *ᵥ N *ᵥ v)` | `⊢ P ((M * N) *ᵥ v)` |

**R23 · `Matrix.sub_mulVec`** changes the **goal**: `(M - N) *ᵥ v = M *ᵥ v - N *ᵥ v`.

| Before | After |
|---|---|
| `⊢ P ((M - N) *ᵥ v)` | `⊢ P (M *ᵥ v - N *ᵥ v)` |

**R24 · `Matrix.smul_mulVec`** changes the **goal**: `(c • M) *ᵥ v = c • (M *ᵥ v)`, printed
`c • M *ᵥ v`.

| Before | After |
|---|---|
| `⊢ P ((c • M) *ᵥ v)` | `⊢ P (c • M *ᵥ v)` |

**R25 · `Matrix.one_mulVec`** changes the **goal**: `1 *ᵥ v = v`. Needs `[DecidableEq ι]`.

| Before | After |
|---|---|
| `⊢ P (1 *ᵥ v)` | `⊢ P v` |

**R26 · `dotProduct_sub`** changes the **goal**: `u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w`.
Placeholders: `(u v w : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (u ⬝ᵥ (v - w))` | `⊢ P (u ⬝ᵥ v - u ⬝ᵥ w)` |

**R27 · `dotProduct_smul`** changes the **goal**: `v ⬝ᵥ (c • w) = c • (v ⬝ᵥ w)`. With `hψ` in the same
`simp only`, `c • (star ψ ⬝ᵥ ψ)` then becomes `c • 1`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ c • w)` | `⊢ P (c • (v ⬝ᵥ w))` |

**R28 · `Complex.ofReal_re`** changes the **goal**: `(↑r).re = r`. After `rw [← h]` (F1 backwards) the
goal contains `↑(↑(…).re).re`; this lemma removes the double cast. `simp` applies it by itself.
Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑r).re` | `⊢ P r` |

**R29 · `simp [sq]`** **closes** the real-part arithmetic: `sq` turns `a ^ 2` into `a * a`, then
`Complex.sub_re`, `Complex.mul_re`, `Complex.ofReal_re`, `Complex.ofReal_im` (`(↑r).im = 0`) and
`Complex.real_smul` (`↑r • z = ↑r * z`) reduce both sides to the same real expression.
Placeholders: `(r : ℝ) (z : ℂ)`.

| Before | After |
|---|---|
| `⊢ (z - ↑r ^ 2).re = (z - ↑r • ↑r).re` | no goals |

---

## Part 4 · `cauchy_schwarz` (milestone)

Statement: `‖star x ⬝ᵥ y‖ ^ 2 ≤ (star x ⬝ᵥ x).re * (star y ⬝ᵥ y).re`. Mathlib's Cauchy–Schwarz lives in
inner-product spaces; a plain `n → ℂ` is not one (its default norm is the sup norm). Wrap the vectors with
`WithLp.toLp 2` to land in `EuclideanSpace ℂ n`, use Cauchy–Schwarz there (R30), translate the inner
product and the norms back to `⬝ᵥ` (R31–R34), and square (R35–R37).

**R30 · `have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x : EuclideanSpace ℂ ι) (WithLp.toLp 2 y)`**
changes the **context**. The lemma is `‖inner 𝕜 x y‖ ≤ ‖x‖ * ‖y‖` in any inner-product space over
`𝕜 ∈ {ℝ, ℂ}`; `(𝕜 := ℂ)` names the field, and the type ascription says which space. Placeholders:
`(x y : ι → ℂ) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h : ‖inner ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 y)‖ ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ ⊢ G` |

**R31 · `rw [EuclideanSpace.inner_eq_star_dotProduct]`** changes the **goal** (or `h` with `at h`). The
lemma is `inner 𝕜 x y = y.ofLp ⬝ᵥ star x.ofLp`: note the order, `y` first. Placeholders:
`(x y : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (inner ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 y))` | `⊢ P ((WithLp.toLp 2 y).ofLp ⬝ᵥ star (WithLp.toLp 2 x).ofLp)` |

**R32 · `simp only at h`** (or plain `simp`) changes the **hypothesis** `h`: `(WithLp.toLp 2 x).ofLp`
(wrap, then unwrap) is `x` by definition, and `simp` removes it.

| Before | After |
|---|---|
| `h : P ((WithLp.toLp 2 y).ofLp ⬝ᵥ star (WithLp.toLp 2 x).ofLp) ⊢ P (y ⬝ᵥ star x)` | `h : P (y ⬝ᵥ star x) ⊢ P (y ⬝ᵥ star x)` |

**R33 · `dotProduct_comm`** changes the **goal**: `v ⬝ᵥ w = w ⬝ᵥ v`, turning `y ⬝ᵥ star x` into
`star x ⬝ᵥ y`. In `simp [dotProduct_comm]`, `simp` uses it as an ordered rewrite (no loop): it puts
both sides in the same order, which closes a goal whose sides differ by this swap. To change one
term in a given direction, use `rw`. Placeholders: `(v w : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ w)` | `⊢ P (w ⬝ᵥ v)` |

**R34 · `rw [@norm_sq_eq_re_inner ℂ]`** changes the **goal**. The lemma is `‖x‖ ^ 2 = RCLike.re (inner 𝕜 x x)`;
`@… ℂ` fixes `𝕜 = ℂ`, which `rw` cannot infer on its own (it reports *typeclass instance problem is
stuck*). Placeholders: `(x : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (‖WithLp.toLp 2 x‖ ^ 2)` | `⊢ P (RCLike.re (inner ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 x)))` |

**R35 · `calc`** changes the **goal list**: `calc a ≤ b := p₁` / `_ = c := p₂` proves `a ≤ c` from one proof
per step (`_` is the previous right side; `≤` and `=` steps mix). The first left side and the last
right side may be written `_` when they match the goal. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `h₁ : a ≤ b, h₂ : b = c ⊢ a ≤ c` | one goal per step, here closed by `h₁`, `h₂` |

**R36 · `pow_le_pow_left₀ ha hab n`** changes the **context** (as a `have`) or closes a `calc` step:
`0 ≤ a → a ≤ b → a ^ n ≤ b ^ n`. `norm_nonneg x : 0 ≤ ‖x‖` supplies `ha` when `a` is a norm.
Placeholders: `(z : ℂ) (b : ℝ) (hab : ‖z‖ ≤ b)`.

| Before | After |
|---|---|
| `⊢ ‖z‖ ^ 2 ≤ b ^ 2` | `h : ‖z‖ ^ 2 ≤ b ^ 2 ⊢ ‖z‖ ^ 2 ≤ b ^ 2` |

**R37 · `mul_pow`** changes the **goal**: `(a * b) ^ n = a ^ n * b ^ n`. Placeholders: `(a b : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((a * b) ^ n)` | `⊢ P (a ^ n * b ^ n)` |

---

## Part 5 · `robertson` (spec)

Statement: `‖ev ψ (A * B - B * A)‖ ^ 2 ≤ 4 * var ψ A * var ψ B`. Prove F3, F4, F5 first (skeleton). F4
uses only earlier entries (R14, R23, R26, R22 right to left, `herm_move`, F3). F5 uses R38–R41. The main
proof is one `rw [← comm_shift …, F4 …, var_eq …, var_eq …]` and a two-step `calc` (R35): F5, then
milestone 4 plus R41 (`nlinarith` multiplies the Cauchy–Schwarz bound by 4).

**R38 · `rw [Complex.sq_norm]`** changes the **goal**: `‖z‖ ^ 2 = Complex.normSq z`. Placeholders:
`(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (‖z‖ ^ 2)` | `⊢ P (Complex.normSq z)` |

**R39 · `rw [Complex.normSq_apply]`** changes the **goal**: `normSq z = z.re * z.re + z.im * z.im`.

| Before | After |
|---|---|
| `⊢ P (Complex.normSq z)` | `⊢ P (z.re * z.re + z.im * z.im)` |

**R40 · `simp`** changes the **goal**: real and imaginary parts of `z - conj z`, by `Complex.sub_re`,
`Complex.sub_im`, `Complex.conj_re : (conj z).re = z.re`, `Complex.conj_im : (conj z).im = -z.im`.
So `z - conj z = 2i·Im z`. Placeholders: `(z : ℂ) (P : ℝ → ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (z - (starRingEnd ℂ) z).re (z - (starRingEnd ℂ) z).im` | `⊢ P 0 (z.im + z.im)` |

**R41 · `nlinarith [t₁, …]`** **closes** a polynomial inequality over `ℝ`. It multiplies pairs of
hypotheses and hint terms `tᵢ` and then does linear arithmetic. `sq_nonneg a : 0 ≤ a ^ 2` is the usual
hint (here `a = z.re`: `4(re² + im²) − (2 im)² = 4 re² ≥ 0`). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ (b + b) * (b + b) ≤ 4 * (a * a + b * b)` | no goals |

---

## Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: a single shift drops out of a commutator.** R4–R8 in one `simp only`, then R12:

```lean-goal
⊢ (M - s • 1) * N - N * (M - s • 1) = M * N - N * M
⊢ M * N - s • N - (N * M - s • N) = M * N - N * M
```

**W2: the real-part twin of F5,** `‖z + conj z‖² ≤ 4‖z‖²`: R38 and R39 twice in one `rw`, `simp` (R40),
then `nlinarith [sq_nonneg z.im]` (R41):

```lean-goal
⊢ ‖z + (starRingEnd ℂ) z‖ ^ 2 ≤ 4 * ‖z‖ ^ 2
⊢ (z.re + z.re) * (z.re + z.re) ≤ 4 * (z.re * z.re + z.im * z.im)
```

**W3: square a bound, then split the square of a product** (the end of milestone 4): `calc` (R35) with
`pow_le_pow_left₀ ha h 2` (R36) and `rw [mul_pow]` (R37):

```lean-goal
⊢ a ^ 2 ≤ b ^ 2 * c ^ 2
```

**W4: a real multiple of the identity is Hermitian** (the scalar half of F2): R19, R20, then `simp`
(R21):

```lean-goal
⊢ (↑r • 1).IsHermitian
⊢ (↑r • 1)ᴴ = ↑r • 1
⊢ star ↑r • 1ᴴ = ↑r • 1
```

---

## Traps

- `comm_shift` takes `a b : ℂ`. Give it the **real** numbers `(ev ψ A).re`, `(ev ψ B).re`; Lean casts them
  to `↑(ev ψ A).re`, which is exactly the shift in `var_eq`. With `ev ψ A` itself the shifted matrices
  differ from `var_eq`'s and the later `rw [var_eq …]` fails.
- `rw [← comm_shift …]` rewrites the commutator **into** the shifted one: the arrow matters.
- Precedence: `star x ⬝ᵥ A *ᵥ y` is `star x ⬝ᵥ (A *ᵥ y)`; `c • M *ᵥ v` is `c • (M *ᵥ v)`. Read the
  infoview with the table above before writing a `show` or `have`.
- `EuclideanSpace.inner_eq_star_dotProduct` gives `y ⬝ᵥ star x`, not `star x ⬝ᵥ y`: finish with
  `dotProduct_comm` (R33).
- `rw [norm_sq_eq_re_inner]` fails with *typeclass instance problem is stuck*: write
  `@norm_sq_eq_re_inner ℂ` (R34).
- `rw [← h]` with `h : ↑(ev ψ A).re = ev ψ A` replaces **every** `ev ψ A`, including the one inside
  `↑(ev ψ A).re`, which leaves `↑(↑(…).re).re`. That is harmless: `simp` removes it (R28).
- `conj` is notation only after `open ComplexConjugate`, which `problem.lean` does not have: writing
  `conj z` in a lemma statement gives *Function expected*. Write `starRingEnd ℂ z` (the infoview prints
  `(starRingEnd ℂ) z`).
- `ring` does not close matrix identities (matrix `*` does not commute); use `abel` after expanding (R12).
- The helper facts F1–F5 are not in `problem.lean`: add them as your own lemmas above the theorem that
  uses them. F2 is needed both in `var_eq` and in `robertson`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| move a Hermitian `A` across `⬝ᵥ` | `rw [Matrix.star_mulVec, hA.eq, Matrix.dotProduct_mulVec]` | R1–R3 |
| expand `(A - a • 1) * (B - b • 1)` | `simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub, smul_smul, mul_comm b a]` | R4–R11 |
| cancel matrix sums | `abel` | R12 |
| `↑z.re = z` from `conj z = z` | `apply Complex.conj_eq_iff_re.mp` | R13 |
| unfold a definition in `h` and the goal | unfold ev at h ⊢ | R14 |
| `conj (star x ⬝ᵥ y) = star y ⬝ᵥ x` | `simp [dotProduct, mul_comm]` | R15, R16 |
| rewrite with an ad-hoc equation | `rw [show a = b by tac]` | R17 |
| `(A - B).IsHermitian` | `hA.sub hB` | R18 |
| `(↑r • 1).IsHermitian` | `simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]` | R19–R21 |
| `M *ᵥ (N *ᵥ v)` ↔ `(M * N) *ᵥ v` | `rw [Matrix.mulVec_mulVec]` / `rw [← Matrix.mulVec_mulVec]` | R22 |
| split `*ᵥ` and `⬝ᵥ` | `Matrix.sub_mulVec`, `Matrix.smul_mulVec`, `Matrix.one_mulVec`, `dotProduct_sub`, `dotProduct_smul` | R23–R27 |
| real parts of casts | `simp [sq]` (`Complex.ofReal_re`, …) | R28, R29 |
| Cauchy–Schwarz for `n → ℂ` | `norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x : EuclideanSpace ℂ n) (WithLp.toLp 2 y)` | R30 |
| `inner` → `⬝ᵥ` | `rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct_comm]` | R31–R33 |
| `‖x‖ ^ 2` → real part of `inner` | `rw [@norm_sq_eq_re_inner ℂ]` | R34 |
| chain `≤` and `=` | `calc _ ≤ b := p₁` / `_ = _ := p₂` | R35 |
| square an inequality | `pow_le_pow_left₀ (norm_nonneg _) h 2` | R36 |
| `(a * b) ^ n` | `rw [mul_pow]` | R37 |
| `‖z‖ ^ 2` → `re² + im²` | `rw [Complex.sq_norm, Complex.normSq_apply]` | R38, R39 |
| re/im of `z - conj z` | `simp` | R40 |
| polynomial inequality | `nlinarith [sq_nonneg z.re]` | R41 |
| see the state | infoview | |
