# H081 · Tsirelson's bound: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's matrices over `ℂ` acting on
vectors (`*ᵥ`, `ᵥ*`, `⬝ᵥ`, `ᴴ`), Hermitian matrices, the inner-product space `EuclideanSpace ℂ n`
and its Cauchy–Schwarz inequality, real parts and absolute values, and the tactics `nlinarith`,
`linarith`, `abel`, `set`, `calc`.

**The math.** Write $\langle x, y\rangle = \sum_i \overline{x_i}\, y_i$ (Lean: `star x ⬝ᵥ y`) and
$\langle M\rangle = \langle\psi, M\psi\rangle$ for a unit vector $\psi$ ($\langle\psi,\psi\rangle = 1$).
Let $C = A_0B_0 + A_0B_1 + A_1B_0 - A_1B_1$ (the CHSH operator), with $A_i, B_j$ Hermitian
($M^\dagger = M$, Lean `Mᴴ = M`), $A_i^2 = B_j^2 = 1$ and $A_iB_j = B_jA_i$. Then

1. Cauchy–Schwarz: $|\langle x, y\rangle|^2 \le \langle x,x\rangle\,\langle y,y\rangle$ (milestone `cauchy_schwarz`).
2. If $W^\dagger W = 1$ then $|\langle W\rangle| \le 1$ (milestone `unitary_expect`).
3. $C^2 = 4 - [A_0, A_1][B_0, B_1]$, where $[X, Y] = XY - YX$ (milestone `chsh_sq_matrix`).
4. For Hermitian $C$: $(\operatorname{Re}\langle C\rangle)^2 \le \operatorname{Re}\langle C^2\rangle$ (milestone `expect_sq_le`).
5. $[A_0,A_1][B_0,B_1]$ expands into four products such as $A_0A_1B_0B_1$, each a product of
   Hermitian involutions, hence unitary, so by 2 each expectation has modulus $\le 1$. So
   $\operatorname{Re}\langle C^2\rangle \le 4 + 4 = 8$, and by 4, $\operatorname{Re}\langle C\rangle \le \sqrt 8 = 2\sqrt 2$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves alone.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Ring R]`
  is a requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. Cells
  containing the absolute value `|…|` are written outside code (Markdown tables cannot hold a bare `|`)
  and repeated in a `lean-goal` block below the table.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix n n ℂ` | `n × n` complex matrices, rows and columns indexed by a finite type `n` (`[Fintype n]`) |
| `n → ℂ` | a vector with one complex entry per index |
| `[Fintype n]`, `[DecidableEq n]` | `n` is finite (sums over it make sense) and has decidable `=` (needed for the identity matrix `1`) |
| `M *ᵥ v` | matrix times column vector, $(Mv)_i = \sum_j M_{ij} v_j$ |
| `v ᵥ* M` | row vector times matrix, $(v^{\mathsf T}M)_j = \sum_i v_i M_{ij}$ |
| `v ⬝ᵥ w` | $\sum_i v_i w_i$, no conjugation |
| `star v` | entrywise complex conjugate of `v` (of a matrix: the conjugate transpose) |
| `star x ⬝ᵥ y` | the inner product $\langle x, y\rangle = \sum_i \overline{x_i} y_i$ |
| `star ψ ⬝ᵥ M *ᵥ ψ` | $\langle\psi, M\psi\rangle$: `⬝ᵥ` binds weaker than `*ᵥ`, `ᵥ*`, `•`, so this is `star ψ ⬝ᵥ (M *ᵥ ψ)` |
| `M *ᵥ N *ᵥ v` | `M *ᵥ (N *ᵥ v)` (`*ᵥ` groups to the right) |
| `v ᵥ* M ᵥ* N` | `(v ᵥ* M) ᵥ* N` (`ᵥ*` groups to the left) |
| `4 * star ψ ⬝ᵥ ψ` | `4 * (star ψ ⬝ᵥ ψ)`: `*` binds weaker than `⬝ᵥ` |
| `Mᴴ` | conjugate transpose $M^\dagger$ |
| `M.IsHermitian` | `Mᴴ = M` (a definition; unfold with R31, use with R26) |
| `c • v`, `c • M` | scalar `c` times every entry of the vector `v` or matrix `M` |
| `1`, `4` as matrices | the identity and `4 • 1` (four times the identity) |
| `EuclideanSpace ℂ n` | `n → ℂ` with the ℓ² inner product and norm (an `InnerProductSpace ℂ`) |
| `WithLp.toLp 2 x`, `u.ofLp` | `x : n → ℂ` seen in `EuclideanSpace ℂ n`, and back (R1, R4) |
| `inner ℂ u v` | the inner product $\langle u, v\rangle$, conjugate-linear in `u` |
| `‖z‖` | modulus of `z : ℂ`; norm of a vector `u` |
| `z.re`, `Complex.re z` | real part of `z : ℂ` (`Complex.re 1` is `(1 : ℂ).re`) |
| `RCLike.re z` | real part, stated for `ℝ` and `ℂ` at once; on `ℂ` it is `z.re`, so `RCLike.re z = z.re` closes by `rfl` (W2) |
| `𝕜`, `(𝕜 := ℂ)` | Mathlib's name for the scalar field (`ℝ` or `ℂ`) of a lemma; `(𝕜 := ℂ)` sets it by name (R2, R6) |
| `\|a\|` | absolute value of `a : ℝ` |
| `√x` | `Real.sqrt x` |
| `C : Matrix n n ℂ := e` | a local definition made by `set` (R30): `C` stands for `e` |
| `case ha`, `case hab` | names of side goals produced by `apply` |

---

## Part 1 · `cauchy_schwarz`

Statement: `‖star x ⬝ᵥ y‖ ^ 2 ≤ (star x ⬝ᵥ x).re * (star y ⬝ᵥ y).re`, i.e.
$|\langle x, y\rangle|^2 \le \langle x,x\rangle\langle y,y\rangle$ for `x y : n → ℂ`. Mathlib proves
Cauchy–Schwarz in any inner-product space; the work is translating between `EuclideanSpace` and `⬝ᵥ`.

**R1 · `WithLp.toLp 2 x`** is a **term**, not a tactic: the function `x : n → ℂ` as an element of
`EuclideanSpace ℂ n`, where `inner` and `‖·‖` are the ℓ² ones. Write the type once,
`(WithLp.toLp 2 x : EuclideanSpace ℂ n)`, so Lean picks the right space. Placeholders:
`{n : Type} [Fintype n] (x : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (WithLp.toLp 2 x)` | closed by `exact h (WithLp.toLp 2 x)` |

**R2 · `have h := norm_inner_le_norm (𝕜 := ℂ) u v`** changes the **context**. The lemma is
`‖inner 𝕜 u v‖ ≤ ‖u‖ * ‖v‖`, for any scalar field `𝕜` (`ℝ` or `ℂ`). `(𝕜 := ℂ)` is a *named argument*: it
sets the lemma's implicit argument `𝕜` to `ℂ`, which Lean cannot infer from `u v`. Placeholders: `{E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (u v : E)`;
`EuclideanSpace ℂ n` meets both brackets.

| Before | After |
|---|---|
| `⊢ G` | `h : ‖inner ℂ u v‖ ≤ ‖u‖ * ‖v‖ ⊢ G` |

**R3 · `rw [EuclideanSpace.inner_eq_star_dotProduct]`** changes the **goal**. The lemma is
`inner 𝕜 x y = y.ofLp ⬝ᵥ star x.ofLp`: the conjugated vector ends up on the right. Placeholders:
`{n : Type} [Fintype n] (x y : EuclideanSpace ℂ n)`.

| Before | After |
|---|---|
| `⊢ P (inner ℂ x y)` | `⊢ P (y.ofLp ⬝ᵥ star x.ofLp)` |

**R4 · `rw [WithLp.ofLp_toLp]`** changes the **goal**: `(WithLp.toLp p x).ofLp = x`. `simp` applies it by
itself. Placeholders: `{n : Type} (x : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (WithLp.toLp 2 x).ofLp` | `⊢ P x` |

**R5 · `rw [dotProduct_comm]`** changes the **goal**: `v ⬝ᵥ w = w ⬝ᵥ v` (entries commute in `ℂ`).
Placeholders: `{n : Type} [Fintype n] (v w : n → ℂ)`. `simp [dotProduct_comm]` uses it to match both sides.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ w)` | `⊢ P (w ⬝ᵥ v)` |

**R6 · `rw [norm_sq_eq_re_inner (𝕜 := ℂ)]`** changes the **goal**. The lemma is
`‖u‖ ^ 2 = RCLike.re (inner 𝕜 u u)`. Placeholders as in R2, `(u : E)`. Without `(𝕜 := ℂ)` (equivalently
`@norm_sq_eq_re_inner ℂ`) `rw` fails: `𝕜` does not occur in `‖u‖ ^ 2`, so Lean cannot infer it.

| Before | After |
|---|---|
| `⊢ P (‖u‖ ^ 2)` | `⊢ P (RCLike.re (inner ℂ u u))` |

**R7 · `rw [e] at h`** changes the **context**: it rewrites hypothesis `h` instead of the goal.
Placeholders: `{α : Type} (a b : α) (e : a = b)`.

| Before | After |
|---|---|
| `h : P a ⊢ G` | `h : P b ⊢ G` |

**R8 · `calc`** changes the **goal list**: the goal `a ≤ c` becomes a chain of steps, each proved after
its `:=`. Steps may mix `≤` and `=`; `_` stands for the previous right-hand side, and a final `_ = _`
lets Lean fill in the goal's right side. Placeholders: `{α : Type} [Preorder α] (a b c : α)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | steps `a ≤ b := h₁` and `_ = c := h₂`; no goal left |

**R9 · `apply pow_le_pow_left₀`** changes the **goal list**. The lemma is
`0 ≤ a → a ≤ b → ∀ m, a ^ m ≤ b ^ m` (on `ℝ`). As a term: `pow_le_pow_left₀ ha hab m`.
Placeholders: `(a b : ℝ) (m : ℕ)`.

| Before | After |
|---|---|
| `⊢ a ^ m ≤ b ^ m` | `⊢ 0 ≤ a`, `⊢ a ≤ b` |

**R10 · `norm_nonneg u`** **closes** `0 ≤ ‖u‖`. Placeholders: `{E : Type} [NormedAddCommGroup E] (u : E)`
(also `u : ℂ`). It is the side goal of R9 and a hint for `nlinarith` (R17).

| Before | After |
|---|---|
| `⊢ 0 ≤ ‖u‖` | closed |

**R11 · `rw [mul_pow]`** changes the **goal**: `(a * b) ^ m = a ^ m * b ^ m`. Placeholders:
`{α : Type} [CommMonoid α] (a b : α) (m : ℕ)`; `ℝ` qualifies.

| Before | After |
|---|---|
| `⊢ P ((a * b) ^ m)` | `⊢ P (a ^ m * b ^ m)` |

**W1, W2: the two translations** (on `Fin 3` vectors, not the exercise's statement). R3, R4 (once per
vector), R5:

```lean-goal
⊢ inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 w) = star v ⬝ᵥ w
⊢ (WithLp.toLp 2 w).ofLp ⬝ᵥ star (WithLp.toLp 2 v).ofLp = star v ⬝ᵥ w
⊢ w ⬝ᵥ star v = star v ⬝ᵥ w
```

R6, R3, R4 for a norm; the last goal closes by `rfl`:

```lean-goal
⊢ ‖WithLp.toLp 2 v‖ ^ 2 = (v ⬝ᵥ star v).re
⊢ RCLike.re (inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 v)) = (v ⬝ᵥ star v).re
⊢ RCLike.re ((WithLp.toLp 2 v).ofLp ⬝ᵥ star (WithLp.toLp 2 v).ofLp) = (v ⬝ᵥ star v).re
⊢ RCLike.re (v ⬝ᵥ star v) = (v ⬝ᵥ star v).re
```

---

## Part 2 · `unitary_expect`

Statement: if `Wᴴ * W = 1` and `star ψ ⬝ᵥ ψ = 1` then `‖star ψ ⬝ᵥ (W *ᵥ ψ)‖ ≤ 1`. Use Part 1 with
`y = W *ᵥ ψ`; then $\langle W\psi, W\psi\rangle = \langle\psi, W^\dagger W\psi\rangle = 1$.

**R12 · `rw [Matrix.star_mulVec]`** changes the **goal**: `star (M *ᵥ v) = star v ᵥ* Mᴴ`
($\overline{Mv} = \bar v^{\mathsf T} M^\dagger$ as a row vector). Placeholders:
`{n : Type} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star (M *ᵥ v))` | `⊢ P (star v ᵥ* Mᴴ)` |

**R13 · `rw [Matrix.dotProduct_mulVec]`** changes the **goal**: `v ⬝ᵥ A *ᵥ w = v ᵥ* A ⬝ᵥ w`, i.e.
$v \cdot (Aw) = (v^{\mathsf T}A)\cdot w$. Right to left (`← dotProduct_mulVec`) moves a matrix from the
row side to the column side. Placeholders: `{n : Type} [Fintype n] (v w : n → ℂ) (A : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ A *ᵥ w)` | `⊢ P (v ᵥ* A ⬝ᵥ w)` |

**R14 · `rw [Matrix.vecMul_vecMul]`** changes the **goal**: `v ᵥ* M ᵥ* N = v ᵥ* (M * N)`.
Placeholders: `(v : n → ℂ) (M N : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P (v ᵥ* M ᵥ* N)` | `⊢ P (v ᵥ* (M * N))` |

**R15 · `rw [Matrix.vecMul_one]`** changes the **goal**: `v ᵥ* 1 = v`. Placeholders:
`{n : Type} [Fintype n] [DecidableEq n] (v : n → ℂ)` (`DecidableEq n` is needed to define the identity matrix).

| Before | After |
|---|---|
| `⊢ P (v ᵥ* 1)` | `⊢ P v` |

**R16 · `rw [Complex.one_re]`, then `rw [one_mul]`** change the **goal**: `Complex.re 1 = 1`, then
`1 * r = r`. After `rw [hψ]` a hypothesis contains `(1 : ℂ).re`. Placeholders: `(r : ℝ)`.

| Before | After `rw [Complex.one_re]` | After `rw [one_mul]` |
|---|---|---|
| `⊢ P (Complex.re 1 * r)` | `⊢ P (1 * r)` | `⊢ P r` |

**R17 · `nlinarith [t₁, …]`** **closes** a goal that is a polynomial (in)equality over `ℝ` following from
the hypotheses and the extra terms `tᵢ` (it also multiplies pairs of them). Give it the sign facts it needs,
such as `norm_nonneg z` (R10). Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `h : a ^ 2 ≤ 1, ha : 0 ≤ a ⊢ a ≤ 1` | closed by `nlinarith [ha]` |

**W3: `⟨Uv, Uw⟩ = ⟨v, w⟩` for `Uᴴ * U = 1`** (two vectors `v`, `w`). R12, R13, R14, `rw [hU]`, R15:

```lean-goal
⊢ star (U *ᵥ v) ⬝ᵥ U *ᵥ w = star v ⬝ᵥ w
⊢ star v ᵥ* Uᴴ ⬝ᵥ U *ᵥ w = star v ⬝ᵥ w
⊢ star v ᵥ* Uᴴ ᵥ* U ⬝ᵥ w = star v ⬝ᵥ w
⊢ star v ᵥ* (Uᴴ * U) ⬝ᵥ w = star v ⬝ᵥ w
⊢ star v ᵥ* 1 ⬝ᵥ w = star v ⬝ᵥ w
```

---

## Part 3 · `chsh_sq_matrix`

Statement: under $A_i^2 = B_j^2 = 1$ and $A_iB_j = B_jA_i$,
`C * C = 4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)` for the CHSH operator `C` written out.
Matrices do not commute, so `ring` is useless; `simp only` with the right rules brings both sides to the
same sum of products, and `abel` matches them.

**R18 · a `∀`-helper `have sw : ∀ {a b : R}, … := by intro a b h x; …`** changes the **context**: it
adds a lemma you can instantiate. With implicit `{a b}`, `sw c₀₀` reads `a b` off `c₀₀ : A₀ * B₀ = B₀ * A₀`
and is `∀ x, B₀ * (A₀ * x) = A₀ * (B₀ * x)`. Its proof: `intro a b h x`, then R19, `rw [← h]`,
`rw [mul_assoc]`. Placeholders: `{R : Type} [Ring R]`; `Matrix n n ℂ` (with `[Fintype n] [DecidableEq n]`)
is a ring.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, plus `sw : ∀ {a b : R}, a * b = b * a → ∀ (x : R), b * (a * x) = a * (b * x)` in the context |

**R19 · `rw [← mul_assoc]`** changes the **goal**. `mul_assoc : a * b * c = a * (b * c)`; `*` groups to
the left, so `a * b * c` is `(a * b) * c`. Plain `rw [← mul_assoc]` regroups the first `x * (y * z)` it
finds; `rw [← mul_assoc b]` fixes the first factor, so only a product `b * (_ * _)` is regrouped (Part 5's
helper `um` needs this to bring `Pᴴ * P` together). Placeholders: `{R : Type} [Ring R] (a b c : R)`.

| Before | After |
|---|---|
| `⊢ P (a * (b * c))` | `⊢ P (a * b * c)` |

**R20 · `simp only [add_mul, mul_add, sub_mul, mul_sub]`** changes the **goal**: every product of sums and
differences is distributed. Placeholders: `{R : Type} [Ring R] (a b c d : R)`. `simp only` complains about
a listed lemma it never uses, so list only those that fire.

| Before | After |
|---|---|
| `⊢ P ((a + b) * (c - d) - (a - b) * (c + d))` | `⊢ P (a * c + b * c - (a * d + b * d) - (a * c - b * c + (a * d - b * d)))` |

**R21 · `simp only [mul_assoc]`** changes the **goal**: every product is re-associated to the right, so
each term becomes `x₁ * (x₂ * (x₃ * x₄))` and the helpers of R22 can see `b * (a * x)`.

| Before | After |
|---|---|
| `⊢ P (a * b * c * d)` | `⊢ P (a * (b * (c * d)))` |

**R22 · `simp only [sw hab, sq1 ha]`** changes the **goal**: rewriting with instantiated helpers.
`sw hab : ∀ x, b * (a * x) = a * (b * x)` moves `a` left past `b`; `sq1 ha : ∀ x, a * (a * x) = x`
(proved like `sw`, with `rw [← mul_assoc, h, one_mul]`) cancels a square in front of any tail. A square
at the very end, `… * (b * b)`, is matched by `hb : b * b = 1` itself. Put R20, R21, R22 in one
`simp only [...]` and `simp` interleaves them. Placeholders: `{R : Type} [Ring R] (a b c : R)`.

| Before | After |
|---|---|
| `⊢ P (a * (b * (a * c)))` | `⊢ P (b * c)` |

**R23 · `simp only [mul_one]`** changes the **goal**: `a * 1 = a`. Rewriting `b * b` to `1` at the end of a
product leaves such `* 1`.

| Before | After |
|---|---|
| `⊢ P (a * (b * 1))` | `⊢ P (a * b)` |

**R24 · `rw [show (4 : R) = 1 + 1 + 1 + 1 by norm_num]`** changes the **goal**. `show T by tac` is a proof of
`T` that `rw` uses like a lemma. Here it splits the numeral so `abel` can cancel the four `1`s. For matrices
write `(4 : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P 4` | `⊢ P (1 + 1 + 1 + 1)` |

**R25 · `abel`** **closes** an equation that holds in every additive commutative group: it reorders and
cancels `+`, `-` and treats each product such as `a * (b * c)` as an opaque atom. It does not know that
`4 = 1 + 1 + 1 + 1` (R24) or anything about `*`.

| Before | After |
|---|---|
| `⊢ 1 + x - y + (1 + y) = 1 + 1 + x` | closed |

**W4: the same pattern on `(ab + ba)(ab − ba) = 0`**, `a² = b² = 1`, `ab = ba`. After R18 (`sw`, `sq1`):
R20 (here only `add_mul`, `mul_sub` fire), R21, R22 (with `sa`, `sb`), R25:

```lean-goal
⊢ (a * b + b * a) * (a * b - b * a) = 0
⊢ a * b * (a * b) + b * a * (a * b) - (a * b * (b * a) + b * a * (b * a)) = 0
⊢ a * (b * (a * b)) + b * (a * (a * b)) - (a * (b * (b * a)) + b * (a * (b * a))) = 0
⊢ 1 + 1 - (1 + 1) = 0
```

---

## Part 4 · `expect_sq_le`

Statement: for Hermitian `C` and unit `ψ`, `(star ψ ⬝ᵥ (C *ᵥ ψ)).re ^ 2 ≤ (star ψ ⬝ᵥ ((C * C) *ᵥ ψ)).re`.
Part 1 with `x = ψ`, `y = C *ᵥ ψ` gives $|\langle C\rangle|^2 \le \langle C\psi, C\psi\rangle =
\langle C^2\rangle$; then $(\operatorname{Re} z)^2 \le |z|^2$.

**R26 · `rw [hA.eq]`** changes the **goal**. `Matrix.IsHermitian.eq : A.IsHermitian → Aᴴ = A`; with
`hA : A.IsHermitian`, `hA.eq` is the equation `Aᴴ = A`. Placeholders: `{n : Type} (A : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P Aᴴ` | `⊢ P A` |

**R27 · `rw [Matrix.mulVec_mulVec]`** changes the **goal**: `M *ᵥ N *ᵥ v = (M * N) *ᵥ v`.
Placeholders: `(M N : Matrix n n ℂ) (v : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (M *ᵥ N *ᵥ v)` | `⊢ P ((M * N) *ᵥ v)` |

**R28 · `have hre := Complex.abs_re_le_norm z`** changes the **context**: $|\operatorname{Re} z| \le |z|$.
Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, plus `hre : \|z.re\| ≤ ‖z‖` in the context |

**R29 · `rw [sq_abs]`** changes the **goal**: `|a| ^ 2 = a ^ 2`. Placeholders: `(a : ℝ)`. In this problem
it is mostly a hint: `nlinarith [abs_nonneg a, sq_abs a]` gets from `|a| ≤ c` and `c ^ 2 ≤ b` to
`a ^ 2 ≤ b` (`abs_nonneg a : 0 ≤ |a|`).

| Before | After |
|---|---|
| ⊢ P (\|a\| ^ 2) | `⊢ P (a ^ 2)` |

```lean-goal
⊢ P (|a| ^ 2)
```

---

## Part 5 · `tsirelson`

Statement: under the hypotheses above, `(star ψ ⬝ᵥ ((A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) *ᵥ ψ)).re ≤ 2 * √2`.
Combine the four milestones as in step 5 of *The math*.

**R30 · `set C := e with hC`** changes the **goal and the context**: every occurrence of `e` in the goal
becomes `C`, and the context gains the definition `C := e` and the equation `hC : C = e` (use
`rw [hC]` to unfold). Placeholders: `{R : Type} [Ring R] (a b : R)`.

| Before | After |
|---|---|
| `⊢ P (a * b + b * a)` | `C : R := a * b + b * a, hC : C = a * b + b * a ⊢ P C` |

**R31 · `simp only [Matrix.IsHermitian]`** changes the **goal**: it unfolds `A.IsHermitian` to `Aᴴ = A`.
Placeholders: `{n : Type} (A : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ A.IsHermitian` | `⊢ Aᴴ = A` |

**R32 · `rw [Matrix.conjTranspose_sub]`, `rw [Matrix.conjTranspose_add]`** change the **goal**:
`(M - N)ᴴ = Mᴴ - Nᴴ`, `(M + N)ᴴ = Mᴴ + Nᴴ`. Placeholders: `(M N K : Matrix n n ℂ)`.

| Before | After `rw [Matrix.conjTranspose_sub]` | After `rw [Matrix.conjTranspose_add]` |
|---|---|---|
| `⊢ P (M + N - K)ᴴ` | `⊢ P ((M + N)ᴴ - Kᴴ)` | `⊢ P (Mᴴ + Nᴴ - Kᴴ)` |

**R33 · `rw [Matrix.conjTranspose_mul]`** changes the **goal**: `(M * N)ᴴ = Nᴴ * Mᴴ`; the order flips. So
`(A₀ * B₀)ᴴ = B₀ * A₀` once `hA₀.eq`, `hB₀.eq` apply, and `c₀₀` turns it back into `A₀ * B₀`. It also gives
$(PQ)^\dagger(PQ) = Q^\dagger P^\dagger P Q$ for products of unitaries.
Placeholders: `{n : Type} [Fintype n] (M N : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P (M * N)ᴴ` | `⊢ P (Nᴴ * Mᴴ)` |

**R34 · `rw [Matrix.sub_mulVec]`** changes the **goal**: `(A - B) *ᵥ x = A *ᵥ x - B *ᵥ x`.
Placeholders: `(A B : Matrix n n ℂ) (x : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((A - B) *ᵥ x)` | `⊢ P (A *ᵥ x - B *ᵥ x)` |

**R35 · `rw [dotProduct_sub]`** changes the **goal**: `v ⬝ᵥ (x - y) = v ⬝ᵥ x - v ⬝ᵥ y`.
Placeholders: `(v x y : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ (x - y))` | `⊢ P (v ⬝ᵥ x - v ⬝ᵥ y)` |

**R36 · `Matrix.ofNat_mulVec`, `dotProduct_smul`, `smul_eq_mul`** change the **goal**: the numeral matrix
`4` acts as the scalar `4`, which leaves the inner product. Plain `simp [hψ]` does all three and then
`4 * 1 = 4`. Placeholders: `{n : Type} [Fintype n] [DecidableEq n] (ψ : n → ℂ)`.

| Before | After `Matrix.ofNat_mulVec` | After `dotProduct_smul` | After `smul_eq_mul` |
|---|---|---|---|
| `⊢ P (star ψ ⬝ᵥ 4 *ᵥ ψ)` | `⊢ P (star ψ ⬝ᵥ 4 • ψ)` | `⊢ P (4 • (star ψ ⬝ᵥ ψ))` | `⊢ P (4 * star ψ ⬝ᵥ ψ)` |

**R37 · `refine h.trans ?_`** changes the **goal**: with `h : a ≤ b`, the goal `a ≤ c` becomes `b ≤ c`
(`h.trans` is `le_trans h`). With `h := expect_sq_le C hC ψ hψ` it trades `⟨C⟩²` for `⟨C²⟩`.
Placeholders: `{α : Type} [Preorder α] (a b c : α)`.

| Before | After |
|---|---|
| `⊢ a ≤ c` | `⊢ b ≤ c` |

**R38 · `simp only [Complex.sub_re, Complex.add_re]`** changes the **goal**: real part of a difference/sum
is the difference/sum of real parts. Placeholders: `(z w u : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (z - (w + u)).re` | `⊢ P (z.re - (w.re + u.re))` |

**R39 · `Complex.re_ofNat` (or `norm_num`)** changes the **goal**: `Complex.re 4 = 4`. `norm_num` does this
and also moves terms across the inequality (see W5).

| Before | After |
|---|---|
| `⊢ P (Complex.re 4)` | `⊢ P 4` |

**R40 · `rw [abs_le] at h`** changes the **context**: `abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b`. Two-sided
bounds are what `linarith` can use. `rw [abs_le] at h1 h2 h3 h4` does several at once.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : \|a\| ≤ b` and `⊢ G` | `h : -b ≤ a ∧ a ≤ b ⊢ G` |

**R41 · `linarith`** **closes** a linear (in)equality over `ℝ` that follows from the hypotheses by adding
them with nonnegative coefficients; it splits `∧` hypotheses. Products of unknowns are atoms. Placeholders:
`(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ a - b ≤ 2` | closed |

**R42 · `Real.sq_sqrt`, `Real.sqrt_nonneg`** change the **goal** with `rw`: `0 ≤ x → √x ^ 2 = x`, and
`Real.sqrt_nonneg x : 0 ≤ √x`. As `nlinarith` hints they finish `t ^ 2 ≤ 4x ⟹ t ≤ 2√x`:
`nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by norm_num), Real.sqrt_nonneg x]`. Placeholders: `(x : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `⊢ P (√x ^ 2)` | `⊢ P x` |

**W5: a real part bounded through unit-modulus terms.** With `hz : |z.re| ≤ 1`, `hw : |w.re| ≤ 1` and
`ht : t ≤ (2 - (z - w)).re`: R37 with `ht`, R38, `norm_num` (R39, and it moves terms), R40, R41:

```lean-goal
⊢ t ≤ 4
⊢ (2 - (z - w)).re ≤ 4
⊢ Complex.re 2 - (z.re - w.re) ≤ 4
⊢ 2 ≤ 4 + (z.re - w.re)
```

**W6: the last step**, `t ^ 2 ≤ 12 ⟹ t ≤ 2 * √3`, is one `nlinarith` call with the R42 hints for `3`:

```lean-goal
⊢ t ≤ 2 * √3
```

---

## Traps

- `ring` fails on matrices (non-commutative). `noncomm_ring` cannot match the matrix numeral `4` with
  `4 • 1`. Expand with `simp only` (R20–R22), split the numeral (R24), finish with `abel` (R25).
- `simp only [mul_assoc, sw c₀₀, …]` only sees `b * (a * x)` after re-association; keep `mul_assoc` in the
  same call as the helpers.
- `rw [norm_sq_eq_re_inner]` without `(𝕜 := ℂ)` fails with a metavariable error (R6).
- `EuclideanSpace.inner_eq_star_dotProduct` puts the `star` on the second factor (R3): finish with
  `dotProduct_comm` (R5).
- After R6, R3, R4, R5 the norm fact `hn` is left at `RCLike.re (star z ⬝ᵥ z) = (star z ⬝ᵥ z).re`: `rw` does
  not see that the two real parts agree, `rfl` does (W2).
- In `um`, plain `rw [← mul_assoc]` regroups the wrong product (`Qᴴ * Pᴴ * P * Q`, where `hP` cannot fire);
  aim it with `← mul_assoc Pᴴ` after `mul_assoc` (R19).
- Type the vector once: `(WithLp.toLp 2 x : EuclideanSpace ℂ n)`. Without it Lean does not know which
  inner product is meant.
- `star ψ ⬝ᵥ C *ᵥ ψ` is `star ψ ⬝ᵥ (C *ᵥ ψ)`; `4 * star ψ ⬝ᵥ ψ` is `4 * (star ψ ⬝ᵥ ψ)` (precedence).
- A `have` belongs to one proof: Part 2's helpers are not visible in Part 5; milestones are, by name.
- `nlinarith` needs the sign facts as hints (`norm_nonneg`, `abs_nonneg`, `Real.sqrt_nonneg`); it does not
  look them up.
- After `set C := …`, a later `rw [chsh_sq_matrix …]` needs the expanded operator: `rw [hC]` first.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `x : n → ℂ` as an ℓ² vector | `(WithLp.toLp 2 x : EuclideanSpace ℂ n)` | R1 |
| Cauchy–Schwarz | `have h := norm_inner_le_norm (𝕜 := ℂ) u v` | R2 |
| `inner` → `⬝ᵥ` | `rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct_comm]` | R3–R5 |
| `‖u‖ ^ 2` → real part | `rw [norm_sq_eq_re_inner (𝕜 := ℂ)]` | R6 |
| rewrite a hypothesis | `rw [e] at h` | R7 |
| chain of `≤`/`=` | `calc a ≤ b := … ⏎ _ = c := …` | R8 |
| square both sides | `pow_le_pow_left₀ (norm_nonneg _) h 2` | R9, R10 |
| `(a * b) ^ 2` | `rw [mul_pow]` | R11 |
| `star (M *ᵥ v)` | `rw [star_mulVec]` | R12 |
| move a matrix across `⬝ᵥ` | `rw [dotProduct_mulVec]` / `rw [← dotProduct_mulVec]` | R13 |
| merge matrices | `rw [vecMul_vecMul]` / `rw [mulVec_mulVec]` | R14, R27 |
| `v ᵥ* 1`, `Complex.re 1` | `rw [vecMul_one]`, `rw [Complex.one_re, one_mul]` | R15, R16 |
| polynomial inequality | `nlinarith [sign facts]` | R17 |
| commute/cancel helpers | `have sw : ∀ {a b : M}, a * b = b * a → ∀ x, …` | R18 |
| expand matrix products | `simp only [add_mul, mul_add, sub_mul, mul_sub, mul_assoc, sw c₀₀, sq1 sA₀, sB₀, …]` | R20–R22 |
| leftover `* 1` | `simp only [mul_one]` | R23 |
| numeral `4` for `abel` | `rw [show (4 : Matrix n n ℂ) = 1 + 1 + 1 + 1 by norm_num]` | R24 |
| sums of atoms equal | `abel` | R25 |
| `Aᴴ` → `A` | `rw [hA.eq]` | R26 |
| `\|Re z\| ≤ ‖z‖` | `Complex.abs_re_le_norm z` | R28 |
| `\|a\|²` → `a²` | `sq_abs a` | R29 |
| name the operator | `set C := … with hC` | R30 |
| Hermitian `C` | `simp only [hC, IsHermitian, conjTranspose_add, conjTranspose_sub, conjTranspose_mul, hA₀.eq, …, c₀₀, …]` | R31–R33 |
| linearity of `⟨ψ\| · \|ψ⟩` | `simp [sub_mul, mul_sub, sub_mulVec, dotProduct_sub, hψ]` | R34–R36 |
| trade a bound | `refine h.trans ?_` | R37 |
| real parts | `simp only [Complex.sub_re, Complex.add_re]; norm_num` | R38, R39 |
| `\|a\| ≤ b` for `linarith` | `rw [abs_le] at h` | R40 |
| linear arithmetic | `linarith` | R41 |
| `x² ≤ 8 ⟹ x ≤ 2√2` | `nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]` | R42 |
| see the state | infoview | |
