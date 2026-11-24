# H087 · ZYZ decomposition of a qubit gate: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). The matrix notation, casts `ℝ → ℂ` and `ext i j` /
`fin_cases` are explained below (Reading the goals) and in `TACTIC_STATES.md`; M126 covers them at
length. **New here:** Mathlib's 2×2 matrices, the unitary group, determinants and conjugate transposes of 2×2
matrices, the complex exponential `cexp`, modulus `‖z‖` and argument `z.arg` (polar form),
`Real.arccos`, and the tactics `linear_combination`, `exact_mod_cast`, `congr`, `conv_lhs`,
`push_cast`, `linarith`, `nlinarith`, `set`, `obtain`.

**The math** (Nielsen–Chuang Thm 4.1). Write $U = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$,
$D = \det U = ad - bc$, $\bar z$ for the complex conjugate.

1. Unitarity $UU^\dagger = 1$ ($U^\dagger$ = conjugate transpose) gives, from entry $(0,0)$,
   $a\bar a + b\bar b = 1$, i.e. $|a|^2 + |b|^2 = 1$, and from entry $(1,0)$, $c\bar a + d\bar b = 0$.
   These two linear equations force $d = D\bar a$ and $c = -D\bar b$; also $|D| = 1$
   (milestone `unitary_struct`).
2. Multiplying out (milestone `zyz_product`):
   $e^{i\alpha}R_z(\beta)R_y(\gamma)R_z(\delta) = \begin{pmatrix}
   e^{i(\alpha-(\beta+\delta)/2)}\cos\frac\gamma2 & -e^{i(\alpha-(\beta-\delta)/2)}\sin\frac\gamma2 \\
   e^{i(\alpha+(\beta-\delta)/2)}\sin\frac\gamma2 & e^{i(\alpha+(\beta+\delta)/2)}\cos\frac\gamma2\end{pmatrix}$.
3. Take $\gamma = 2\arccos|a|$. Then $\cos\frac\gamma2 = |a|$ and
   $\sin\frac\gamma2 = \sqrt{1-|a|^2} = |b|$ (milestone `half_angle`; $\arccos$ maps $[-1,1]$ onto $[0,\pi]$).
4. Polar form: $z = |z|e^{i\arg z}$. With $\varphi = \arg D$, $\theta_a = \arg a$, $\theta_b = \arg b$ and
   $|D| = 1$: $D\bar z = e^{i(\varphi - \arg z)}|z|$ (milestone `polar_mul`).
5. Match the four phases: $\alpha - \frac{\beta+\delta}2 = \theta_a$,
   $\alpha - \frac{\beta-\delta}2 = \theta_b + \pi$ (the $\pi$ absorbs the minus sign, $e^{i\pi} = -1$),
   $\alpha + \frac{\beta-\delta}2 = \varphi - \theta_b - \pi$, $\alpha + \frac{\beta+\delta}2 = \varphi - \theta_a$.
   Solving: $\alpha = \varphi/2$, $\beta = \varphi - \theta_a - \theta_b - \pi$, $\delta = \theta_b - \theta_a + \pi$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves alone (the entry changes the
  context); `g : … → G` only exists to finish the example.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommRing α]`
  is a requirement on `α` (a *type class*; `[CommRing α]`: `+`, `-`, `*` with the usual commutative
  ring laws, met by `ℤ`, `ℝ`, `ℂ`).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix (Fin 2) (Fin 2) ℂ`, `!![a, b; c, d]`, `M i j` | 2×2 complex matrices, a literal with rows `a b` / `c d`, the entry in row `i`, column `j` (from 0) |
| `![a, b]`, `of f` | the vector `Fin 2 → α` with entries `a, b`; `Matrix.of` turns `f : Fin 2 → Fin 2 → α` into a matrix. `!![a, b; c, d]` is `of ![![a, b], ![c, d]]` |
| `c • M` | scalar `c` times every entry of `M` |
| `I` | `Complex.I`, the imaginary unit (the file has `open Complex`) |
| `unitaryGroup (Fin 2) ℂ` | `Matrix.unitaryGroup`: the matrices `M` with `star M * M = 1` and `M * star M = 1` |
| `star M` | the conjugate transpose $M^\dagger$ of a matrix: `star M i j = conj (M j i)`. Also written `Mᴴ` |
| `(starRingEnd ℂ) z` | Lean's name for the complex conjugate $\bar z$ (`conj z`); it is a ring map, so R24 applies |
| `1 1 0` | entry `(1, 0)` of the identity matrix `1`, which is `0` (`simp` evaluates it) |
| `M.det` | `Matrix.det M`, the determinant |
| `‖z‖` | the modulus $\lvert z\rvert$ of `z : ℂ`, a real number |
| `normSq z` | `Complex.normSq z` $= (\operatorname{Re} z)^2 + (\operatorname{Im} z)^2 = \lvert z\rvert^2$, a real number |
| `unitary ℂ` | the complex numbers `u` with `conj u * u = 1` and `u * conj u = 1`: the unit circle |
| `z.arg` | `Complex.arg z` $\in (-\pi, \pi]$, the angle of `z`; `arg 0 = 0` |
| `cexp z` | `Complex.exp z` |
| `↑x` | the real number `x` cast into `ℂ` (`Complex.ofReal x`) |
| `cos (↑γ / 2)`, `sin (↑γ / 2)` with no `Real.` | `Complex.cos`, `Complex.sin`: `simp` rewrote `↑(Real.cos x)` to `Complex.cos ↑x` |
| `Real.arccos x` | $\arccos x \in [0, \pi]$; for `x` outside `[-1, 1]` Mathlib returns a junk value, hence the side conditions of R19 |
| `√x` | `Real.sqrt x`, a real number (`0` for negative `x`) |
| `Real.pi` | $\pi$ (write `Real.pi`: the file does not `open Real`) |
| `x : ℂ := M 0 0` | a local definition made by `set` (R30) |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, as printed right after `fin_cases` (before `simp`) |
| `case «0».«1»` | the goal for entry (0, 1), made by `fin_cases i <;> fin_cases j` |
| `case e_a`, `case refine_1` | goal names made by `congr` and `refine`; ignore them |

---

## Part 1 · `unitary_struct`

Statement: for `U` in the unitary group, `U 1 1 = D * conj (U 0 0)`, `U 1 0 = -(D * conj (U 0 1))`,
`‖U 0 0‖ ^ 2 + ‖U 0 1‖ ^ 2 = 1` and `‖D‖ = 1`, where `D = U.det` (step 1 of the math).

**R1 · `have h := (Matrix.mem_unitaryGroup_iff).mp hM`** changes the **context**. The lemma is
`M ∈ unitaryGroup n α ↔ M * star M = 1`; `.mp` uses the `→` direction on `hM`. Placeholders:
`(M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ unitaryGroup (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `hM : M ∈ unitaryGroup (Fin 2) ℂ ⊢ G` | `h : M * star M = 1 ⊢ G` |

**R2 · `have e := congrFun (congrFun h i) j`** changes the **context**: from a matrix equation it takes the
equation of entry `(i, j)`. A matrix is a function of two arguments, and `congrFun : f = g → ∀ x, f x = g x`.
Placeholders: `(M N : Matrix (Fin 2) (Fin 2) ℂ) (h : M = N)`.

| Before | After |
|---|---|
| `h : M = N ⊢ G` | `e : M 1 0 = N 1 0 ⊢ G` |

**R3 · `simp [Matrix.mul_apply, Fin.sum_univ_two] at e`** changes the **context**: it evaluates the hypothesis
`e` instead of the goal. `Matrix.mul_apply : (M * N) i k = ∑ j, M i j * N j k` turns an entry of a product
into a sum over the middle index, `Fin.sum_univ_two : ∑ i, f i = f 0 + f 1` splits a sum over `Fin 2`;
`simp` itself applies `Matrix.star_apply` (`star N i j = conj (N j i)`) and
evaluates the identity's entries. `simp … at e₁ e₂` does several hypotheses at once. Placeholders:
`(M N : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `e : (M * star N) 1 0 = 1 1 0 ⊢ G` | `e : M 1 0 * (starRingEnd ℂ) (N 0 0) + M 1 1 * (starRingEnd ℂ) (N 0 1) = 0 ⊢ G` |

**R4 · `rw [Matrix.det_fin_two]`** changes the **goal**. The lemma is
`M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0` for any 2×2 matrix. `rw [← Matrix.det_fin_two]` folds it back.
Placeholders: `(M : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `⊢ P M.det` | `⊢ P (M 0 0 * M 1 1 - M 0 1 * M 1 0)` |

**R5 · `refine ⟨by tac, by tac, ?_, ?_⟩`** changes the **goal list**: the conjuncts written `by tac` are proved
on the spot, each `?_` stays as a goal. Placeholders: `(A B C D : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B ∧ C ∧ D` | `⊢ C`, `⊢ D` |

**R6 · `linear_combination c₁ * e₁ + c₂ * e₂`** **closes** a goal `lhs = rhs` from equations
`eᵢ : lhsᵢ = rhsᵢ`: it checks with `ring` that
`lhs - rhs - (c₁ * (lhs₁ - rhs₁) + c₂ * (lhs₂ - rhs₂)) = 0`. The coefficients `cᵢ` may be any terms, not
just numbers. To find them, multiply out `lhs - rhs` and match it against the `lhsᵢ - rhsᵢ`.
Placeholders: `(a b u : ℂ) (e₁ : a * u = 1) (e₂ : b * u = 0)`; here `b = -b * (a * u - 1) + a * (b * u - 0)`,
so `linear_combination (-b) * e₁ + a * e₂`.

| Before | After |
|---|---|
| `e₁ : a * u = 1, e₂ : b * u = 0 ⊢ b = 0` | no goals |

**R7 · `rw [Complex.mul_conj]`** changes the **goal** (or a hypothesis, with `at e`). The lemma is
`z * conj z = ↑(normSq z)`: the right side is a real number cast into `ℂ`. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (z * (starRingEnd ℂ) z)` | `⊢ P ↑(normSq z)` |

**R8 · `rw [Complex.normSq_eq_norm_sq]`** changes the **goal** (or a hypothesis). The lemma is
`normSq z = ‖z‖ ^ 2`. In a hypothesis that mentions `normSq` twice, `rw` rewrites only the instances of the
first match: write the lemma twice, `rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at e`.
Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (normSq z)` | `⊢ P (‖z‖ ^ 2)` |

**R9 · `exact_mod_cast e`** **closes** a goal that is `e` up to casts: it moves all casts `↑` outward on both
and compares. Use it when `e` lives in `ℂ` and the goal is the same statement in `ℝ`. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `e : ↑x + ↑y = 1 ⊢ x + y = 1` | no goals |

**R10 · `Matrix.det_of_mem_unitary`** adds to the **context** (with `have`): `M ∈ unitaryGroup n α → M.det ∈ unitary α`.
Placeholders: `(M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M ∈ unitaryGroup (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `hM : M ∈ unitaryGroup (Fin 2) ℂ ⊢ G` | `h : M.det ∈ unitary ℂ ⊢ G` |

**R11 · `exact CStarRing.norm_of_mem_unitary hu`** **closes** `‖u‖ = 1` from `hu : u ∈ unitary ℂ` (in any
C*-ring, unitaries have norm 1; `ℂ` is one). Combine with R10: `CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)`.
Placeholders: `(u : ℂ)`.

| Before | After |
|---|---|
| `hu : u ∈ unitary ℂ ⊢ ‖u‖ = 1` | no goals |

---

## Part 2 · `zyz_product`

Statement: `cexp (↑α * I) • (Rz β * Ry γ * Rz δ)` equals the explicit matrix of step 2 of the math.
After unfolding and `ext i j; fin_cases i <;> fin_cases j <;> simp`, each of the four entry goals has the
shape `cexp (↑α * I) * (cexp u * c * cexp v) = cexp w * c`, with `c` a `cos (↑γ / 2)` or `sin (↑γ / 2)`
and `u v w` complex exponents.

**R12 · `rw [Matrix.mul_fin_two]`** changes the **goal**: the product of two 2×2 literals becomes one literal.
Placeholders: `{α : Type} [CommRing α] (a b c d e f g k : α)`.

| Before | After |
|---|---|
| `⊢ P (!![a, b; c, d] * !![e, f; g, k])` | `⊢ P !![a * e + b * g, a * f + b * k; c * e + d * g, c * f + d * k]` |

**R13 · `rw [Matrix.smul_of]`** changes the **goal**: `s • of f = of (s • f)`. It moves a scalar inside the
literal; `simp` then evaluates `(s • f) i j = s * f i j`. Placeholders: `{α : Type} [CommRing α] (s a b c d : α)`.

| Before | After |
|---|---|
| `⊢ P (s • !![a, b; c, d])` | `⊢ P (of (s • ![![a, b], ![c, d]]))` |

**R14 · `simp only [mul_zero, zero_mul, add_zero, zero_add]`** changes the **goal**: it removes the `0` terms that
R12 creates from the zeros of `Rz`. (`a * 0 = 0`, `0 * a = 0`, `a + 0 = a`, `0 + a = a`.) Placeholders:
`{α : Type} [CommRing α] (a b c : α)`.

| Before | After |
|---|---|
| `⊢ P (0 * c + (a * b + c * 0))` | `⊢ P (a * b)` |

**R15 · `Complex.exp_add`** changes the **goal**. The lemma is `cexp (x + y) = cexp x * cexp y`. Left to right
it splits; right to left (`rw [← Complex.exp_add]`) it merges two *adjacent* factors. A helper
`have e : ∀ x y : ℂ, cexp x * cexp y = cexp (x + y) := fun x y => (Complex.exp_add x y).symm` names the
merging direction (`.symm` flips an equation). Placeholders: `(x y : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (cexp x * cexp y)` | `⊢ P (cexp (x + y))` |

**R16 · `rw [show ∀ a b c : α, … from fun a b c => by ring]`** changes the **goal**: `rw` matches terms
literally, so it cannot see `a * (b * c)` as `a * c * b`. State the reordering you need as a fact, prove it by
`ring`, and rewrite with it. The `∀` form matches any `a b c`; for one specific rearrangement write
`rw [show t₁ = t₂ by ring]`. Placeholders: `{α : Type} [CommRing α] (x y z : α)`.

| Before | After |
|---|---|
| `⊢ P (x * (y * z))` | `⊢ P (x * z * y)` |

**R17 · `congr 2`** changes the **goal**: it peels two layers of the same function off both sides and leaves
the arguments to prove equal. On `cexp a * ↑c = cexp b * ↑c`: layer 1 is `* ↑c` (the right factors agree and
are closed), layer 2 is `cexp`. `congr` closes leftovers by `rfl` or by an assumption; `congr 3` would go one
layer too deep. Placeholders: `(a b : ℂ) (c : ℝ)`; in the example `h : b = a` is stated backwards so that
`congr` cannot close the goal by assumption.

| Before | After |
|---|---|
| `⊢ cexp a * ↑c = cexp b * ↑c` | `⊢ a = b` |

`ring` then proves the exponent equation (TACTIC_STATES, "Closing").

**W2: two phase gates multiply by adding angles** (R12, R14, then R15 right to left):

```lean-goal
⊢ !![cexp x, 0; 0, 1] * !![cexp y, 0; 0, 1] = !![cexp (x + y), 0; 0, 1]
⊢ !![cexp x * cexp y + 0 * 0, cexp x * 0 + 0 * 1; 0 * cexp y + 1 * 0, 0 * 0 + 1 * 1] = !![cexp (x + y), 0; 0, 1]
⊢ !![cexp x * cexp y, 0; 0, 1] = !![cexp (x + y), 0; 0, 1]
```

---

## Part 3 · `half_angle`

Statement: for `0 ≤ r ≤ 1`, `Real.cos (2 * Real.arccos r / 2) = r` and
`Real.sin (2 * Real.arccos r / 2) = √(1 - r ^ 2)` (step 3 of the math).

**R18 · `rw [mul_div_cancel_left₀ _ two_ne_zero]`** changes the **goal**. The lemma is
`b ≠ 0 → b * a / b = a`; `two_ne_zero : 2 ≠ 0` supplies the side condition and `_` lets Lean find `a`.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (2 * x / 2)` | `⊢ P x` |

**R19 · `Real.cos_arccos`** **closes** (with `exact`): `-1 ≤ x → x ≤ 1 → Real.cos (Real.arccos x) = x`.
Placeholders: `(x : ℝ) (h0 : -1 ≤ x) (h1 : x ≤ 1)`.

| Before | After |
|---|---|
| `h0 : -1 ≤ x, h1 : x ≤ 1 ⊢ Real.cos (Real.arccos x) = x` | no goals |

**R20 · `rw [Real.sin_arccos]`** changes the **goal**. The lemma is `Real.sin (Real.arccos x) = √(1 - x ^ 2)`,
with no side condition. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.sin (Real.arccos x))` | `⊢ P √(1 - x ^ 2)` |

**R21 · `linarith`** **closes** a goal `t ≤ s`, `t < s`, `t = s` (or `False`) that follows from the hypotheses
by adding up linear (in)equalities with nonnegative coefficients. It treats `‖a‖`, `‖a‖ ^ 2` as unknowns.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `h0 : 0 ≤ x ⊢ -1 ≤ x` | no goals |

---

## Part 4 · `polar_mul`

Statement: for `‖D‖ = 1`, `D * conj z = cexp (↑(D.arg - z.arg) * I) * ↑‖z‖` (step 4 of the math).

**R22 · `Complex.norm_mul_exp_arg_mul_I`** changes the **goal**. The lemma is
`↑‖z‖ * cexp (↑z.arg * I) = z` (polar form; it holds for `z = 0` as well). Right to left,
`rw [← Complex.norm_mul_exp_arg_mul_I z]` replaces `z` by its polar form. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P z` | `⊢ P (↑‖z‖ * cexp (↑z.arg * I))` |

**R23 · `conv_lhs => rw [h]`** changes the **goal**, but only on the left side of `=`. Needed here because
R22 right to left rewrites *every* `z`, including the one inside `z.arg` on the right side. Placeholders:
`(z w : ℂ) (h : z = w)`.

| Before | After |
|---|---|
| `⊢ z = ↑z.re` | `⊢ w = ↑z.re` |

**R24 · `rw [map_mul]`** changes the **goal**: `f (x * y) = f x * f y` for any map `f` that respects `*`, here
`starRingEnd ℂ` (complex conjugation). Placeholders: `(x y : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (x * y))` | `⊢ P ((starRingEnd ℂ) x * (starRingEnd ℂ) y)` |

**R25 · `rw [Complex.conj_ofReal]`** changes the **goal**: `conj ↑r = ↑r` for `r : ℝ`. Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) ↑r)` | `⊢ P ↑r` |

**R26 · `rw [← Complex.exp_conj]`** changes the **goal**. The lemma is `cexp (conj x) = conj (cexp x)`; right
to left it moves `conj` inside the exponential. Placeholders: `(x : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (cexp x))` | `⊢ P (cexp ((starRingEnd ℂ) x))` |

**R27 · `push_cast`** changes the **goal**: it moves casts `↑` inward through `+`, `-`, `*`, `/`, `^`, so
`↑(x - y)` becomes `↑x - ↑y` and `ring` can see the parts. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ↑(x - y)` | `⊢ P (↑x - ↑y)` |

**W3: polar form of `z * z`** (R23 with R22, R27, then `two_mul`, R34 and R15, then `ring`):

```lean-goal
⊢ z * z = ↑(‖z‖ ^ 2) * cexp (↑(2 * z.arg) * I)
⊢ ↑‖z‖ * cexp (↑z.arg * I) * (↑‖z‖ * cexp (↑z.arg * I)) = ↑(‖z‖ ^ 2) * cexp (↑(2 * z.arg) * I)
⊢ ↑‖z‖ * cexp (↑z.arg * I) * (↑‖z‖ * cexp (↑z.arg * I)) = ↑‖z‖ ^ 2 * cexp (2 * ↑z.arg * I)
⊢ ↑‖z‖ * cexp (↑z.arg * I) * (↑‖z‖ * cexp (↑z.arg * I)) = ↑‖z‖ ^ 2 * (cexp (↑z.arg * I) * cexp (↑z.arg * I))
```

In `polar_mul` the same pattern needs one more move: write the right exponent `↑(D.arg - z.arg) * I` as
`↑D.arg * I + conj (↑z.arg * I)` (R16 with `by simp; ring`), so that R15 splits it into the two factors
the left side has.

---

## Part 5 · `zyz`

Statement: every `U ∈ unitaryGroup (Fin 2) ℂ` is `cexp (↑α * I) • (Rz β * Ry γ * Rz δ)` for some
`α β γ δ : ℝ` (step 5 of the math). Uses all four milestones.

**R28 · `obtain ⟨h₁, h₂, h₃⟩ := e`** changes the **context**: a hypothesis (or a milestone applied to
arguments, `obtain ⟨…⟩ := unitary_struct U hU`) that is a conjunction is replaced by its parts.
Placeholders: `(A B C : Prop) (e : A ∧ B ∧ C)`.

| Before | After |
|---|---|
| `e : A ∧ B ∧ C ⊢ G` | `h₁ : A, h₂ : B, h₃ : C ⊢ G` |

**R29 · `rw [Matrix.eta_fin_two M]`** changes the **goal**: `M = !![M 0 0, M 0 1; M 1 0, M 1 1]`, so a 2×2
matrix variable becomes a literal of its entries, which `rw [hd, hc]` can then rewrite. Placeholders:
`(M : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `⊢ P M` | `⊢ P !![M 0 0, M 0 1; M 1 0, M 1 1]` |

**R30 · `set x := e`** changes the **context and the goal**: it adds the local definition `x := e` and replaces
every `e` in the goal and in all hypotheses by `x`. Shorter goals, same meaning. Placeholders:
`(M : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `h : P (M 0 0) ⊢ P (M 0 0)` | `x : ℂ := M 0 0, h : P x ⊢ P x` |

**R31 · `nlinarith [t₁, t₂]`** **closes** a polynomial (in)equality: like `linarith`, but it also multiplies
pairs of hypotheses and hint terms `tᵢ`. Give it the facts it cannot guess, such as
`norm_nonneg z : 0 ≤ ‖z‖` or `sq_nonneg y : 0 ≤ y ^ 2`. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `h : x ^ 2 + y ^ 2 = 1, hx : 0 ≤ x ⊢ x ≤ 1` | no goals |

**R32 · `Real.sqrt_sq`** **closes** (with `exact`): `0 ≤ a → √(a ^ 2) = a`. Placeholders: `(a : ℝ) (ha : 0 ≤ a)`.

| Before | After |
|---|---|
| `ha : 0 ≤ a ⊢ √(a ^ 2) = a` | no goals |

**R33 · `rw [Complex.exp_pi_mul_I]`** changes the **goal**: `cexp (↑Real.pi * I) = -1`, i.e. $e^{i\pi} = -1$.

| Before | After |
|---|---|
| `⊢ P (cexp (↑Real.pi * I))` | `⊢ P (-1)` |

**R34 · `rw [add_mul]`** changes the **goal**: `(a + b) * c = a * c + b * c`. It turns `(↑x + ↑π) * I` into a
sum so R15 can split the exponential. Placeholders: `{α : Type} [CommRing α] (a b c : α)`.

| Before | After |
|---|---|
| `⊢ P ((a + b) * c)` | `⊢ P (a * c + b * c)` |

**R35 · `rw [sub_add_cancel] at h`** changes the **context**: `a - b + b = a` inside hypothesis `h`. Use it
to get the `x - π` fact from the `x + π` fact applied to `x - π`. Placeholders: `{α : Type} [CommRing α] (a b : α)`.

| Before | After |
|---|---|
| `h : P (a - b + b) ⊢ G` | `h : P a ⊢ G` |

**R36 · `rw [neg_mul]`, `rw [neg_neg]`** change the **goal**: `-a * b = -(a * b)` and `- -a = a`. They clean the
signs once R33 has turned a phase into a minus sign. Placeholders: `{α : Type} [CommRing α] (a b : α)`.

| Before | After `rw [neg_mul]` | After `rw [neg_neg]` |
|---|---|---|
| `⊢ P (-(-a * b))` | `⊢ P (- -(a * b))` | `⊢ P (a * b)` |

**R37 · `rw [mul_comm]`** changes the **goal**: `a * b = b * a`, applied to the first product found. Use it to
flip R22 into `cexp (↑z.arg * I) * ↑‖z‖ = z`, the order `polar_mul` produces. Placeholders:
`{α : Type} [CommRing α] (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (a * b)` | `⊢ P (b * a)` |

**R38 · `refine ⟨x₁, x₂, ?_⟩`** changes the **goal**: the witnesses of `∃ a b, …` are chosen now and the
property is left to prove. For four angles: `refine ⟨α₀, β₀, γ₀, δ₀, ?_⟩`. Placeholders: `(P : ℝ → ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ ∃ a b, P a b` | `⊢ P 1 2` |

**W4: a phase shifted by `2π` is unchanged** (R27, then R34, R15 and `Complex.exp_two_pi_mul_I`, then `ring`);
the `+ π` fact of `zyz` has the same shape with R33:

```lean-goal
⊢ cexp (↑(x + 2 * Real.pi) * I) = cexp (↑x * I)
⊢ cexp ((↑x + 2 * ↑Real.pi) * I) = cexp (↑x * I)
⊢ cexp (↑x * I) * 1 = cexp (↑x * I)
```

**W1: one entry of `M * N = 1` as a number equation** (R2, R3), the move that starts Part 1:

```lean-goal
⊢ M 0 0 * N 0 1 + M 0 1 * N 1 1 = 0
```

---

## Traps

- `rw [← Complex.norm_mul_exp_arg_mul_I D]` rewrites every `D` in the goal, also inside `D.arg` on the right
  side, and the goal becomes unreadable. Use `conv_lhs => rw [...]` (R23).
- After `rw [Matrix.det_fin_two]` (R4) all four conjuncts of `unitary_struct` mention the expanded determinant,
  so R10–R11 no longer match `‖U.det‖`. Fold it back with `rw [← Matrix.det_fin_two]` in that goal.
- `rw [Complex.exp_add]` splits, `rw [← Complex.exp_add]` merges, and merging only works on two adjacent
  factors. Reorder first (R16).
- `simp` rewrites `↑(Real.cos x)` to `Complex.cos ↑x`. In `zyz`, rewrite with `hcos`, `hsin` (from
  `half_angle`) right after `rw [zyz_product]`, before any `simp`, while the goal still has `Real.cos`.
- `set a := U 0 0` also rewrites hypotheses. Do the `rw [Matrix.eta_fin_two U, hd, hc]` first, then `set`, so
  the goal and `hd`, `hc`, `hab` all speak about `a`, `b`, `D`.
- `linear_combination` checks `lhs - rhs - Σ cᵢ (lhsᵢ - rhsᵢ) = 0`: a wrong sign on one coefficient fails, and
  the error shows the leftover `ring` could not close.
- `Real.arccos` gives junk outside `[-1, 1]`; R19 needs `-1 ≤ ‖a‖` (from `norm_nonneg` by R21) and `‖a‖ ≤ 1`
  (by R31 from `hab`).
- `Complex.arg 0 = 0` and `‖0‖ = 0`: polar form holds for `0` too, so `a = 0` or `b = 0` needs no case split.
- `Real.pi` must be written in full; `π` is only available after `open Real`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unitary → `M * star M = 1` | `have h := (Matrix.mem_unitaryGroup_iff).mp hU` | R1 |
| entry `(i, j)` of a matrix equation | `have e := congrFun (congrFun h i) j` | R2 |
| evaluate it | `simp [Matrix.mul_apply, Fin.sum_univ_two] at e` | R3 |
| `det` of a 2×2 | `rw [Matrix.det_fin_two]` | R4 |
| close some conjuncts inline | `refine ⟨by tac, by tac, ?_, ?_⟩` | R5 |
| equation from equations, ring-linear | `linear_combination c₁ * e₁ + c₂ * e₂` | R6 |
| `z * conj z → ‖z‖ ^ 2` | `rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]` | R7, R8 |
| same statement up to casts | `exact_mod_cast e` | R9 |
| `‖det U‖ = 1` | `CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)` | R10, R11 |
| multiply 2×2 literals | `simp only [Matrix.mul_fin_two, Matrix.smul_of, mul_zero, …]` | R12–R14 |
| `cexp x * cexp y ↔ cexp (x + y)` | `rw [← Complex.exp_add]` / `rw [Complex.exp_add]` | R15 |
| reorder before `rw` | `rw [show ∀ a b c : ℂ, … from fun a b c => by ring]` | R16 |
| equal exponents suffice | `congr 2` | R17 |
| `2 * x / 2 → x` | `rw [mul_div_cancel_left₀ _ two_ne_zero]` | R18 |
| `cos (arccos x)`, `sin (arccos x)` | `Real.cos_arccos h0 h1`, `Real.sin_arccos x` | R19, R20 |
| linear / polynomial arithmetic | `linarith`, `nlinarith [norm_nonneg a, …]` | R21, R31 |
| polar form, `z → ‖z‖ e^{i arg z}` | `conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]` | R22, R23 |
| conjugate a product / real / exponential | `rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]` | R24–R26 |
| casts inward | `push_cast` | R27 |
| split a milestone's `∧` | `obtain ⟨hd, hc, hab, hD⟩ := unitary_struct U hU` | R28 |
| matrix variable → literal | `rw [Matrix.eta_fin_two U]` | R29 |
| name a subterm | `set a := U 0 0` | R30 |
| `√(a ^ 2) = a` | `Real.sqrt_sq (norm_nonneg b)` | R32 |
| `e^{iπ} = -1` | `rw [Complex.exp_pi_mul_I]` | R33 |
| signs and order | `add_mul`, `sub_add_cancel`, `neg_mul`, `neg_neg`, `mul_comm` | R34–R37 |
| choose the four angles | `refine ⟨α₀, β₀, γ₀, δ₀, ?_⟩` | R38 |
