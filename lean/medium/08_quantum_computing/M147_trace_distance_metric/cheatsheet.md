# M147 · Trace distance is a unitarily invariant metric: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's density matrices (`MState`),
unitaries (`𝐔[d]`), unitary conjugation of a state (`MState.uConj`), Hermitian matrices (`HermitianMat`),
the trace norm (`Matrix.traceNorm`) and the trace distance (`TrDistance`); Mathlib's `linarith`,
`convert`, `simpa`.

The math. For complex `d × d` matrices, the trace norm is $\|A\|_1 = \operatorname{Tr}\sqrt{A^\dagger A}$,
the sum of the singular values of $A$ ($A^\dagger$ = conjugate transpose). The trace distance of two
density matrices is $T(\rho, \sigma) = \tfrac12 \|\rho - \sigma\|_1$. The three facts used:
$\|A\|_1 \ge 0$ with equality iff $A = 0$; $\|A + B\|_1 \le \|A\|_1 + \|B\|_1$; and
$\|U A U^\dagger\|_1 = \|A\|_1$ for unitary $U$ ($U U^\dagger = 1$). The exercise only transports these
to $T$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` (or `Q`) is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves alone.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddGroup α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- `{d : Type} [Fintype d] [DecidableEq d]`: `d` is a finite index type (rows/columns, e.g. `Fin 2`) whose
  elements can be compared by `=`. All matrices here are `Matrix d d ℂ`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `MState d` | a density matrix (mixed state) on `d`: Hermitian, positive semidefinite, trace 1 |
| `ρ.m` | the `Matrix d d ℂ` of the state `ρ` (by definition `ρ.M.mat`) |
| `ρ.M` | the state's `HermitianMat d ℂ`: a matrix bundled with a proof that it is Hermitian |
| `↑↑ρ` | `ρ.M.mat` printed as two coercions: state → `HermitianMat` → `Matrix`. Same as `ρ.m` |
| `↑A` (with `A : HermitianMat d ℂ`) | `A.mat`, the underlying matrix |
| `𝐔[d]`, `↥𝐔[d]` | `Matrix.unitaryGroup d ℂ`, the unitary `d × d` matrices; `↥` makes the set a type |
| `U : ↥𝐔[d]`, `↑U`, `U.val` | a unitary, bundled with its proof `U.2`; `↑U = U.val` is its matrix |
| `Mᴴ` | conjugate transpose $M^\dagger$ |
| `ρ.uConj U` | the rotated state $U \rho U^\dagger$ |
| `(HermitianMat.conj B) A` | `A.conj B`, the Hermitian matrix $B A B^\dagger$ |
| `{ M := …, nonneg := ⋯, tr := ⋯ }` | a state written out by its fields (matrix, PSD proof, trace proof) |
| `A.traceNorm` | $\|A\|_1$, a real number |
| `TrDistance ρ σ` | $\tfrac12 \|\rho.m - \sigma.m\|_1 : ℝ$ |
| `↑⟨↑V, ⋯⟩` | the matrix of a unitary rebuilt from `↑V` and a proof `⋯`; it is `↑V` |
| `case mp`, `case mpr` | the `→` and `←` halves of an `↔` |
| `inst✝¹ : Fintype d`, `inst✝ : DecidableEq d` | the unnamed instance arguments `[Fintype d] [DecidableEq d]` of the theorem |

---

## Part 1 · `td_eq_zero_iff`

Statement: `TrDistance ρ σ = 0 ↔ ρ = σ`. The distance vanishes exactly when the states are equal.

**R1 · `constructor`** changes the **goal list**: an `↔` becomes its two implications, named `mp` (→) and
`mpr` (←). Placeholders: `(A B : Prop)`. (TACTIC_STATES shows it on `∧`; on `↔` it works the same way.)

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

Then `intro h` (Lean basics) on the `mp` goal.

**R2 · `apply MState.ext_m`** changes the **goal**. The lemma is `MState.ext_m : ρ₁.m = ρ₂.m → ρ₁ = ρ₂`: two
states are equal when their matrices are (the PSD and trace fields are proofs, so they agree automatically).
Placeholders: `(ρ₁ ρ₂ : MState d)`.

| Before | After |
|---|---|
| `⊢ ρ₁ = ρ₂` | `⊢ ρ₁.m = ρ₂.m` |

**R3 · `rw [← sub_eq_zero]`** changes the **goal**. The lemma is `sub_eq_zero : a - b = 0 ↔ a = b`; `rw`
rewrites with an `↔` like with an `=`, and `←` uses it right to left. Placeholders:
`{α : Type} [AddGroup α] (a b : α)`. `AddGroup` means `+`, `0`, `-`; `ℝ`, `ℂ` and `Matrix d d ℂ` qualify.

| Before | After |
|---|---|
| `⊢ a = b` | `⊢ a - b = 0` |

**R4 · `rw [← Matrix.traceNorm_zero_iff]`** changes the **goal**. The lemma is
`Matrix.traceNorm_zero_iff (A) : A.traceNorm = 0 ↔ A = 0`. Placeholders: `(A : Matrix d d ℂ)`.

| Before | After |
|---|---|
| `⊢ A = 0` | `⊢ A.traceNorm = 0` |

**R5 · `unfold TrDistance at h`** changes the **context**: `h` gets the definition
`TrDistance ρ σ = 1 / 2 * (ρ.m - σ.m).traceNorm`. Placeholders: `(ρ₁ ρ₂ : MState d) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `h : P (TrDistance ρ₁ ρ₂) ⊢ P (1 / 2 * (ρ₁.m - ρ₂.m).traceNorm)` | `h : P (1 / 2 * (ρ₁.m - ρ₂.m).traceNorm) ⊢ P (1 / 2 * (ρ₁.m - ρ₂.m).traceNorm)` |

**R6 · `have := Matrix.traceNorm_nonneg A`** changes the **context**: it adds `this : 0 ≤ A.traceNorm`.
Placeholders: `(A : Matrix d d ℂ)`. You can also pass it straight to `linarith` (R7) instead of a `have`.

| Before | After |
|---|---|
| `⊢ G` | `this : 0 ≤ A.traceNorm ⊢ G` |

**R7 · `linarith [t₁, …]`** **closes** a goal `=`, `≤`, `<` over `ℝ` that follows linearly from the
hypotheses and the extra facts `tᵢ`. Anything that is not `+`, `-`, a numeral, or a numeral times
something is an unknown to it: `A.traceNorm` is just a real `x`, and `linarith` does not know `0 ≤ x`
unless you pass `Matrix.traceNorm_nonneg A`. It proves an `=` goal as two `≤`.

```lean-goal
⊢ A.traceNorm = 0
```

with `h : 1 / 2 * A.traceNorm ≤ 0` closes by `linarith [Matrix.traceNorm_nonneg A]` and not by `linarith`.

**R8 · `rintro rfl`** changes the **goal and the context**: it introduces `a = b` and substitutes it at once,
so `b` leaves the context and every `b` becomes `a`. Placeholders: `{α : Type} (a b : α) (P : α → α → Prop)`.

| Before | After |
|---|---|
| `⊢ a = b → P a b` | `⊢ P a a` |

**R9 · `simp`** on `(A - A).traceNorm` changes the **goal**: `sub_self` gives `A - A = 0`, then
`Matrix.traceNorm_zero : traceNorm 0 = 0`. With `simp [TrDistance]` it first unfolds the definition (R12)
and also clears `1 / 2 * 0`. Placeholders: `(A : Matrix d d ℂ) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (A - A).traceNorm` | `⊢ P 0` |

---

## Part 2 · `td_triangle`

Statement: `TrDistance ρ τ ≤ TrDistance ρ σ + TrDistance σ τ`. Write
$\rho - \tau = (\rho - \sigma) + (\sigma - \tau)$ and apply the triangle inequality of $\|\cdot\|_1$.

**R10 · `have := Matrix.traceNorm_add_le A B`** changes the **context**. The lemma is
`Matrix.traceNorm_add_le (A B : Matrix n n ℂ) : (A + B).traceNorm ≤ A.traceNorm + B.traceNorm`. You choose
`A` and `B`: the two differences whose sum is the left side. Placeholders: `(A B : Matrix d d ℂ)`.

| Before | After |
|---|---|
| `⊢ G` | `this : (A + B).traceNorm ≤ A.traceNorm + B.traceNorm ⊢ G` |

**R11 · `rw [sub_add_sub_cancel] at this`** changes the **context**. The lemma is
`sub_add_sub_cancel (a b c) : a - b + (b - c) = a - c`. Placeholders: `{α : Type} [AddGroup α] (a b c : α)
(Q : α → Prop)`; here `α = Matrix d d ℂ`.

| Before | After |
|---|---|
| `this : Q (a - b + (b - c)) ⊢ Q (a - c)` | `this : Q (a - c) ⊢ Q (a - c)` |

**R12 · `unfold TrDistance`** changes the **goal**: every `TrDistance x y` becomes
`1 / 2 * (x.m - y.m).traceNorm`, so the goal is a linear inequality in three trace norms and `this` (R10,
R11) gives it after multiplying by `1 / 2`: `linarith` (R7, no extra facts needed).
Placeholders: `(ρ₁ ρ₂ : MState d) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (TrDistance ρ₁ ρ₂)` | `⊢ P (1 / 2 * (ρ₁.m - ρ₂.m).traceNorm)` |

**W1: three matrices.** R10 twice, on `(A + B) + C` and on `A + B`, then `linarith`:

```lean-goal
⊢ (A + B + C).traceNorm ≤ A.traceNorm + B.traceNorm + C.traceNorm
```

---

## Part 3 · `td_unitary`

Statement: `TrDistance (ρ.uConj U) (σ.uConj U) = TrDistance ρ σ`. After unfolding, the left side is
$\tfrac12\|U\rho U^\dagger - U\sigma U^\dagger\|_1 = \tfrac12\|U(\rho - \sigma)U^\dagger\|_1$, and unitary
invariance removes `U`.

### Exposing the matrices

`simp only [TrDistance, MState.uConj, MState.m, HermitianMat.conj_apply_mat]` does R12 and R13–R15 in one
step on both sides.

**R13 · `simp only [MState.uConj]`** changes the **goal**: `ρ.uConj U` is replaced by the state it is
defined as, whose matrix field is `HermitianMat.conj ↑U ↑ρ`. Placeholders: `(ρ : MState d) (U : 𝐔[d])
(P : Matrix d d ℂ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (ρ.uConj U).m` | `⊢ P { M := (HermitianMat.conj ↑U) ↑ρ, nonneg := ⋯, tr := ⋯ }.m` |

**R14 · `simp only [MState.m]`** changes the **goal**: `x.m` becomes `x.M.mat`. On a plain state it prints as
`↑↑ρ`; on R13's written-out state it picks the field `M`, giving `↑((HermitianMat.conj ↑U) ↑ρ)`.
Placeholders: `(ρ : MState d) (P : Matrix d d ℂ → Prop)`.

| Before | After |
|---|---|
| `⊢ P ρ.m` | `⊢ P ↑↑ρ` |

**R15 · `simp only [HermitianMat.conj_apply_mat]`** changes the **goal**. The lemma is
`(A.conj B).mat = B * A.mat * Bᴴ`. Placeholders: `(A : HermitianMat d ℂ) (B : Matrix d d ℂ)`.

| Before | After |
|---|---|
| `⊢ P ↑((HermitianMat.conj B) A)` | `⊢ P (B * ↑A * Bᴴ)` |

### Factoring out `U`

**R16 · `rw [← Matrix.sub_mul]`** changes the **goal**. The lemma is
`Matrix.sub_mul (M M' N) : (M - M') * N = M * N - M' * N`; right to left it factors the common right
factor `N` out. `*` groups to the left, so `U * A * Uᴴ` is `(U * A) * Uᴴ`: do this one first.
Placeholders: `(M M' N : Matrix d d ℂ)`.

| Before | After |
|---|---|
| `⊢ P (M * N - M' * N)` | `⊢ P ((M - M') * N)` |

**R17 · `rw [← Matrix.mul_sub]`** changes the **goal**. The lemma is
`Matrix.mul_sub (M N N') : M * (N - N') = M * N - M * N'`; right to left it factors the left factor `M` out.
Placeholders: `(M N N' : Matrix d d ℂ)`.

| Before | After |
|---|---|
| `⊢ P (M * N - M * N')` | `⊢ P (M * (N - N'))` |

### Unitary invariance of the trace norm (the milestone `key`)

**R18 · `Matrix.traceNorm_unitary_conj`** changes the **context** when used in a `have`. The lemma is
`traceNorm_unitary_conj {A : Matrix n n R} {U : unitaryGroup n R} : (↑U * A * (↑U)ᴴ).traceNorm = A.traceNorm`
for `[RCLike R]` (`R` is `ℝ` or `ℂ`). Trap: physlib states it with a classical `DecidableEq n` and with the
ring structure of `ℂ` obtained through `RCLike`, so its `unitaryGroup d ℂ` is a different (equal, but not
syntactically equal) type from the one your `U : 𝐔[d]` lives in. `rw [traceNorm_unitary_conj]` fails
("did not find an occurrence") and `simp` makes no progress. Rebuild `U` there:
`(U := ⟨U.val, by convert U.2 <;> rfl⟩)` (R20). Placeholders: `(V : 𝐔[d]) (A : Matrix d d ℂ)`.

The goal `⊢ G` is unchanged; the context gains (copied from the infoview; the `⋯` is the membership proof)

```text
this : (↑⟨↑V, ⋯⟩ * A * (↑⟨↑V, ⋯⟩)ᴴ).traceNorm = A.traceNorm
```

R19 then erases the `↑⟨↑V, ⋯⟩`.

**R19 · `simpa using this`** **closes** the goal: it simplifies both `this` and the goal, then closes the
goal with `this`. Here the simplification is `↑⟨a, ha⟩ = a` (taking the value of a subtype element you just
built), which turns R18's `↑⟨↑V, ⋯⟩` into `↑V`; it works the same whether the wrapper sits in the goal (as
in the example, with `this : Q a`) or in `this` (as after R18). Placeholders:
`{α : Type} (p : α → Prop) (a : α) (ha : p a) (Q : α → Prop)`.

| Before | After |
|---|---|
| `this : Q a ⊢ Q ↑⟨a, ha⟩` | closed |

**R20 · `convert h`** changes the **goal list**: it closes the goal with `h` wherever the two agree and
leaves one equation for each place they differ. Placeholders: `(P : ℕ → Prop) (a b : ℕ) (h : P a)`.
Inside R18's `by convert U.2 <;> rfl`, the goal is `↑U ∈ unitaryGroup d ℂ` (the lemma's version) and
`U.2 : ↑U ∈ 𝐔[d]`; the differences left are instance equations such as
`Complex.instRCLike.toCommRing = Complex.commRing`, which `rfl` closes (the `DecidableEq` difference
`convert` closes by itself, since any two `DecidableEq` instances are equal).

| Before | After |
|---|---|
| `h : P a ⊢ P b` | `⊢ b = a` |

**W2: a conjugated sum.** `rw [← Matrix.add_mul, ← Matrix.mul_add]` (the `+` versions of R16, R17) factors
`V`; then the idiom R18 as `have key := …`, `simp only at key` (erases `↑⟨↑V, ⋯⟩`, as R19 does), `rw [key]`,
and R10 finishes:

```lean-goal
⊢ (↑V * A * (↑V)ᴴ + ↑V * B * (↑V)ᴴ).traceNorm ≤ A.traceNorm + B.traceNorm
⊢ (↑V * (A + B) * (↑V)ᴴ).traceNorm ≤ A.traceNorm + B.traceNorm
⊢ (A + B).traceNorm ≤ A.traceNorm + B.traceNorm
```

---

## Traps

- `rw [Matrix.traceNorm_unitary_conj]` and `simp` both fail on your `U` (instance mismatch, R18). Use the
  rebuilt `⟨U.val, by convert U.2 <;> rfl⟩`, ideally once, in a milestone
  `key : ∀ A : Matrix d d ℂ, ((U : Matrix d d ℂ) * A * (U : Matrix d d ℂ)ᴴ).traceNorm = A.traceNorm`
  (a `have` or a helper lemma above the theorem). `convert U.2` alone leaves ring-instance goals: keep `<;> rfl`.
- `linarith` treats `A.traceNorm` as an unknown real: pass `Matrix.traceNorm_nonneg A` when the sign matters (R7).
- `rw [sub_add_sub_cancel]` needs the literal shape `a - b + (b - c)`: choose R10's `A`, `B` as
  `ρ.m - σ.m` and `σ.m - τ.m`, in that order.
- After `simp only [MState.m]`, `ρ.m` is printed `↑↑ρ` (= `ρ.M.mat`). If you name the difference in a
  `have`, write `ρ.M.mat - σ.M.mat` or `ρ.m - σ.m`: both are accepted, they are the same term up to unfolding.
- Factor the right `Uᴴ` first (R16), then the left `U` (R17): `U * A * Uᴴ` is `(U * A) * Uᴴ`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `↔` | `constructor` | R1 |
| equal states from equal matrices | `apply MState.ext_m` | R2 |
| `a = b` → `a - b = 0` | `rw [← sub_eq_zero]` | R3 |
| `A = 0` → `‖A‖₁ = 0` | `rw [← Matrix.traceNorm_zero_iff]` | R4 |
| unfold the distance | `unfold TrDistance` / `unfold TrDistance at h` | R12, R5 |
| `0 ≤ ‖A‖₁` | `Matrix.traceNorm_nonneg A` | R6 |
| linear arithmetic over `ℝ` | `linarith [facts]` | R7 |
| assume `a = b` and substitute | `rintro rfl` | R8 |
| `‖A - A‖₁` → `0` | `simp` (`simp [TrDistance]` for the distance) | R9 |
| triangle inequality | `have := Matrix.traceNorm_add_le A B` | R10 |
| `a - b + (b - c)` → `a - c` | `rw [sub_add_sub_cancel] at this` | R11 |
| matrix of `ρ.uConj U` | `simp only [MState.uConj, MState.m, HermitianMat.conj_apply_mat]` | R13–R15 |
| `M * N - M' * N` → `(M - M') * N` | `rw [← Matrix.sub_mul]` | R16 |
| `M * N - M * N'` → `M * (N - N')` | `rw [← Matrix.mul_sub]` | R17 |
| `‖U A U†‖₁ = ‖A‖₁` | `have := Matrix.traceNorm_unitary_conj (A := A) (U := ⟨U.val, by convert U.2 <;> rfl⟩)` | R18, R20 |
| erase `↑⟨↑U, ⋯⟩` and close | `simpa using this` | R19 |
| see the state | infoview | |
