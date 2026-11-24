# M129 · GHZ: Mermin's operator identity: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), and from M126: 2×2 matrices `Matrix (Fin 2) (Fin 2) ℂ`,
literals `!![a, b; c, d]`, `ext i j` with `fin_cases`, `simp [names]`. **New here:** Mathlib's Kronecker
product `⊗ₖ`, matrix–vector product `*ᵥ`, scalar multiplication `•` of matrices and vectors, and
cancelling a nonzero vector.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` (or `Q` for a hypothesis) is "the rest of your goal" (`P : α → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommRing α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it. In the infoview an
  unnamed bracket shows up as `inst✝ : CommRing α`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix (Fin 2) (Fin 2) ℂ` | 2×2 complex matrices; rows and columns are indexed by `Fin 2 = {0, 1}` (M126) |
| `!![a, b; c, d]` | the literal matrix with rows `a b` and `c d` (M126) |
| `M i j` | the entry in row `i`, column `j`, counted from 0 |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases` (W1) |
| `Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ` | an 8×8 complex matrix whose rows and columns are indexed by triples `(i₁, i₂, i₃)`, one bit per qubit |
| `A ⊗ₖ B` | the Kronecker (tensor) product: `(A ⊗ₖ B) (i, k) (j, l) = A i j * B k l`. Needs `open scoped Kronecker` |
| `kroneckerMap (fun x1 x2 => x1 * x2) A B` | how the infoview prints `A ⊗ₖ B` |
| `P3 P Q R` | the problem's three-qubit Pauli string `P ⊗ₖ (Q ⊗ₖ R)` |
| `r • M`, `r • v` | scalar `r` times every entry of the matrix `M` / vector `v` |
| `-1 • X` | `(-1 : ℂ) • X`; Lean does not print the type ascription |
| `(· *ᵥ v)` | the function `fun M => M *ᵥ v` (written in the skeleton; the infoview shows it applied, R7) |
| `M *ᵥ v` | `Matrix.mulVec`: the matrix `M` applied to the column vector `v`, `(M *ᵥ v) i = ∑ j, M i j * v j` |
| `v : Fin 2 × Fin 2 × Fin 2 → ℂ` | a vector in `ℂ⁸`, written as a function from indices to entries |
| `M *ᵥ N *ᵥ v` | `M *ᵥ (N *ᵥ v)`: `*ᵥ` and `•` group to the right, at the same precedence |
| `c • M *ᵥ v` | `c • (M *ᵥ v)` |
| `-A *ᵥ v` | `(-A) *ᵥ v`: the prefix `-` binds tighter (R11) |
| `I` | `Complex.I`, the imaginary unit (from `open Complex`) |
| `v ≠ 0` | `¬(v = 0)`, with `0` the zero vector |
| `case inl`, `case inr` | the two goals after splitting `A ∨ B`: left side, right side (R16) |

---

## Part 1 · `mermin_identity`

Statement: `P3 X Y Y * P3 Y X Y * P3 Y Y X = -P3 X X X`, an equation between 8×8 matrices. The
mixed-product rule `(A ⊗ B)(A' ⊗ B') = (AA') ⊗ (BB')` reduces it to three 2×2 products, one per qubit:
`X·Y·Y = X`, `Y·X·Y = -X`, `Y·Y·X = X`. Never compute an 8×8 matrix.

### One-qubit products

**R1 · `simp` on literal matrices** changes the **goal**: a product of two literal 2×2 matrices becomes one
literal matrix (row times column, entry by entry). Pass the names of your definitions (`simp [X, Y]`) so
they unfold to literals first. Placeholders: `{α : Type} [CommRing α] (a b c d p q r s : α)`; `ℂ` qualifies.

| Before | After |
|---|---|
| `⊢ P (!![a, b; c, d] * !![p, q; r, s])` | `⊢ P !![a * p + b * r, a * q + b * s; c * p + d * r, c * q + d * s]` |

If `simp [names]` ever stops on a matrix equation without closing it (a scalar `•` on one side is the usual
suspect), go entry by entry first: `ext i j; fin_cases i <;> fin_cases j <;> simp [names]` (TACTIC_STATES, "Extensionality"; W1).

### Kronecker products

**R2 · `simp only [D]`** changes the **goal**: a definition built from `⊗ₖ` is replaced by its body, which the
infoview prints with `kroneckerMap`. Placeholders: `(A B : Matrix (Fin 2) (Fin 2) ℂ)`, with
`D A B := A ⊗ₖ B` defined in the guide.

| Before | After |
|---|---|
| `⊢ P (D A B)` | `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A B)` |

**R3 · `rw [← Matrix.mul_kronecker_mul]`** changes the **goal**. The lemma is the mixed-product rule
`(A * B) ⊗ₖ (A' * B') = A ⊗ₖ A' * B ⊗ₖ B'`; right to left it merges a product of two Kronecker products.
Placeholders: `{α m n : Type} [CommSemiring α] [Fintype m] [Fintype n]` (α has commutative `+`, `*`, as `ℂ`
does; `m`, `n` are finite index types such as `Fin 2` or `Fin 2 × Fin 2`), `(A B : Matrix m m α)
(A' B' : Matrix n n α)`. Use `simp only [← Matrix.mul_kronecker_mul]` to repeat it: a triple product needs
it twice at the top and again inside the nested `⊗ₖ` (W2).

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A A' * kroneckerMap (fun x1 x2 => x1 * x2) B B')` | `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) (A * B) (A' * B'))` |

**R4 · `rw [Matrix.smul_kronecker]`** changes the **goal**. The lemma is `(r • A) ⊗ₖ B = r • (A ⊗ₖ B)`: a
scalar on the left factor moves outside. Placeholders: `{α m n : Type} [CommRing α] (r : α)
(A : Matrix m m α) (B : Matrix n n α)`.

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) (r • A) B)` | `⊢ P (r • kroneckerMap (fun x1 x2 => x1 * x2) A B)` |

**R5 · `rw [Matrix.kronecker_smul]`** changes the **goal**. The lemma is `A ⊗ₖ (r • B) = r • (A ⊗ₖ B)`: the
same for the right factor. Placeholders as in R4.

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A (r • B))` | `⊢ P (r • kroneckerMap (fun x1 x2 => x1 * x2) A B)` |

**R6 · `rw [neg_one_smul]`** changes the **goal**. The lemma is `(-1 : R) • x = -x`. Placeholders:
`{R M : Type} [Ring R] [AddCommGroup M] [Module R M] (x : M)`: `M` is a vector space (module) over `R`;
complex matrices and complex vectors over `R = ℂ` qualify.

| Before | After |
|---|---|
| `⊢ P (-1 • x)` | `⊢ P (-x)` |

### Worked combinations (W1–W2, on `Z = !![1, 0; 0, -1]`, `A = !![0, 2; 3, 0]`, `D A B = A ⊗ₖ B`)

**W1.** `Z * Z * Z = Z` is `simp [Z]` (R1). `Z * A * Z = (-1 : ℂ) • A` goes entry by entry: after `ext i j`
and `fin_cases`, the four goals look like

```lean-goal
⊢ (Z * A * Z) ((fun i => i) ⟨0, ⋯⟩) ((fun i => i) ⟨1, ⋯⟩) = (-1 • A) ((fun i => i) ⟨0, ⋯⟩) ((fun i => i) ⟨1, ⋯⟩)
```

and `simp [Z, A]` closes them.

**W2: a two-qubit mixed product** `D Z Z * D A Z * D Z Z = -D A Z`, with the one-qubit facts `hZAZ`, `hZZZ`
from W1 in the context. `simp only [D]` (R2), `simp only [← Matrix.mul_kronecker_mul]` (R3), `rw [hZAZ, hZZZ]`,
`rw [Matrix.smul_kronecker]` (R4), then `rw [neg_one_smul]` (R6) closes it:

```lean-goal
⊢ D Z Z * D A Z * D Z Z = -D A Z
⊢ kroneckerMap (fun x1 x2 => x1 * x2) Z Z * kroneckerMap (fun x1 x2 => x1 * x2) A Z * kroneckerMap (fun x1 x2 => x1 * x2) Z Z = -kroneckerMap (fun x1 x2 => x1 * x2) A Z
⊢ kroneckerMap (fun x1 x2 => x1 * x2) (Z * A * Z) (Z * Z * Z) = -kroneckerMap (fun x1 x2 => x1 * x2) A Z
⊢ kroneckerMap (fun x1 x2 => x1 * x2) (-1 • A) Z = -kroneckerMap (fun x1 x2 => x1 * x2) A Z
⊢ -1 • kroneckerMap (fun x1 x2 => x1 * x2) A Z = -kroneckerMap (fun x1 x2 => x1 * x2) A Z
```

In the exercise the sign sits in the middle qubit, inside the nested `⊗ₖ`: pull it out of the inner product
first (R4), then out of the outer one (R5), then R6.

---

## Part 2 · `mermin_eigen`

Statement: `v ≠ 0` is a common eigenvector of the four strings, `P3 X Y Y *ᵥ v = a • v`, `P3 Y X Y *ᵥ v = b • v`,
`P3 Y Y X *ᵥ v = c • v`, `P3 X X X *ᵥ v = e • v`; prove `e = -(a * b * c)`. Physics: a local hidden-variable
model assigns each qubit fixed values `x_k, y_k ∈ {±1}` for its `X` and `Y` measurements, so
`a·b·c = (x₁y₂y₃)(y₁x₂y₃)(y₁y₂x₃) = x₁x₂x₃ · (y₁y₂y₃)² = e`. Quantum mechanics gives `e = -abc`: the GHZ
contradiction, with no inequality needed.

The route: apply the identity of Part 1 to `v` (R7), take the products apart and substitute the eigen
equations (R8–R11) until `h : (c * (b * a)) • v = -(e • v)`, then cancel `v` (R12–R18).

### Matrices acting on a vector

**R7 · `have h := congrArg f e`** changes the **context**: from `e : A = B` it adds `h : f A = f B`. With
`f = (· *ᵥ v)`, which is `fun M => M *ᵥ v`, Lean shows `h` already beta-reduced. Placeholders:
`{α n : Type} [CommRing α] [Fintype n] (A B : Matrix n n α) (v : n → α) (e : A = B)`. The `e` can be a
theorem you proved earlier, applied by name.

| Before | After |
|---|---|
| `⊢ G` | `h : A *ᵥ v = B *ᵥ v ⊢ G` |

**R8 · `rw [← Matrix.mulVec_mulVec] at h`** changes the **context**. The lemma is
`M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v`; right to left it applies a product one factor at a time. `at h` rewrites the
hypothesis `h` instead of the goal; every entry below works with `at h` too. Placeholders:
`{α n : Type} [CommRing α] [Fintype n] (M N : Matrix n n α) (v : n → α)`.

| Before | After |
|---|---|
| `h : Q ((M * N) *ᵥ v) ⊢ Q (M *ᵥ N *ᵥ v)` | `h : Q (M *ᵥ N *ᵥ v) ⊢ Q (M *ᵥ N *ᵥ v)` |

After R8, `rw [hc] at h` replaces the innermost `P3 Y Y X *ᵥ v` by `c • v` (TACTIC_STATES, `rw [h]`).

**R9 · `rw [Matrix.mulVec_smul]`** changes the **goal**: `M *ᵥ (b • v) = b • (M *ᵥ v)`, a scalar moves out
past the matrix, so the next eigen equation can match. Placeholders: `(M : Matrix n n α) (b : α) (v : n → α)`
with `[CommRing α] [Fintype n]`.

| Before | After |
|---|---|
| `⊢ P (M *ᵥ b • v)` | `⊢ P (b • M *ᵥ v)` |

**R10 · `rw [smul_smul]`** changes the **goal**: `a • b • x = (a * b) • x`. Placeholders:
`{R M : Type} [Monoid R] [MulAction R M] (a b : R) (x : M)` (`R` has `*`, and `•` respects it; `ℂ` acting on
vectors qualifies).

| Before | After |
|---|---|
| `⊢ P (a • b • x)` | `⊢ P ((a * b) • x)` |

**R11 · `rw [Matrix.neg_mulVec]`** changes the **goal**: `(-A) *ᵥ v = -(A *ᵥ v)`. Needed because the right
side of the identity is `-P3 X X X`, so after R7 it reads `-P3 X X X *ᵥ v`. Placeholders:
`(A : Matrix n n α) (v : n → α)`.

| Before | After |
|---|---|
| `⊢ P (-A *ᵥ v)` | `⊢ P (-(A *ᵥ v))` |

`simp only [l₁, …, lₖ] at h` applies a whole list of these rewrites, in whatever order they match, until
none applies. That is easier than finding the right `rw` order by hand (W3).

**W3: the eigen chain on two operators** `M * N = -K` with `M *ᵥ v = a • v`, `N *ᵥ v = b • v`,
`K *ᵥ v = e • v`, one rewrite at a time. The goal stays `⊢ (a * b) • v = -(e • v)`; `h` changes:

| Step | State |
|---|---|
| `have h := congrArg (· *ᵥ v) hMN` (R7) | `h : (M * N) *ᵥ v = -K *ᵥ v ⊢ (a * b) • v = -(e • v)` |
| `rw [← Matrix.mulVec_mulVec] at h` (R8) | `h : M *ᵥ N *ᵥ v = -K *ᵥ v ⊢ (a * b) • v = -(e • v)` |
| `rw [hn] at h` | `h : M *ᵥ b • v = -K *ᵥ v ⊢ (a * b) • v = -(e • v)` |
| `rw [Matrix.mulVec_smul] at h` (R9) | `h : b • M *ᵥ v = -K *ᵥ v ⊢ (a * b) • v = -(e • v)` |
| `rw [hm] at h` | `h : b • a • v = -K *ᵥ v ⊢ (a * b) • v = -(e • v)` |
| `rw [smul_smul] at h` (R10) | `h : (b * a) • v = -K *ᵥ v ⊢ (a * b) • v = -(e • v)` |
| `rw [Matrix.neg_mulVec] at h` (R11) | `h : (b * a) • v = -(K *ᵥ v) ⊢ (a * b) • v = -(e • v)` |
| `rw [hk] at h` | `h : (b * a) • v = -(e • v) ⊢ (a * b) • v = -(e • v)` |

Note the order of the scalars: the innermost operator acts first, so its eigenvalue ends up on the outside,
`(b * a)`, not `(a * b)`. With three operators you get `(c * (b * a))`.

### Cancelling the vector

**R12 · `rw [add_smul]`** changes the **goal**: `(r + s) • x = r • x + s • x`. Placeholders:
`{R M : Type} [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M)`.

| Before | After |
|---|---|
| `⊢ P ((r + s) • x)` | `⊢ P (r • x + s • x)` |

**R13 · `rw [show t = u by ring]`** changes the **goal**: it proves a ring identity on the spot and rewrites
with it, here to make a product look exactly like the one in `h` (`rw [h]` needs a literal match).
Placeholders: `{α : Type} [CommRing α] (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (a * b)` | `⊢ P (b * a)` |

**R14 · `simp`** **closes** `x + -x = 0` (lemma `add_neg_cancel`) in any `[AddCommGroup M]`, vectors included.

**R15 · `have h := smul_eq_zero.mp h0`** changes the **context**. The lemma is `r • x = 0 ↔ r = 0 ∨ x = 0`
(true for complex scalars on complex vectors: no zero divisors); `.mp` uses the `→` direction. Placeholders:
`{n : Type} (r : ℂ) (x : n → ℂ) (h0 : r • x = 0)`.

| Before | After |
|---|---|
| `⊢ G` | `h : r = 0 ∨ x = 0 ⊢ G` |

**R16 · `rcases h with h1 | h1`** changes the **goal list and the context**: `h : A ∨ B` is replaced by two
goals, one with `h1 : A`, one with `h1 : B`. Work on them with `·`. You can write
`rcases smul_eq_zero.mp h0 with h1 | h1` directly. Placeholders: `(A B G : Prop) (h : A ∨ B)`.

| Before | After |
|---|---|
| `h : A ∨ B ⊢ G` | `h1 : A ⊢ G`, `h1 : B ⊢ G` |

**R17 · `linear_combination h1`** **closes** an equation `x = y` when `x - y` equals `lhs - rhs` of `h1`
(times a constant you may write, `linear_combination 2 * h1`) up to `ring`. Example: from
`h1 : x - y = 0` it proves `x = y`; from `h1 : r + s = 0` it proves `r = -s`.

**R18 · `exact absurd h hn`** **closes** any goal from `h : A` and `hn : ¬A`. Here `A` is `v = 0` and `hn` is
`hv : v ≠ 0`. Placeholders: `(A G : Prop)`.

**W4: cancel a nonzero vector.** From `h : s • x = -(r • x)` and `hx : x ≠ 0`, prove `r = -s`:
`have h0 : (r + s) • x = 0 := by rw [add_smul, h]; simp` (R12, R14), then R15 with R16:

```lean-goal
⊢ r = -s
```

| Branch | State | Close with |
|---|---|---|
| `inl` | `h1 : r + s = 0 ⊢ r = -s` | `linear_combination h1` (R17) |
| `inr` | `h1 : x = 0 ⊢ r = -s` | `exact absurd h1 hx` (R18) |

---

## Traps

- Mathlib has `smul_kronecker` but no `neg_kronecker`: state the sign as `(-1 : ℂ) • X`, not `-X`, so R4–R6
  can move it out of the Kronecker product.
- `*` groups to the left: `P3 X Y Y * P3 Y X Y * P3 Y Y X` is `(… * …) * …`, and each `P3` hides a nested `⊗ₖ`.
  One `rw [← Matrix.mul_kronecker_mul]` is not enough; `simp only [P3, ← Matrix.mul_kronecker_mul]` repeats it.
- `rw` with an eigen equation fails while a scalar sits between the matrix and `v` (`M *ᵥ b • v`): apply R9 first,
  or put everything in one `simp only [...] at h`.
- `-P3 X X X *ᵥ v` is `(-P3 X X X) *ᵥ v`, not `-(… *ᵥ v)`: R11 converts.
- The scalar comes out as `c * (b * a)`, not `a * b * c`: rewrite one into the other with R13 before `rw [h]`.
- `simp only [...] at h` errors if no lemma in the list applies, and warns (linter) about lemmas that never fire.
- `have h : T` with no `:= …` makes `T` your next goal instead of adding `h` (TACTIC_STATES, "Adding facts").

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a one-qubit product | `simp [X, Y]`, or `ext i j; fin_cases i <;> fin_cases j <;> simp [X, Y]` | R1 |
| unfold a Kronecker definition | `simp only [P3]` | R2 |
| product of `⊗ₖ`'s → `⊗ₖ` of products | `simp only [← Matrix.mul_kronecker_mul]` | R3 |
| scalar out of `⊗ₖ` (left / right factor) | `rw [Matrix.smul_kronecker]` / `rw [Matrix.kronecker_smul]` | R4, R5 |
| `-1 • x → -x` | `rw [neg_one_smul]` | R6 |
| apply both sides of `e : A = B` to `v` | `have h := congrArg (· *ᵥ v) e` | R7 |
| `(M * N) *ᵥ v → M *ᵥ (N *ᵥ v)` in `h` | `rw [← Matrix.mulVec_mulVec] at h` | R8 |
| `M *ᵥ (b • v) → b • (M *ᵥ v)` | `Matrix.mulVec_smul` | R9 |
| `a • b • x → (a * b) • x` | `smul_smul` | R10 |
| `(-A) *ᵥ v → -(A *ᵥ v)` | `Matrix.neg_mulVec` | R11 |
| all of the above at once | `simp only [l₁, …, lₖ] at h` | R8–R11 |
| `(r + s) • x → r • x + s • x` | `rw [add_smul]` | R12 |
| reorder a product to match `h` | `rw [show a * b * c = … by ring]` | R13 |
| `x + -x = 0` | `simp` | R14 |
| `r • x = 0` → two cases | `rcases smul_eq_zero.mp h0 with h1 \| h1` | R15, R16 |
| `e = -(…)` from `e + … = 0` | `linear_combination h1` | R17 |
| contradiction `h : A`, `hn : ¬A` | `exact absurd h hn` | R18 |
| see the state | infoview | |
