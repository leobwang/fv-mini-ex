# M149 · The PPT (Peres–Horodecki) criterion: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). M126 (the Hadamard gate) uses some of the same `√`/cast
moves, but nothing here depends on it. **New here:** matrices indexed by pairs, the Kronecker product
`⊗ₖ`, positive semidefinite (PSD) matrices `M.PosSemidef`, the order `≤` on `ℂ`, dot products and
matrix–vector products, `set`, `field_simp`, `linear_combination`.

**The physics.** A two-party state on `ℂᵈ¹ ⊗ ℂᵈ²` is a PSD matrix indexed by pairs `(a, b)`. It is
*separable* if it is a mixture `∑ₖ pₖ ρₖ ⊗ σₖ` with weights `pₖ ≥ 0` and PSD `ρₖ, σₖ`. The *partial
transpose* on the second factor is `(M^{T_B}) (a, b) (c, e) = M (a, e) (c, b)` (swap the second
indices). On a product it gives `ρ ⊗ σᵀ`, which is PSD again; so every separable state has a PSD
partial transpose (PPT). The Bell vector `Φ = (|00⟩ + |11⟩)/√2` fails this: for the singlet
`v = |01⟩ − |10⟩`, `⟨v| (|Φ⟩⟨Φ|)^{T_B} |v⟩ = −1 < 0`. Hence `|Φ⟩⟨Φ|` is not separable (it is entangled).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`refine`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Fintype ι]`
  is a requirement on the type (a *type class*): `[Fintype ι]` says `ι` is finite and lists its
  elements, so `∑ k : ι` makes sense (`Fin m`, `Fin 2 × Fin 2` qualify). `[Mul γ]` says `γ` has a `*`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix (d₁ × d₂) (d₁ × d₂) ℂ` | a complex matrix whose rows and columns are indexed by pairs `(a, b)`: an operator on `ℂᵈ¹ ⊗ ℂᵈ²` |
| `M (a, b) (c, e)` | the entry in row `(a, b)`, column `(c, e)` |
| `p.1`, `p.2`; `(a, b).1` | the first and second component of the pair `p`; `(a, b).1` is `a` (`simp` reduces it) |
| `of f` | `Matrix.of f`: the matrix whose entry `(i, j)` is `f i j` (R2) |
| `kroneckerMap (fun x1 x2 => x1 * x2) A B` | how the infoview prints `A ⊗ₖ B`, the Kronecker (tensor) product: `(A ⊗ₖ B) (a, b) (c, e) = A a c * B b e` (R3) |
| `Mᵀ` | the transpose: `Mᵀ i j = M j i` (R4) |
| `r • M` with `r : ℝ` | the real number `r` times every entry of the complex matrix `M` (R6) |
| `↑r` | the real number `r` cast into `ℂ` (`Complex.ofReal r`) |
| `√x` | `Real.sqrt x`, a real number |
| `∑ k, X k` | the sum over all `k : ι`, i.e. over `Finset.univ` (the finite set of all elements of `ι`) |
| `inst✝⁴ : Fintype d₁` | an unnamed instance argument: the `[Fintype d₁]` bracket of the statement (the superscript only numbers them) |
| `x✝ : k ∈ Finset.univ` | an unnamed hypothesis (Lean writes `✝` for names you cannot refer to); here it is always true and unused |
| `M.PosSemidef` | `M` is positive semidefinite: Hermitian (`Mᴴ = M`) and `0 ≤ star x ⬝ᵥ M *ᵥ x` for every vector `x` |
| `0 ≤ z`, `z ≤ w` for `z w : ℂ` | the partial order from `open scoped ComplexOrder`: `z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im` (R25) |
| `z.re`, `z.im` | the real and imaginary parts of `z : ℂ` |
| `star v` (`v : n → ℂ`) | the entrywise complex conjugate of the vector `v` (R19) |
| `(starRingEnd ℂ) z` | Lean's name for the complex conjugate `conj z` |
| `v ⬝ᵥ w` | the dot product `∑ i, v i * w i`, **without** conjugation (R16) |
| `M *ᵥ v` | the matrix `M` times the column vector `v` (R17) |
| `star v ⬝ᵥ M *ᵥ v` | parsed as `star v ⬝ᵥ (M *ᵥ v)`: the number `⟨v\|M\|v⟩` |
| `vecMulVec w u` | the outer product, entry `(i, j)` is `w i * u j`; `vecMulVec v (star v)` is the projector `\|v⟩⟨v\|` (R18) |
| `v : τ := e` in the context | a local definition made by `set` (R12): `v` stands for `e` |
| `¬A` | `A → False` |
| `case refine_1` | the label of the first goal left by `refine` |

---

## Part 1 · `ptB_sep`

Statement: for weights `p k ≥ 0` and PSD matrices `ρ k`, `σ k`, the partial transpose of the separable
state `∑ k, p k • (ρ k ⊗ₖ σ k)` is PSD.

Plan: first prove the **milestone** `ptB (ρ ⊗ₖ σ) = ρ ⊗ₖ σᵀ` as a helper lemma (R1, then `simp [ptB]`,
which uses R2–R4). Then show `ptB` is linear (R1, `simp` with R5, R6), and build PSD from the pieces
(R7–R10).

### Matrices indexed by pairs

**R1 · `ext ⟨a, b⟩ ⟨c, e⟩`** changes the **goal and the context**. It uses `Matrix.ext` (two matrices are
equal when every entry is) and splits each pair index into its components. `ext i j` (no patterns) also
works; the entries then carry `i.1`, `i.2`. Placeholders: `{α β γ : Type} (M N : Matrix (α × β) (α × β) γ)`.

| Before | After |
|---|---|
| `⊢ M = N` | `a : α, b : β, c : α, e : β ⊢ M (a, b) (c, e) = N (a, b) (c, e)` |

**R2 · `Matrix.of_apply`** changes the **goal**. The lemma is `of f i j = f i j`: an entry of a matrix
built from a function is that function's value. A definition written `Matrix.of fun p q => …` (such as
`ptB`) unfolds this way after `simp [name]`. Placeholders: `{m n α : Type} (f : m → n → α) (i : m) (j : n)`,
and for pair indices `(g : α × β → α × β → γ)`.

| Before | After |
|---|---|
| `⊢ P (of f i j)` | `⊢ P (f i j)` |
| `⊢ P (of (fun p q => g (q.1, p.2) (p.1, q.2)) (a, b) (c, e))` | `⊢ P (g ((c, e).1, (a, b).2) ((a, b).1, (c, e).2))` |

The projections `(c, e).1` are left behind by `rw`; `simp` reduces them to `c`.

**R3 · `Matrix.kronecker_apply`** changes the **goal**. The lemma is
`(A ⊗ₖ B) (a, b) (c, e) = A a c * B b e`. Placeholders: `{α β γ : Type} [Mul γ] (A : Matrix α α γ)
(B : Matrix β β γ) (a c : α) (b e : β)`. `simp` applies it by itself.

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A B (a, b) (c, e))` | `⊢ P (A a c * B b e)` |

**R4 · `Matrix.transpose_apply`** changes the **goal**. The lemma is `Mᵀ i j = M j i`. Placeholders:
`{n α : Type} (M : Matrix n n α) (i j : n)`. `simp` applies it by itself.

| Before | After |
|---|---|
| `⊢ P (Mᵀ i j)` | `⊢ P (M j i)` |

**R5 · `Matrix.sum_apply`** changes the **goal**: the entry of a sum of matrices is the sum of the entries,
`(∑ c ∈ s, g c) i j = ∑ c ∈ s, g c i j`. Placeholders: `{ι n : Type} [Fintype ι] (X : ι → Matrix n n ℂ)
(i j : n)`. `simp` does **not** use it unless you name it: `simp [ptB, Matrix.sum_apply]`.

| Before | After |
|---|---|
| `⊢ P ((∑ k, X k) i j)` | `⊢ P (∑ c, X c i j)` |

**R6 · `Matrix.smul_apply`, then `Complex.real_smul`** change the **goal**. `(r • M) i j = r • M i j`, and for
`r : ℝ`, `z : ℂ`: `r • z = ↑r * z`. Placeholders: `(r : ℝ) (M : Matrix n n ℂ) (i j : n)`. `simp` applies both.

| Before | After `rw [Matrix.smul_apply]` | After `rw [Complex.real_smul]` |
|---|---|---|
| `⊢ P ((r • M) i j)` | `⊢ P (r • M i j)` | `⊢ P (↑r * M i j)` |

### Building PSD matrices

Never unfold `PosSemidef` (see Traps). Build it with these four lemmas; each one, used with `refine … ?_`,
replaces the goal by the PSD facts it needs.

**R7 · `refine Matrix.posSemidef_sum _ fun k _ => ?_`** changes the **goal list and the context**. The lemma
is `Matrix.posSemidef_sum (s) : (∀ i ∈ s, (x i).PosSemidef) → (∑ i ∈ s, x i).PosSemidef`; the `_` is
`s = Finset.univ`. Placeholders: `{ι n : Type} [Fintype ι] (X : ι → Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ (∑ k, X k).PosSemidef` | `k : ι, x✝ : k ∈ Finset.univ ⊢ (X k).PosSemidef` |

**R8 · `Matrix.PosSemidef.smul`** changes the **goal**. The lemma is
`X.PosSemidef → 0 ≤ r → (r • X).PosSemidef`, here with a real `r` and a complex `X`. Placeholders:
`(r : ℝ) (X : Matrix n n ℂ) (hr : 0 ≤ r)`. As a term: `hX.smul hr`.

| Before | After `refine Matrix.PosSemidef.smul ?_ hr` |
|---|---|
| `⊢ (r • X).PosSemidef` | `⊢ X.PosSemidef` |

**R9 · `Matrix.PosSemidef.kronecker`** changes the **goal list**. The lemma is
`A.PosSemidef → B.PosSemidef → (A ⊗ₖ B).PosSemidef` (`ρ ⊗ σ ⪰ 0` when both are). Placeholders:
`{m n : Type} [Fintype m] [Fintype n] (A : Matrix m m ℂ) (B : Matrix n n ℂ)`. As a term: `hA.kronecker hB`.

| Before | After `refine Matrix.PosSemidef.kronecker ?_ ?_` |
|---|---|
| `⊢ (kroneckerMap (fun x1 x2 => x1 * x2) A B).PosSemidef` | `⊢ A.PosSemidef`, `⊢ B.PosSemidef` |

**R10 · `Matrix.PosSemidef.transpose`** changes the **goal**. The lemma is `M.PosSemidef → Mᵀ.PosSemidef`.
Placeholders: `(M : Matrix n n ℂ)`. As a term: `hM.transpose`.

| Before | After `refine Matrix.PosSemidef.transpose ?_` |
|---|---|
| `⊢ Mᵀ.PosSemidef` | `⊢ M.PosSemidef` |

R8–R10 chain as one term, read inside out: `(hA.transpose.kronecker hB).smul hr` proves
`(r • (Aᵀ ⊗ₖ B)).PosSemidef` (W3). `x.f y` is `Matrix.PosSemidef.f x y`: dot notation on a proof `x` of
`PosSemidef`.

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1.** `(A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ`: R1 gives one entry, `simp only [Matrix.transpose_apply,
Matrix.kronecker_apply]` (R4, R3) closes it. The entry goal after R1:

```lean-goal
⊢ (kroneckerMap (fun x1 x2 => x1 * x2) A B)ᵀ (a, b) (c, e) = kroneckerMap (fun x1 x2 => x1 * x2) Aᵀ Bᵀ (a, b) (c, e)
```

**W2.** The transpose is linear: `(∑ k, p k • X k)ᵀ = ∑ k, p k • (X k)ᵀ`. `ext a b` (R1) gives

```lean-goal
⊢ (∑ k, p k • X k)ᵀ a b = (∑ k, p k • (X k)ᵀ) a b
```

and `simp [Matrix.sum_apply]` (R5; it applies R4 and R6 itself) closes it. `ptB` is linear the same way.

**W3.** A mixture with the *first* factor transposed and one fixed `B` is PSD: R7, then
`((hA k).transpose.kronecker hB).smul (hp k)` (R8 ∘ R9 ∘ R10 as one term).

| Before | After R7 |
|---|---|
| `⊢ (∑ k, p k • kroneckerMap (fun x1 x2 => x1 * x2) (A k)ᵀ B).PosSemidef` | `k : ι ⊢ (p k • kroneckerMap (fun x1 x2 => x1 * x2) (A k)ᵀ B).PosSemidef` |

---

## Part 2 · `bell_npt`

Statement: the partial transpose of the Bell projector `|Φ⟩⟨Φ|` (`vecMulVec bell (star bell)`) is **not**
PSD. Plan: assume it is (R11), pick the singlet as test vector (R12), get `0 ≤ ⟨v|…|v⟩` (R13), compute that
number to be `-1` (R14–R23), and derive `False` (R24–R26).

### Assuming the opposite, choosing the test vector

**R11 · `intro h` on `¬A`** changes the **goal and the context**: `¬A` is `A → False`, so `intro` assumes
`A`. Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬A` | `h : A ⊢ False` |

**R12 · `set v : τ := e`** changes the **context** (and the goal): it adds the local definition `v`, and
replaces `e` by `v` wherever it occurs. `simp [v]` later unfolds it. Placeholders:
`(f : (Fin 2 → ℂ) → Prop)`.

| Before | After |
|---|---|
| `⊢ f fun i => if i = 0 then 1 else 0` | `v : Fin 2 → ℂ := fun i => if i = 0 then 1 else 0 ⊢ f v` |

**R13 · `have h1 := hM.dotProduct_mulVec_nonneg v`** changes the **context**. The lemma is
`Matrix.PosSemidef.dotProduct_mulVec_nonneg : M.PosSemidef → ∀ x, 0 ≤ star x ⬝ᵥ M *ᵥ x`. Placeholders:
`{n : Type} [Fintype n] (M : Matrix n n ℂ) (hM : M.PosSemidef) (v : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ False` | `h1 : 0 ≤ star v ⬝ᵥ M *ᵥ v ⊢ False` |

### The √2 fact

`bell` holds `(↑√2)⁻¹`, a real square root cast into `ℂ`. Prove `h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2`
once with R14, R15, then `simp` (it closes `↑2 = 2`; `norm_num` also does).

**R14 · `rw [← Complex.ofReal_pow]`** changes the **goal**. The lemma is `↑(x ^ n) = ↑x ^ n`; right to left
it moves `^` inside the cast. Placeholders: `(x : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (↑x ^ n)` | `⊢ P ↑(x ^ n)` |

**R15 · `rw [Real.sq_sqrt hx]`** changes the **goal**. The lemma is `0 ≤ x → √x ^ 2 = x`. Placeholders:
`(x : ℝ) (hx : 0 ≤ x)`; write `Real.sq_sqrt (by norm_num)` for a numeral.

| Before | After |
|---|---|
| `⊢ P (√x ^ 2)` | `⊢ P x` |

The whole chain on `√3` (W4, `sqrt3_sq`):

```lean-goal
⊢ ↑√3 ^ 2 = 3
⊢ ↑(√3 ^ 2) = 3
⊢ ↑3 = 3
```

### Computing `⟨v| M |v⟩`

One `simp` call with the names of your definitions (`v`, `ptB`, `bell`) and R16–R18, R20, R21 turns the
quadratic form into arithmetic in `(↑√2)⁻¹`; it applies R2, R19 and evaluates every `if` on concrete
indices by itself. In the exercise it leaves `-(s * s) + -(s * s) = -1` with `s = (↑√2)⁻¹`; R22 turns
that into `-1 + -1 = -↑√2 ^ 2` (compare W4's last line), and R23 with `h2` closes it.

**R16 · `dotProduct`** (unfold with `simp only [dotProduct]`) changes the **goal**: `v ⬝ᵥ w` becomes
`∑ i, v i * w i`. Placeholders: `{n : Type} [Fintype n] (v w : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ w)` | `⊢ P (∑ i, v i * w i)` |

**R17 · `Matrix.mulVec`** (unfold) changes the **goal**: entry `i` of `M *ᵥ v` is row `i` of `M` dotted
with `v`. Placeholders: `(M : Matrix n n ℂ) (v : n → ℂ) (i : n)`.

| Before | After `simp only [Matrix.mulVec]` | After `simp only [dotProduct]` |
|---|---|---|
| `⊢ P ((M *ᵥ v) i)` | `⊢ P ((fun j => M i j) ⬝ᵥ v)` | `⊢ P (∑ x, M i x * v x)` |

**R18 · `Matrix.vecMulVec`** (unfold) changes the **goal**: `vecMulVec w u = of fun x y => w x * u y`,
then R2 gives the entry. Placeholders: `(w u : n → ℂ) (i j : n)`.

| Before | After `simp only [Matrix.vecMulVec]` | After `simp only [Matrix.of_apply]` |
|---|---|---|
| `⊢ P (vecMulVec w u i j)` | `⊢ P (of (fun x y => w x * u y) i j)` | `⊢ P (w i * u j)` |

**R19 · `Pi.star_apply`, then `Complex.star_def`** change the **goal**: `star` of a vector is taken entry
by entry, and on `ℂ` it is the conjugate. `simp` applies both, and then `Complex.conj_ofReal`
(`conj ↑r = ↑r`), so the conjugate of `(↑√2)⁻¹` disappears. Placeholders: `(v : n → ℂ) (i : n)`.

| Before | After `rw [Pi.star_apply]` | After `rw [Complex.star_def]` |
|---|---|---|
| `⊢ P (star v i)` | `⊢ P (star (v i))` | `⊢ P ((starRingEnd ℂ) (v i))` |

**R20 · `Fintype.sum_prod_type`** changes the **goal**: a sum over pairs becomes a double sum,
`∑ x, f x = ∑ a, ∑ b, f (a, b)`. Placeholders: `{α β γ : Type} [Fintype α] [Fintype β] [AddCommMonoid γ]
(f : α × β → γ)` (`γ` has `+` and `0`; `ℂ` qualifies).

| Before | After |
|---|---|
| `⊢ P (∑ x, f x)` | `⊢ P (∑ x, ∑ y, f (x, y))` |

**R21 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms. Placeholders:
`{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R22 · `field_simp`** changes the **goal**: it multiplies out every `⁻¹` and `/`, leaving an equation
without fractions. It needs each denominator `≠ 0`: it takes `ha : a ≠ 0` from the context, and proves it
itself for `↑√2` and `↑√3`. Placeholders: `(a : ℂ) (ha : a ≠ 0)`.

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ a⁻¹ * a⁻¹ = 1 / 3` | `⊢ 3 = a ^ 2` |

**R23 · `linear_combination e`** **closes** an equation `L = R` when `L - R - (e.lhs - e.rhs)` is `0` by
`ring`. So it proves `L = R` from a fact `e` up to ring arithmetic; scale with `linear_combination -e` or
`2 * e`. Example: `h : x ^ 2 = 3` proves `x ^ 2 + 1 = 4`, because
`(x ^ 2 + 1 - 4) - (x ^ 2 - 3) = 0`. Placeholders: `(x : ℂ)`.

**W4: the computation on other objects.** `w = |00⟩/√3`, `u = |00⟩ + |11⟩`, so
`⟨u| (−|w⟩⟨w|) |u⟩ = −|⟨w|u⟩|² = −1/3`. `simp [u, w, dotProduct, Matrix.mulVec, Matrix.vecMulVec,
Fintype.sum_prod_type, Fin.sum_univ_two]`, then R22, then `linear_combination sqrt3_sq` (R23):

```lean-goal
⊢ star u ⬝ᵥ -vecMulVec w (star w) *ᵥ u = -1 / 3
⊢ -((↑√3)⁻¹ * (↑√3)⁻¹) = -1 / 3
⊢ -3 = -↑√3 ^ 2
```

### From `0 ≤ -1` to `False`

**R24 · `rw [hv] at h1`** changes the **context**: it rewrites inside the hypothesis `h1`, not the goal.
Placeholders: `(c d : ℂ) (hv : c = d)`.

| Before | After |
|---|---|
| `h1 : 0 ≤ c ⊢ False` | `h1 : 0 ≤ d ⊢ False` |

**R25 · `rw [Complex.nonneg_iff] at h1`** changes the **context**. The lemma is
`0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im` (the meaning of `≤` on `ℂ`). Placeholders: `{z : ℂ}`, here `z = -1`.

| Before | After |
|---|---|
| `h1 : 0 ≤ -1 ⊢ False` | `h1 : 0 ≤ (-1).re ∧ 0 = (-1).im ⊢ False` |

**R26 · `norm_num at h1`** changes the **goal list**: it computes `(-1).re = -1`, sees `0 ≤ -1` is false,
so `h1 : False`, and closes the goal. `norm_num [Complex.nonneg_iff] at h1` does R25 and R26 in one step
when the number is `-1` (see Traps for `-1 / 3`).

| Before | After |
|---|---|
| `h1 : 0 ≤ (-1).re ∧ 0 = (-1).im ⊢ False` | no goals |

**W5: `-(|w⟩⟨w|)` is not PSD** (R11, R13 with test vector `u`, then `rw [quad_w] at h1` (R24), R25, R26):

| After R13 | After R24 | After R25 |
|---|---|---|
| `h1 : 0 ≤ star u ⬝ᵥ -vecMulVec w (star w) *ᵥ u ⊢ False` | `h1 : 0 ≤ -1 / 3 ⊢ False` | `h1 : 0 ≤ (-1 / 3).re ∧ 0 = (-1 / 3).im ⊢ False` |

---

## Part 3 · `bell_entangled`

Statement: there is no separable decomposition `|Φ⟩⟨Φ| = ∑ k, p k • (ρ k ⊗ₖ σ k)` with `p k ≥ 0` and PSD
`ρ k`, `σ k` (`k : Fin m`). Plan: unpack a hypothetical decomposition (R27), feed it to `ptB_sep`, move the
result to the Bell matrix with the equation (R28), and contradict `bell_npt` (R29).

**R27 · `rintro ⟨x, ha, hb⟩` on `¬ ∃ x, A x ∧ B x`** changes the **goal and the context**: it assumes the
statement and takes it apart in one step, one name per `∃` witness and per `∧` part. Placeholders:
`{α : Type} (A B : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ¬∃ x, A x ∧ B x` | `x : α, ha : A x, hb : B x ⊢ False` |

**R28 · `h ▸ e`** is a term: from `h : a = b` and `e : P b` it builds `P a`, rewriting the type of `e`
with `h` until it matches the expected type. Placeholders: `{α : Type} (P : α → Prop) (a b : α)`.

| Before | After `exact h ▸ e` |
|---|---|
| `h : a = b, e : P b ⊢ P a` | no goals |

**R29 · `exact hn e`** **closes** `False` from `hn : ¬A` and `e : A`: a proof of `¬A` is a function from
proofs of `A` to `False`. Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `hn : ¬A, e : A ⊢ False` | no goals |

---

## Traps

- **Do not unfold `PosSemidef`.** Mathlib states its quadratic-form condition over finitely supported
  vectors (`n →₀ ℂ`, `Finsupp`), not plain functions `n → ℂ`. To *use* PSD, apply R13; to *prove* PSD,
  build it with R7–R10.
- `norm_num [Complex.nonneg_iff] at h1` closes `h1 : 0 ≤ -1`, but on `h1 : 0 ≤ -1 / 3` it first rewrites to
  `1 / 3 ≤ 0`, which `Complex.nonneg_iff` no longer matches, and gets stuck. Do `rw [Complex.nonneg_iff] at h1`
  (R25) first, then `norm_num at h1` (R26).
- `⊗ₖ` needs `open scoped Kronecker`; `≤` on `ℂ` and `PosSemidef` over `ℂ` need `open scoped ComplexOrder`.
  `problem.lean` opens both; a helper lemma inside the file sees them.
- The milestone `ptB (ρ ⊗ₖ σ) = ρ ⊗ₖ σᵀ` is your own helper lemma: put it outside the spec regions, after
  `ptB` and before `ptB_sep`, and `rw [your_lemma]` with it. A `have` inside `ptB_sep` also works.
- `simp [ptB]` alone does not split the entry of a sum: name `Matrix.sum_apply` (R5).
- `v ⬝ᵥ w` does not conjugate. The conjugate in `⟨v|M|v⟩` comes from `star v` (R19).
- `star v ⬝ᵥ M *ᵥ v` is `star v ⬝ᵥ (M *ᵥ v)`; write the parentheses in your own `have` to be safe.
- In `refine Matrix.posSemidef_sum _ fun k _ => ?_`, the second `_` names the unused hypothesis
  `k ∈ Finset.univ`; it shows as `x✝`.
- Write cast types out in a `have`: `((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2`. A bare `√2 ^ 2` stays in `ℝ` and does
  not match the goal's `↑√2`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| matrix equation over pair indices → one entry | `ext ⟨a, b⟩ ⟨c, e⟩` (or `ext a b`) | R1 |
| evaluate `of`, `⊗ₖ`, `ᵀ`, `r •` entries | `simp [ptB]` | R2–R4, R6 |
| entry of a sum of matrices | `simp [ptB, Matrix.sum_apply]` | R5 |
| PSD of `∑ k, X k` | `refine Matrix.posSemidef_sum _ fun k _ => ?_` | R7 |
| PSD of `r • (A ⊗ₖ Bᵀ)` | `exact (hA.kronecker hB.transpose).smul hr` | R8–R10 |
| prove `¬A` | `intro h` | R11 |
| name a test vector | `set v : n → ℂ := …` | R12 |
| use PSD on a vector | `have h1 := h.dotProduct_mulVec_nonneg v` | R13 |
| `(↑√x) ^ 2 = x` | `rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp` | R14, R15 |
| expand `⟨v\|M\|v⟩` on `Fin 2 × Fin 2` | `simp [v, defs, dotProduct, Matrix.mulVec, Matrix.vecMulVec, Fintype.sum_prod_type, Fin.sum_univ_two]` | R16–R21 |
| clear `⁻¹` and `/` | `field_simp` | R22 |
| close an equation from a fact up to ring arithmetic | `linear_combination h2` | R23 |
| rewrite a hypothesis | `rw [hv] at h1` | R24 |
| `0 ≤ z` on `ℂ` → real and imaginary parts | `rw [Complex.nonneg_iff] at h1` | R25 |
| a false numeric hypothesis closes the goal | `norm_num at h1` | R26 |
| prove `¬ ∃ …` | `rintro ⟨m, p, …, h⟩` | R27 |
| move a proof along an equation | `h ▸ e` | R28 |
| `False` from `¬A` and `A` | `exact hn e` | R29 |
| see the state | infoview | |
