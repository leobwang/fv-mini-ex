# M143 · Correlations of the maximally entangled state; the 2√2 value: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`have`, `intro`, `rw [h]`, `simp [d]`, `ring`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). The 2×2 matrix tools of M126 help but are re-explained
here. **New here:** physlib's maximally entangled state `Ket.MES`; Mathlib's vectors as functions,
dot product `⬝ᵥ`, matrix–vector product `*ᵥ`, Kronecker product `⊗ₖ`; finite sums `∑` over a product
type and their collapse by `if`; complex conjugation `star`; `field_simp` and `linear_combination`.

The physics. `Φ = (1/√d) Σᵢ |i⟩|i⟩` is a state of two `d`-level systems; its amplitude at the basis pair
`(i, k)` is `1/√d` when `i = k` and `0` otherwise. For matrices `A, B` on one system, the expectation value
`⟨Φ|A ⊗ B|Φ⟩ = Σ_{(i,k),(j,l)} conj Φ(i,k) · A_{ij} B_{kl} · Φ(j,l)`, and the two `Φ` factors force `k = i`,
`l = j`, leaving `(1/d) Σᵢⱼ A_{ij} B_{ij}` (Part 1). The CHSH operator is
`A₀⊗B₀ + A₀⊗B₁ + A₁⊗B₀ − A₁⊗B₁`; a local hidden-variable model keeps its expectation in `[−2, 2]` (M141),
and Part 2 shows `Φ` (for `d = 2`, the Bell state) reaches `2√2`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Fintype ι]` is a
  requirement on the type (a *type class*): `[Fintype ι]` says `ι` is finite, so `∑ i, f i` makes sense
  (`Fin n` and products of finite types qualify); `[DecidableEq ι]` says `i = j` can be decided, so
  `if i = j then … else …` is allowed; `[Nonempty d]` says `d` has an element.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ket.MES d` | physlib's maximally entangled state `Φ = (1/√d) Σᵢ \|i⟩\|i⟩` on `d × d`, a `Ket (d × d)` |
| `(Ket.MES d).vec` | its amplitudes, a function `d × d → ℂ`; `(Ket.MES d).vec (i, j)` is the amplitude at `(i, j)` (R1) |
| `d × d`, `(i, j)` | the product type (pairs) and a pair; `x.1`, `x.2` are its components |
| `inst✝² : Fintype d`, `inst✝¹ : DecidableEq d`, `inst✝ : Nonempty d` | the unnamed type-class assumptions from the `[…]` brackets of the statement; you never use them by name |
| `Matrix d d ℂ` | square matrices indexed by `d`: functions `d → d → ℂ`, so `A i j` is the entry in row `i`, column `j` |
| `Fin 2` | the type `{0, 1}`; `Matrix (Fin 2) (Fin 2) ℂ` is the 2×2 complex matrices |
| `Fintype.card d` | the number of elements of the finite type `d`, a natural number (the dimension) |
| `↑√↑(Fintype.card d)` | `card d : ℕ` cast into `ℝ`, its square root `√` (`Real.sqrt`), cast into `ℂ`. Every `↑` is a cast |
| `↑↑n` vs `↑n` | `n : ℕ` cast into `ℝ` then `ℂ`, vs `n` cast straight into `ℂ`; equal by R6 |
| `x⁻¹` | the inverse `1/x` |
| `v : ι → ℂ` | a vector is just a function from indices to `ℂ` |
| `v ⬝ᵥ w` | dot product `∑ x, v x * w x` (no conjugation) |
| `M *ᵥ v` | matrix times column vector, `(M *ᵥ v) x = ∑ y, M x y * v y` |
| `star v ⬝ᵥ M *ᵥ v` | read `star v ⬝ᵥ (M *ᵥ v)`: the bra-ket `⟨v\|M\|v⟩` |
| `star z`, `(starRingEnd ℂ) z` | the complex conjugate `z̄`; `star v` on a vector conjugates each entry (R10, R16) |
| `A ⊗ₖ B`, printed `kroneckerMap (fun x1 x2 => x1 * x2) A B` | the Kronecker (tensor) product: `(A ⊗ₖ B) (i, k) (j, l) = A i j * B k l` (R9) |
| `∑ x, f x` | the sum over every `x` of a finite type; the same as `∑ x ∈ Finset.univ, f x` |
| `Finset.univ` | the finite set of all elements of a finite type |
| `x_1`, `x_2`, `y`, `y_1`, `i_1` | bound variables of sums, renamed by Lean when it unfolds definitions or splits a sum over pairs (R8) |
| `if c then a else 0` | Lean's `ite`; needs `c` decidable |
| `x✝ : i ∈ Finset.univ` | an unnamed hypothesis (written `_` in `fun i _ => …`), added by R18 |
| `!![a, b; c, d]` | the 2×2 matrix with rows `a b` and `c d`; `M i j` is row `i`, column `j`, from 0 |
| `c • M` | scalar `c` times every entry of `M` |

---

## Part 1 · `mes_expect`

Statement: for any finite nonempty `d` and `A B : Matrix d d ℂ`,
`star (Ket.MES d).vec ⬝ᵥ ((A ⊗ₖ B) *ᵥ (Ket.MES d).vec) = (↑(card d))⁻¹ * ∑ i, ∑ j, A i j * B i j`, i.e.
`⟨Φ|A ⊗ B|Φ⟩ = (1/d) Σᵢⱼ A_{ij} B_{ij}`.

### The two facts to prove first

**R1 · `simp [Ket.MES]`** changes the **goal**: an amplitude of `Φ` becomes an explicit `if`. `simp` unfolds the
definition `vec := fun (i, j) ↦ if i = j then 1 / √(card d) else 0` and writes `1 / x` as `x⁻¹`. Placeholders:
`{d : Type} [Fintype d] [DecidableEq d] [Nonempty d] (i j : d)`. State the fact as
`hΦ : ∀ i j : d, (Ket.MES d).vec (i, j) = if i = j then ((Real.sqrt (Fintype.card d) : ℝ) : ℂ)⁻¹ else 0`
and prove it with `intro i j` then R1.

| Before | After |
|---|---|
| `⊢ P ((Ket.MES d).vec (i, j))` | `⊢ P (if i = j then (↑√↑(Fintype.card d))⁻¹ else 0)` |

**R2 · `rw [← mul_inv]`** changes the **goal**. The lemma is `mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹`, and `←` uses it
right to left. Placeholders: `{α : Type} [DivisionCommMonoid α] (a b : α)` (α has a commutative `*` and `⁻¹`;
`ℂ` and `ℝ` qualify).

| Before | After |
|---|---|
| `⊢ P (a⁻¹ * b⁻¹)` | `⊢ P (a * b)⁻¹` |

**R3 · `rw [← Complex.ofReal_mul]`** changes the **goal**. The lemma is `↑(x * y) = ↑x * ↑y` (cast ℝ → ℂ), and
right to left it moves `*` inside the cast, so a real lemma can apply. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑x * ↑y)` | `⊢ P ↑(x * y)` |

**R4 · `rw [Real.mul_self_sqrt]`** changes the **goal list**. The lemma is `0 ≤ x → √x * √x = x`: the goal is
rewritten and a side goal `0 ≤ x` is added. Here `x = ↑n` with `n : ℕ`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (√↑n * √↑n)` | `⊢ P ↑n`, `⊢ 0 ≤ ↑n` |

**R5 · `Nat.cast_nonneg`** **closes** `⊢ 0 ≤ ↑n`: a natural number cast into `ℝ` is nonnegative. Pass it to R4
directly: `rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]`, and no side goal remains.

| Before | After |
|---|---|
| `⊢ 0 ≤ ↑n` | no goal |

**R6 · `rw [Complex.ofReal_natCast]`** changes the **goal**. The lemma is `↑↑n = ↑n`: casting `n : ℕ` to `ℝ` and
then to `ℂ` is the same as casting it to `ℂ`. `simp` applies it by itself. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑↑n` | `⊢ P ↑n` |

The second fact: `hn : (↑√↑(card d))⁻¹ * (↑√↑(card d))⁻¹ = (↑(card d))⁻¹`, written with full casts
`((Real.sqrt (Fintype.card d) : ℝ) : ℂ)` and `((Fintype.card d : ℂ))`. Proof: R2, R3, R4 with R5, then R6
(or `simp`).

### From `⟨Φ|A ⊗ B|Φ⟩` to sums

**R7 · `simp only [dotProduct, mulVec]`** changes the **goal**: unfolds both products into sums. Placeholders:
`{ι : Type} [Fintype ι] (v w : ι → ℂ) (M : Matrix ι ι ℂ)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ M *ᵥ w)` | `⊢ P (∑ x, v x * ∑ x_1, M x x_1 * w x_1)` |

**R8 · `Fintype.sum_prod_type`** changes the **goal**: a sum over pairs becomes a double sum,
`∑ x, f x = ∑ x, ∑ y, f (x, y)`. Placeholders: `{α β : Type} [Fintype α] [Fintype β] (f : α × β → ℂ)`. In the
exercise both sums (over `(i, k)` and over `(j, l)`) split, giving four sums.

| Before | After |
|---|---|
| `⊢ P (∑ x, f x)` | `⊢ P (∑ x, ∑ y, f (x, y))` |

**R9 · `simp only [kroneckerMap_apply]`** changes the **goal**: an entry of the Kronecker product becomes a
product of entries. Lemma: `kroneckerMap f A B i j = f (A i.1 j.1) (B i.2 j.2)`. Placeholders:
`{α β : Type} (A : Matrix α α ℂ) (B : Matrix β β ℂ) (i j : α) (k l : β)`.

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A B (i, k) (j, l))` | `⊢ P (A i j * B k l)` |

**R10 · `Pi.star_apply`** changes the **goal**: `star x i = star (x i)`; conjugating a vector and then taking
entry `x` is conjugating that entry. Placeholders: `{ι : Type} (v : ι → ℂ) (x : ι)`.

| Before | After |
|---|---|
| `⊢ P (star v x)` | `⊢ P (star (v x))` |

**R11 · `simp only [hf]` with `hf : ∀ i j, …`** changes the **goal**: rewrites every instance of the left side,
including those under `∑` binders. Placeholders: `{α : Type} [Fintype α] (f : α × α → ℂ) (g : α → α → ℂ)`,
`hf : ∀ i j, f (i, j) = g i j`. This is how `hΦ` enters (and, in Part 2, `mes_expect`).

| Before | After |
|---|---|
| `⊢ P (∑ i, ∑ j, f (i, j))` | `⊢ P (∑ x, ∑ x_1, g x x_1)` |

### Pushing `if` outward and collapsing sums

After R7–R11 the goal is a quadruple sum of `star (if …) * ∑ ∑ (A … * B … * if …)`. R12–R14 move every `if`
to the front of its term, then R15 kills one sum per `if`. All of them can go into the same `simp only`.

**R12 · `apply_ite star`, then `star_zero`** change the **goal**. `apply_ite f : f (if c then x else y) =
if c then f x else f y`; `star_zero : star 0 = 0`. Placeholders: `(c : Prop) [Decidable c] (a : ℂ)`.

| Before | After `apply_ite star` | After `star_zero` |
|---|---|---|
| `⊢ P (star (if c then a else 0))` | `⊢ P (if c then star a else star 0)` | `⊢ P (if c then star a else 0)` |

**R13 · `mul_ite`, then `mul_zero`** change the **goal**: a factor on the left moves into both branches.
Placeholders: `(c : Prop) [Decidable c] (a b : ℂ)`.

| Before | After `mul_ite` | After `mul_zero` |
|---|---|---|
| `⊢ P (a * if c then b else 0)` | `⊢ P (if c then a * b else a * 0)` | `⊢ P (if c then a * b else 0)` |

**R14 · `ite_mul`, then `zero_mul`** change the **goal**: the same for a factor on the right.
Placeholders: `(c : Prop) [Decidable c] (a b : ℂ)`.

| Before | After `ite_mul` | After `zero_mul` |
|---|---|---|
| `⊢ P ((if c then a else 0) * b)` | `⊢ P (if c then a * b else 0 * b)` | `⊢ P (if c then a * b else 0)` |

**R15 · `Finset.sum_ite_eq`, `Finset.mem_univ`, `if_true`** change the **goal**: a sum whose terms are `0`
except at `j = i` is its `i`-th term. Lemma: `∑ j ∈ s, (if i = j then f j else 0) = if i ∈ s then f i else 0`;
`Finset.mem_univ i : i ∈ Finset.univ` (simp turns it into `True`); `if_true : (if True then t else e) = t`.
Placeholders: `{ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (f : ι → ℂ)`. For the condition `j = i` (bound
variable on the left) use `Finset.sum_ite_eq'`.

| Before | After `sum_ite_eq` | After `mem_univ` | After `if_true` |
|---|---|---|---|
| `⊢ P (∑ j, if i = j then f j else 0)` | `⊢ P (if i ∈ Finset.univ then f i else 0)` | `⊢ P (if True then f i else 0)` | `⊢ P (f i)` |

**R16 · `Complex.star_def`, `map_inv₀`, `Complex.conj_ofReal`** change the **goal**: the conjugate of a real
amplitude `(↑r)⁻¹` is itself. `Complex.star_def : star = starRingEnd ℂ` (conjugation on `ℂ`);
`map_inv₀ : f a⁻¹ = (f a)⁻¹` for a ring map `f`; `Complex.conj_ofReal : conj ↑r = ↑r`. Placeholders: `(r : ℝ)`.

| Before | After `star_def` | After `map_inv₀` | After `conj_ofReal` |
|---|---|---|---|
| `⊢ P (star (↑r)⁻¹)` | `⊢ P ((starRingEnd ℂ) (↑r)⁻¹)` | `⊢ P ((starRingEnd ℂ) ↑r)⁻¹` | `⊢ P (↑r)⁻¹` |

### Comparing the two sides sum by sum

After R16 the goal is `∑ x, c * ∑ x_1, A x x_1 * B x x_1 * c = (↑(card d))⁻¹ * ∑ i, ∑ j, A i j * B i j` with
`c = (↑√↑(card d))⁻¹`.

**R17 · `rw [Finset.mul_sum]`** changes the **goal**: `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`. Placeholders:
`{ι : Type} [Fintype ι] (a : ℂ) (f : ι → ℂ)`. `rw` rewrites the first match whose pieces mention no bound
variable, so in the exercise it first hits the right-hand side only.

| Before | After |
|---|---|
| `⊢ P (a * ∑ i, f i)` | `⊢ P (∑ i, a * f i)` |

**R18 · `refine Finset.sum_congr rfl fun i _ => ?_`** changes the **goal and the context**: two sums over the same
set are equal if their terms are. Lemma: `s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`; `rfl` proves
`s₁ = s₂`, and `?_` is the new goal for a fresh `i`. Placeholders: `{ι : Type} [Fintype ι] (f g : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ ∑ i, f i = ∑ i, g i` | `i : ι, x✝ : i ∈ Finset.univ ⊢ f i = g i` |

Use R17, R18 for the outer sum, then R17 on both sides and R18 for the inner sum. The last goal is
`c * (A i j * B i j * c) = (↑(card d))⁻¹ * (A i j * B i j)`: `rw [← hn]` turns the right factor into `c * c`,
and `ring` closes it.

---

## Part 2 · `bell_chsh`

Statement: `star Φ ⬝ᵥ (chsh *ᵥ Φ) = 2 * ↑√2` for `Φ = Ket.MES (Fin 2)` (the Bell state) and
`chsh = Z ⊗ₖ B₀ + Z ⊗ₖ B₁ + X ⊗ₖ B₀ - X ⊗ₖ B₁`. Do not expand 4×4 matrices: unfold `chsh` (`simp only [chsh]`),
split by linearity (R19, R20), and use `mes_expect` on each of the four terms (as in R11).

### Linearity

**R19 · `Matrix.add_mulVec`, `Matrix.sub_mulVec`** change the **goal**: `(A + B) *ᵥ x = A *ᵥ x + B *ᵥ x`, and
the same with `-`. Placeholders: `{ι : Type} [Fintype ι] (M N K : Matrix ι ι ℂ) (v : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((M + N - K) *ᵥ v)` | `⊢ P (M *ᵥ v + N *ᵥ v - K *ᵥ v)` |

**R20 · `dotProduct_add`, `dotProduct_sub`** change the **goal**: `u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w`, and the
same with `-`. Placeholders: `{ι : Type} [Fintype ι] (u v w x : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (u ⬝ᵥ (v + w - x))` | `⊢ P (u ⬝ᵥ v + u ⬝ᵥ w - u ⬝ᵥ x)` |

After R19, R20 and `mes_expect`, the goal is a combination of four terms
`(↑(Fintype.card (Fin 2)))⁻¹ * ∑ i, ∑ j, Z i j * B₀ i j` etc., equal to `2 * ↑√2`.

### Facts about `√2`

State `h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2` (proof R21, R22, R23 or `simp`) and
`hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0` (R24, for R29) before the final `field_simp`.

**R21 · `rw [← Complex.ofReal_pow]`** changes the **goal**. The lemma is `↑(x ^ n) = ↑x ^ n`; right to left it
moves `^` inside the cast. Placeholders: `(x : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (↑x ^ n)` | `⊢ P ↑(x ^ n)` |

**R22 · `rw [Real.sq_sqrt hx]`** changes the **goal**. The lemma is `0 ≤ x → √x ^ 2 = x`; with
`hx : 0 ≤ x` given (or `(by norm_num)` for a numeral) no side goal is added. Placeholders: `(x : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `⊢ P (√x ^ 2)` | `⊢ P x` |

**R23 · `rw [Complex.ofReal_ofNat]`** changes the **goal**: a real numeral cast into `ℂ` is the complex numeral.
Lemma: `↑(OfNat.ofNat n) = OfNat.ofNat n` for numerals `n ≥ 2`. `simp` applies it by itself.

| Before | After |
|---|---|
| `⊢ P ↑3` | `⊢ P 3` |

**R24 · `simp`** **closes** `↑√3 ≠ 0` (any positive numeral). It uses `Complex.ofReal_eq_zero : ↑r = 0 ↔ r = 0`
and `Real.sqrt_eq_zero : 0 ≤ x → (√x = 0 ↔ x = 0)` (side condition `0 ≤ 3` by `Nat.ofNat_nonneg`), then
`OfNat.ofNat_ne_zero : 3 ≠ 0`.

### Evaluating 2×2 sums

`simp [Fin.sum_univ_two, B₀, B₁, X, Z]` does R25–R28 in one call and leaves an equation of numbers and
`(↑√2)⁻¹`.

**R25 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms. Naming it makes the
`simp` call independent of which `Fin` sum lemmas `simp` happens to use by default. Placeholders: `{β : Type} [AddCommMonoid β] (f : Fin 2 → β)` (β has `+` and `0`).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R26 · `Fintype.card_fin`** changes the **goal**: `Fintype.card (Fin n) = n`. `simp` applies it by itself.
Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑(Fintype.card (Fin n))` | `⊢ P ↑n` |

**R27 · `Matrix.smul_apply`, `Matrix.add_apply`, `Matrix.sub_apply`, `smul_eq_mul`** change the **goal**: an
entry of a scaled sum of matrices becomes arithmetic on entries. `simp` applies them by itself. Placeholders:
`{ι : Type} (c : ℂ) (M N K : Matrix ι ι ℂ) (i j : ι)`.

| Before | After |
|---|---|
| `⊢ P ((c • (M + N - K)) i j)` | `⊢ P (c * (M i j + N i j - K i j))` |

**R28 · entry of a literal (`simp`)** changes the **goal**: `simp` reads off the entry (`Matrix.of_apply`,
`Matrix.cons_val_…`). Placeholders: `{α : Type} (a b c d : α)`.

| Before | After |
|---|---|
| `⊢ P (!![a, b; c, d] 1 0)` | `⊢ P c` |

### Finishing an equation with `√2`

**R29 · `field_simp`** changes the **goal**: multiplies both sides by every denominator it can prove nonzero
(it uses hypotheses such as `hx : x ≠ 0`, and tries `simp` on the rest; `↑√2 ≠ 0` it can prove itself, but
stating `hne` makes that explicit). The result has no `⁻¹` or `/`;
its exact shape is not predictable, so look at the infoview. Placeholders: `(x y : ℂ) (hx : x ≠ 0)`.

| Before | After |
|---|---|
| `hx : x ≠ 0 ⊢ 2⁻¹ * (x⁻¹ + x⁻¹) = y` | `hx : x ≠ 0 ⊢ 1 + 1 = 2 * x * y` |

**R30 · `linear_combination c * h`** **closes** a goal `a = b` when `a - b - c * (lhs_h - rhs_h)` is `0` by
`ring`; `h` is an equation hypothesis and `c` any coefficient. Example: from `h : x ^ 2 = 3`,
`linear_combination 2 * h` proves `2 * x ^ 2 = 6`. In the exercise `h` is `h2` and you read `c` off the goal
`field_simp` leaves: match the `↑√2 ^ 2` terms.

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: diagonal collapse.** `∑ i, ∑ j, (if i = j then f i j else 0) * g j = ∑ i, f i i * g i`. R14 moves the
`if` out, then R15 removes the `j` sum:

```lean-goal
⊢ ∑ i, ∑ j, (if i = j then f i j else 0) * g j = ∑ i, f i i * g i
⊢ (∑ x, ∑ x_1, if x = x_1 then f x x_1 * g x_1 else 0) = ∑ i, f i i * g i
```

**W2: linearity of an expectation value.** R19 then R20:

```lean-goal
⊢ star v ⬝ᵥ (M + N) *ᵥ v = star v ⬝ᵥ M *ᵥ v + star v ⬝ᵥ N *ᵥ v
⊢ star v ⬝ᵥ (M *ᵥ v + N *ᵥ v) = star v ⬝ᵥ M *ᵥ v + star v ⬝ᵥ N *ᵥ v
```

**W3: the `√3` fact.** R21, R22 with `(by norm_num)`, R23:

```lean-goal
⊢ ↑√3 ^ 2 = 3
⊢ ↑(√3 ^ 2) = 3
⊢ ↑3 = 3
```

**W4: `field_simp` then `linear_combination`.** With `h3 : ↑√3 ^ 2 = 3` and `hne : ↑√3 ≠ 0` in context, R29 turns
the first goal into the second; `linear_combination 3 * h3` (R30) closes it:

```lean-goal
⊢ 3⁻¹ * (↑√3 + ↑√3 + ↑√3) = (↑√3)⁻¹ * 3
⊢ ↑√3 ^ 2 * (1 + 1 + 1) = 3 ^ 2
```

---

## Traps

- `rw [hΦ]` fails after R7: every amplitude sits under a `∑` binder and mentions the bound variable. Use
  `simp only [hΦ]` (R11). The same holds for `mes_expect` in Part 2.
- `rw [Finset.mul_sum]` on the whole Part 1 goal rewrites only the right-hand side (the left-hand instance is
  under a binder). Split with R18 first, then `rw` inside.
- Write casts in full inside a `have`: `((Real.sqrt (Fintype.card d) : ℝ) : ℂ)⁻¹`. A bare `√↑(card d)` is real,
  and the `have` will not match the complex goal.
- Do not expand `chsh` into a 4×4 matrix with `ext`/`fin_cases`: 16 entries of products of `√2`. Linearity plus
  `mes_expect` leaves only 2×2 sums.
- `field_simp` clears only denominators it can prove nonzero. If a `⁻¹` survives it, add `hne : x ≠ 0` for
  that denominator to the context and run it again.
- `ring` does not know `↑√2 ^ 2 = 2`: feed `h2` to `linear_combination`, not `ring`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| amplitude of `Φ` as an `if` | `intro i j; simp [Ket.MES]` | R1 |
| `(√n)⁻¹ * (√n)⁻¹ = n⁻¹` in `ℂ` | `rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp` | R2–R6 |
| `⟨v\|M\|w⟩` → sums | `simp only [dotProduct, mulVec]` | R7 |
| sum over pairs → double sum | `Fintype.sum_prod_type` | R8 |
| entry of `A ⊗ₖ B` | `kroneckerMap_apply` | R9 |
| entry of `star v` | `Pi.star_apply` | R10 |
| rewrite under `∑` with a `∀` fact | `simp only [h]` | R11 |
| `if` out of `star`, `*` | `apply_ite star, star_zero, mul_ite, mul_zero, ite_mul, zero_mul` | R12–R14 |
| collapse `∑ j, if i = j then f j else 0` | `Finset.sum_ite_eq, Finset.mem_univ, if_true` (or `sum_ite_eq'`) | R15 |
| `star` of a real cast | `simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]` | R16 |
| factor into a sum | `rw [Finset.mul_sum]` | R17 |
| equal sums term by term | `refine Finset.sum_congr rfl fun i _ => ?_` | R18 |
| linearity of `*ᵥ`, `⬝ᵥ` | `simp only [add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub]` | R19, R20 |
| `(↑√2) ^ 2 = 2` | `rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp` | R21–R23 |
| `↑√2 ≠ 0` | `simp` | R24 |
| evaluate 2×2 sums of named matrices | `simp [Fin.sum_univ_two, names]` | R25–R28 |
| clear denominators | `field_simp` | R29 |
| goal = `c ·` (hypothesis equation) | `linear_combination c * h` | R30 |
| see the state | infoview | |
