# H079 · The no-cloning theorem: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `rw`, `simp`, `have`, `exact`, `rcases`, `Or.inl`/`Or.inr`.
**New here:** physlib's pure states (`Ket`, `Bra`, the bra-ket `〈ψ‖φ〉`, the product state `ψ ⊗ᵠ φ`), the
unitary group `𝐔[n]`, Mathlib's vector–matrix operations (`*ᵥ`, `ᵥ*`, `⬝ᵥ`, `star`, `Mᴴ`), big-operator
sums `∑` over finite types, complex conjugation `starRingEnd ℂ`, and `linear_combination`.

**The mathematics.** For a finite index type `d` (the basis labels), a ket `ψ : Ket d` is a unit vector
`ψ.vec : d → ℂ`. The inner product is $\langle\psi|\varphi\rangle = \sum_x \overline{\psi_x}\,\varphi_x$
($\overline{z}$ is the complex conjugate). The product state `ψ ⊗ᵠ φ : Ket (d × d)` has entries
$(\psi\otimes\varphi)_{(i,j)} = \psi_i\varphi_j$. A unitary `U : 𝐔[n]` is an `n × n` complex matrix with
$U^\dagger U = 1$, where $U^\dagger$ (Lean: `Uᴴ` or `star U`) is the conjugate transpose. Three facts:

1. $\langle\psi_1\otimes\psi_2|\varphi_1\otimes\varphi_2\rangle = \langle\psi_1|\varphi_1\rangle\langle\psi_2|\varphi_2\rangle$
   (MILESTONE `dot_prod`), because the double sum factors.
2. $\langle Ux|Uy\rangle = \langle x|U^\dagger U y\rangle = \langle x|y\rangle$ (MILESTONE `unitary_dot`).
3. With $z = \langle\psi|\varphi\rangle$: the inputs have inner product
   $\langle\psi\otimes f|\varphi\otimes f\rangle = z\langle f|f\rangle = z$, the outputs
   $\langle\psi\otimes\psi|\varphi\otimes\varphi\rangle = z^2$, and by 2 they are equal. So $z = z^2$,
   i.e. $z(z-1) = 0$, i.e. $z = 0$ or $z = 1$.

MILESTONE `dot_eq_star_dotProduct` translates physlib's `〈ψ‖φ〉` into Mathlib's `star ψ.vec ⬝ᵥ φ.vec`, the
language in which fact 2 is stated.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. A hypothesis `h` in an example is only there to finish it.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Fintype d]` is a
  requirement on the type (a *type class*): `Fintype d` says `d` is finite, so `∑ x : d` makes sense; the
  exercise's `d` and `d × d` meet it. Each entry says which familiar types meet its brackets.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. `∅` means
  the goal is closed.

## Reading the goals

| You see | It means |
|---|---|
| `Ket d` | a normalized vector; field `ψ.vec : d → ℂ`, plus a proof that $\sum_x \lVert\psi_x\rVert^2 = 1$ |
| `Bra d` | the same data, kept as a separate type so that conjugation is never forgotten |
| `〈ψ‖φ〉` (needs `open Braket`) | the inner product; the infoview prints it as `dot (↑ψ) φ` |
| `↑ψ` in `dot (↑ψ) φ` | the bra `Ket.to_bra ψ`, whose entries are the conjugates of `ψ`'s (R2) |
| `ψ x` | a ket used as a function `d → ℂ`; it equals `ψ.vec x` (`Ket.apply`, R4) |
| `⇑ψ` | `ψ` coerced to the function `d → ℂ` (same thing as `fun x => ψ x`) |
| `ψ ⊗ᵠ φ` | `Ket.prod ψ φ : Ket (d × d)`, entry at `(i, j)` is `ψ i * φ j` (R10) |
| `x.1`, `x.2`, `(i, j)` | the two components of a pair `x : d × d`, and the pair itself |
| `𝐔[n]` | `Matrix.unitaryGroup n ℂ`, the unitary `n × n` matrices; `↥𝐔[n]` is its element type |
| `U.val`, `↑U` | the matrix underlying `U : 𝐔[n]` (the same term, printed `↑U`); `(↑U)ᴴ` is its conjugate transpose |
| `Matrix n n ℂ`, `1` | `n × n` complex matrices indexed by the finite type `n`; `1` is the identity matrix |
| `M *ᵥ v` | matrix times column vector: $(Mv)_i = \sum_j M_{ij} v_j$ |
| `v ᵥ* M` | row vector times matrix: $(vM)_j = \sum_i v_i M_{ij}$ |
| `v ⬝ᵥ w` | `dotProduct v w` $= \sum_i v_i w_i$, with NO conjugation |
| `v ⬝ᵥ ↑U *ᵥ y`, `v ᵥ* A ⬝ᵥ w` | the infoview drops brackets: `v ⬝ᵥ (↑U *ᵥ y)` and `(v ᵥ* A) ⬝ᵥ w` (R13) |
| `star v` (vector) | entrywise conjugate: `star v i = star (v i)` (R6) |
| `star M`, `Mᴴ` (matrix) | conjugate transpose $M^\dagger$; `Mᴴ i j = star (M j i)` |
| `star z`, `(starRingEnd ℂ) z` (number) | the complex conjugate $\overline{z}$, two spellings (R6) |
| `(starRingEnd (d → ℂ)) v` | conjugation applied to a whole function `v`, entrywise (R3) |
| `∑ x, g x` | $\sum_{x} g(x)$ over all of a finite type; `∑ x : d × d` runs over pairs |
| `Finset.univ` | the set of all elements of a finite type; `x✝ : i ∈ Finset.univ` is a trivial fact |
| `{ vec := …, normalized' := ⋯ }` | a `Ket`/`Bra` written out as a structure after unfolding its definition |
| `x✝`, `h✝`, `inst✝` | inaccessible names Lean made (you cannot type them); `h✝` is an older `h` shadowed by a new one, `inst✝` an unnamed type-class argument |

---

## Part 1 · `dot_eq_star_dotProduct` (MILESTONE 1)

Statement: `〈ψ‖φ〉 = star ψ.vec ⬝ᵥ φ.vec`, i.e. physlib's bra-ket is Mathlib's dot product with the first
vector conjugated. Both sides are sums over `d`; unfold both and make the summands identical. `simp` with
R1, R2, R4, R5 does all of it at once (it finds R3 and R6 itself).

**R1 · `simp only [Braket.dot]`** changes the **goal**: the bra-ket becomes its defining sum
`dot ξ ψ = ∑ x, ξ x * ψ x`. Placeholders: `{d : Type} [Fintype d] (ψ φ : Ket d)`.

| Before | After |
|---|---|
| `⊢ P (dot (↑ψ) φ)` | `⊢ P (∑ x, ↑ψ x * φ x)` |

**R2 · `simp only [Ket.to_bra]`, then `simp only [Bra.apply]`** change the **goal**: an entry of the bra `↑ψ`
becomes an entry of the conjugated function. `Ket.to_bra ψ` is defined as `⟨conj ψ, _⟩`;
`Bra.apply : ξ i = ξ.vec i` reads the field. Placeholders: `{d : Type} [Fintype d] (ψ : Ket d) (x : d)`.

| Before | After `simp only [Ket.to_bra]` | After `simp only [Bra.apply]` |
|---|---|---|
| `⊢ P (↑ψ x)` | `⊢ P ({ vec := (starRingEnd (d → ℂ)) ⇑ψ, normalized' := ⋯ } x)` | `⊢ P ((starRingEnd (d → ℂ)) (⇑ψ) x)` |

**R3 · `rw [Pi.conj_apply]`** changes the **goal**: conjugating a function and then evaluating is evaluating
and then conjugating. `simp` applies it by itself. Placeholders: `{d : Type} (v : d → ℂ) (x : d)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd (d → ℂ)) v x)` | `⊢ P ((starRingEnd ℂ) (v x))` |

**R4 · `rw [Ket.apply]`** changes the **goal**: the lemma is `Ket.apply : ψ i = ψ.vec i` (true by `rfl`).
Placeholders: `{d : Type} [Fintype d] (ψ : Ket d) (x : d)`.

| Before | After |
|---|---|
| `⊢ P (ψ x)` | `⊢ P (ψ.vec x)` |

**R5 · `simp only [dotProduct]`** changes the **goal**: `v ⬝ᵥ w` becomes its defining sum.
Placeholders: `{d : Type} [Fintype d] (v w : d → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ w)` | `⊢ P (∑ i, v i * w i)` |

**R6 · `rw [Pi.star_apply]`, then `rw [RCLike.star_def]`** change the **goal**. `Pi.star_apply : star v i = star (v i)`
(star of a function is entrywise); `RCLike.star_def : star = starRingEnd` on `ℂ` (and `ℝ`). `simp` applies
both by itself. Placeholders: `{d : Type} (v : d → ℂ) (i : d)`.

| Before | After `rw [Pi.star_apply]` | After `rw [RCLike.star_def]` |
|---|---|---|
| `⊢ P (star v i)` | `⊢ P (star (v i))` | `⊢ P ((starRingEnd ℂ) (v i))` |

---

## Part 2 · `dot_prod` (MILESTONE 2)

Statement: `〈ψ₁ ⊗ᵠ ψ₂‖φ₁ ⊗ᵠ φ₂〉 = 〈ψ₁‖φ₁〉 * 〈ψ₂‖φ₂〉`. Left: one sum over pairs. Right: a product of two sums.
Bring both to a double sum $\sum_i\sum_j$ (R1, R7, R8), then compare summands (R9) and compute one summand
(R10, R2–R4, R11, `ring`).

**R7 · `rw [Fintype.sum_prod_type]`** changes the **goal**: a sum over pairs becomes a double sum,
$\sum_{x : \alpha\times\beta} g(x) = \sum_a \sum_b g(a, b)$. Placeholders:
`{α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (g : α × β → M)`; `[AddCommMonoid M]` asks for a
commutative `+` with `0` (`ℂ`, `ℝ`, `ℕ` qualify).

| Before | After |
|---|---|
| `⊢ P (∑ x, g x)` | `⊢ P (∑ x, ∑ y, g (x, y))` |

**R8 · `rw [Finset.sum_mul_sum]`** changes the **goal**: $(\sum_i f_i)(\sum_j g_j) = \sum_i\sum_j f_i g_j$.
Placeholders: `{α β R : Type} [Fintype α] [Fintype β] [NonUnitalNonAssocSemiring R] (f : α → R) (g : β → R)`;
the bracket asks for `+` and a `*` that distributes over it (`ℂ` qualifies).

| Before | After |
|---|---|
| `⊢ P ((∑ i, f i) * ∑ j, g j)` | `⊢ P (∑ i, ∑ j, f i * g j)` |

**R9 · `refine Finset.sum_congr rfl fun i _ => ?_`** changes the **goal and the context**: two sums over the
same index set are equal when their summands are. `Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) →
s₁.sum f = s₂.sum g`; `rfl` proves the index sets agree. For the double sum of Part 2 nest it:
`refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_`.
Placeholders: `{α M : Type} [Fintype α] [AddCommMonoid M] (f g : α → M)`.

| Before | After |
|---|---|
| `⊢ ∑ i, f i = ∑ i, g i` | `i : α, x✝ : i ∈ Finset.univ ⊢ f i = g i` |

**R10 · `simp only [Ket.prod, Ket.apply]`** changes the **goal**: an entry of a product state becomes the
product of entries. Placeholders: `{d : Type} [Fintype d] (ψ φ : Ket d) (i j : d)`. On the bra side
`↑(ψ ⊗ᵠ φ) (i, j)` you also need R2, which gives `conj (ψ.vec i * φ.vec j)`; then R11.

| Before | After |
|---|---|
| `⊢ P ((ψ ⊗ᵠ φ) (i, j))` | `⊢ P (ψ.vec i * φ.vec j)` |

**R11 · `rw [map_mul]`** changes the **goal**: conjugation is multiplicative,
$\overline{ab} = \overline{a}\,\overline{b}$. `map_mul` holds for every map that preserves `*`, and
`starRingEnd ℂ` is one. `simp` applies it by itself. Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (a * b))` | `⊢ P ((starRingEnd ℂ) a * (starRingEnd ℂ) b)` |

What is left after `simp [Ket.prod, Ket.to_bra, Bra.apply, Ket.apply]` is the same four factors in a
different order and grouping, `conj ψ₁ᵢ * conj ψ₂ⱼ * (φ₁ᵢ * φ₂ⱼ) = conj ψ₁ᵢ * φ₁ᵢ * (conj ψ₂ⱼ * φ₂ⱼ)`:
close it with `ring` (TACTIC_STATES, "Closing").

---

## Part 3 · `unitary_dot` (MILESTONE 3)

Statement: `star (U.val *ᵥ x) ⬝ᵥ (U.val *ᵥ y) = star x ⬝ᵥ y`, i.e. $\langle Ux|Uy\rangle = \langle x|y\rangle$.
Push the left `U` across the dot product as `Uᴴ` and combine: $\overline{Ux}\cdot Uy = (\overline{x}\,U^\dagger)\cdot Uy
= (\overline{x}\,U^\dagger U)\cdot y = \overline{x}\cdot y$. One `rw [R12, R13, R14, R15, R16, R17]`; the goal then
closes by `rfl` automatically. Placeholders for all six: `{n : Type} [Fintype n]` (and `[DecidableEq n]`
where the identity matrix `1` or `𝐔[n]` appears: equality of indices must be decidable to write `1`);
the exercise's `d × d` meets both.

**R12 · `rw [Matrix.star_mulVec]`** changes the **goal**: $\overline{Mv} = \overline{v}\,M^\dagger$ (a column
becomes a row). Placeholders: `(M : Matrix n n ℂ) (v : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star (M *ᵥ v))` | `⊢ P (star v ᵥ* Mᴴ)` |

**R13 · `rw [Matrix.dotProduct_mulVec]`** changes the **goal**: $v\cdot(Aw) = (vA)\cdot w$. Note how the
infoview drops brackets: `v ⬝ᵥ A *ᵥ w` means `v ⬝ᵥ (A *ᵥ w)`, and `v ᵥ* A ⬝ᵥ w` means `(v ᵥ* A) ⬝ᵥ w`.
Placeholders: `(A : Matrix n n ℂ) (v w : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ A *ᵥ w)` | `⊢ P (v ᵥ* A ⬝ᵥ w)` |

**R14 · `rw [Matrix.vecMul_vecMul]`** changes the **goal**: $(vM)N = v(MN)$; `v ᵥ* M ᵥ* N` means
`(v ᵥ* M) ᵥ* N`. Placeholders: `(M N : Matrix n n ℂ) (v : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (v ᵥ* M ᵥ* N)` | `⊢ P (v ᵥ* (M * N))` |

**R15 · `rw [← Matrix.star_eq_conjTranspose]`** changes the **goal**: the lemma is `star M = Mᴴ`; right to left
it turns `Mᴴ` back into `star M`, the form R16 is stated in. Placeholders: `(M : Matrix n n ℂ)`.

| Before | After |
|---|---|
| `⊢ P Mᴴ` | `⊢ P (star M)` |

**R16 · `rw [Matrix.UnitaryGroup.star_mul_self]`** changes the **goal**: for `U : 𝐔[n]`,
`star ↑U * ↑U = 1` (this is $U^\dagger U = 1$). Placeholders: `[DecidableEq n] (U : 𝐔[n])`.

| Before | After |
|---|---|
| `⊢ P (star ↑U * ↑U)` | `⊢ P 1` |

**R17 · `rw [Matrix.vecMul_one]`** changes the **goal**: `v ᵥ* 1 = v`. Placeholders:
`[DecidableEq n] (v : n → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (v ᵥ* 1)` | `⊢ P v` |

**W2: the same shape with `*ᵥ` and a left inverse** (`hAB : A * B = 1`), chained by `Matrix.mulVec_mulVec`,
`rw [hAB]`, `Matrix.one_mulVec`:

```lean-goal
⊢ A *ᵥ B *ᵥ x = x
⊢ (A * B) *ᵥ x = x
⊢ 1 *ᵥ x = x
```

---

## Part 4 · `cloning_forces_orthogonal`

Statement: from `hψ : ↑U *ᵥ (ψ ⊗ᵠ f).vec = (ψ ⊗ᵠ ψ).vec` and `hφ : ↑U *ᵥ (φ ⊗ᵠ f).vec = (φ ⊗ᵠ φ).vec`,
conclude `〈ψ‖φ〉 = 0 ∨ 〈ψ‖φ〉 = 1`. First the fact `key : 〈ψ‖φ〉 * 〈f‖f〉 = 〈ψ‖φ〉 * 〈ψ‖φ〉`, proved by one
`rw` chain through MILESTONES 2, 1, the hypotheses and MILESTONE 3. Then algebra on $z = \langle\psi|\varphi\rangle$.

**R18 · `rw [← L]` where `L` has arguments** changes the **goal**. Right to left, `rw` searches for `L`'s right
side with its arguments as unknowns; the FIRST match fixes them, and only that instance is rewritten. A second
`rw [← L]` takes the next instance. Left to right (`rw [L]`) the same rule applies to `L`'s left side. Example lemma `mul_add : a * (b + c) = a * b + a * c`, placeholders
`{R : Type} [CommRing R] (x y z w : R)`. In Part 4 this is how `rw [← dot_prod, ← dot_prod]` turns the left
product and then the right product of `key` into one bra-ket each, and `rw [dot_eq_star_dotProduct,
dot_eq_star_dotProduct]` (left to right) converts first the left, then the right bra-ket.

| Before | After first `rw [← mul_add]` | After second `rw [← mul_add]` |
|---|---|---|
| `⊢ P (x * y + x * z) (w * y + w * z)` | `⊢ P (x * (y + z)) (w * y + w * z)` | `⊢ P (x * (y + z)) (w * (y + z))` |

**R19 · `rw [Braket.dot_self_eq_one] at h`** changes the **context**: `Braket.dot_self_eq_one : 〈ψ‖ψ〉 = 1` (a ket
is normalized). `at h` rewrites inside the hypothesis `h` instead of the goal. Placeholders:
`{d : Type} [Fintype d] (f : Ket d)`.

| Before | After |
|---|---|
| `h : P (dot (↑f) f) ⊢ P 1` | `h : P 1 ⊢ P 1` |

**R20 · `linear_combination e`** **closes** an equation `a = b` in a commutative ring when `a - b` equals the
`lhs - rhs` of the combination `e` after `ring` normalization. `e` is built from hypotheses with numbers or
terms as coefficients: `h`, `-h`, `2 * h`, `h₁ - z * h₂`. Placeholders: `{R : Type} [CommRing R] (a b : R)`.

| Before | After |
|---|---|
| `h : a = b ⊢ b - a = 0` | ∅ (with `linear_combination -h`: `b - a - 0 = -(a - b)`) |

**R21 · `rcases mul_eq_zero.mp h with h | h`** changes the **goal list and the context**:
`mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0` (true in `ℂ`, `ℝ`: no zero divisors); `.mp` uses the `→` direction
and `rcases … with h | h` splits the `∨`. Placeholders: `(a b : ℂ) (G : Prop)`.

| Before | After |
|---|---|
| `h : a * b = 0 ⊢ G` | `h : a = 0 ⊢ G`, `h : b = 0 ⊢ G` |

**R22 · `sub_eq_zero.mp`** **closes** `a = b` from `h : a - b = 0`; `sub_eq_zero : a - b = 0 ↔ a = b`.
Placeholders: `{R : Type} [CommRing R] (a b : R)`.

| Before | After |
|---|---|
| `h : a - b = 0 ⊢ a = b` | ∅ (`exact sub_eq_zero.mp h`) |

**R23 · `Or.inl`, `Or.inr`** **close** `A ∨ B` from a proof of `A`, resp. `B`. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `hb : B ⊢ A ∨ B` | ∅ (`exact Or.inr hb`) |

**W1: a sum over pairs of a product factors** (R7, then R8; the goal closes by `rfl`):

```lean-goal
⊢ ∑ x, a x.1 * b x.2 = (∑ i, a i) * ∑ j, b j
⊢ ∑ x, ∑ y, a (x, y).1 * b (x, y).2 = (∑ i, a i) * ∑ j, b j
```

**W3: `key : z * 2 = z * z` → `z = 0 ∨ z = 2`.** `have h : z * (z - 2) = 0 := by linear_combination -key`
(R20), then R21, then R23 in the first case and R22 inside R23 in the second.

---

## Traps

- physlib has its own `MState.no_cloning`. `BANNED: no_cloning` matches the last name component anywhere in
  your file, so do not name a helper `no_cloning` either.
- `〈ψ‖φ〉` is scoped notation: it needs `open Braket` (the file has it). The infoview shows `dot (↑ψ) φ`.
- Order in the `key` chain: `hψ`'s right side `(ψ ⊗ᵠ ψ).vec` appears only AFTER MILESTONE 1 has turned
  `dot (↑(ψ ⊗ᵠ ψ)) (φ ⊗ᵠ φ)` into `star (ψ ⊗ᵠ ψ).vec ⬝ᵥ (φ ⊗ᵠ φ).vec`. So: `← dot_prod` twice, then
  `dot_eq_star_dotProduct` twice, then `← hψ, ← hφ`, then `unitary_dot`.
- `rw [← dot_prod]` rewrites one product per call (R18); you need it twice. The same goes for
  `dot_eq_star_dotProduct`.
- `star` means three things: on `ℂ` the conjugate, on a vector the entrywise conjugate, on a matrix the
  conjugate transpose. R12 produces `Mᴴ`, but R16 is stated with `star`: convert with R15.
- `⬝ᵥ` does not conjugate. The physical inner product is `star x ⬝ᵥ y`, not `x ⬝ᵥ y`.
- `linear_combination key` vs `-key`: the sign must make `goal.lhs - goal.rhs` equal `±(key.lhs - key.rhs)`.
  If it fails, it shows the `ring` goal it could not close; flip the sign.
- `key` still contains `〈f‖f〉`: rewrite it to `1` with R19 `at key` before `linear_combination`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| bra-ket → sum | `simp only [Braket.dot]` | R1 |
| bra entry → conjugated ket entry | `simp [Ket.to_bra, Bra.apply, Ket.apply]` | R2–R4 |
| `v ⬝ᵥ w` → sum | `simp only [dotProduct]` | R5 |
| `star v i` → `conj (v i)` | `Pi.star_apply`, `RCLike.star_def` (in `simp`) | R6 |
| sum over pairs → double sum | `rw [Fintype.sum_prod_type]` | R7 |
| product of sums → double sum | `rw [Finset.sum_mul_sum]` | R8 |
| equal sums from equal summands | `refine Finset.sum_congr rfl fun i _ => ?_` | R9 |
| entry of `ψ ⊗ᵠ φ` | `simp [Ket.prod, Ket.apply]` | R10 |
| `conj (a * b)` | `map_mul` (in `simp`) | R11 |
| shuffle factors | `ring` | TACTIC_STATES |
| `star (M *ᵥ v)` → `star v ᵥ* Mᴴ` | `rw [Matrix.star_mulVec]` | R12 |
| `v ⬝ᵥ (A *ᵥ w)` → `(v ᵥ* A) ⬝ᵥ w` | `rw [Matrix.dotProduct_mulVec]` | R13 |
| `v ᵥ* M ᵥ* N` → `v ᵥ* (M * N)` | `rw [Matrix.vecMul_vecMul]` | R14 |
| `Mᴴ` → `star M` | `rw [← Matrix.star_eq_conjTranspose]` | R15 |
| `star ↑U * ↑U` → `1` | `rw [Matrix.UnitaryGroup.star_mul_self]` | R16 |
| `v ᵥ* 1` → `v` | `rw [Matrix.vecMul_one]` | R17 |
| fold a product back with a lemma | `rw [← L, ← L]` (once per instance) | R18 |
| `〈f‖f〉` → `1` in a hypothesis | `rw [Braket.dot_self_eq_one] at h` | R19 |
| equation from hypotheses by ring algebra | `linear_combination ±h` | R20 |
| `a * b = 0` → two cases | `rcases mul_eq_zero.mp h with h \| h` | R21 |
| `a - b = 0` → `a = b` | `sub_eq_zero.mp h` | R22 |
| prove a disjunction | `exact Or.inl h` / `exact Or.inr h` | R23 |
| see the state | infoview | |
