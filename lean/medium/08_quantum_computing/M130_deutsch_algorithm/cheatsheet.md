# M130 · Deutsch's algorithm: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's matrices and vectors over `ℂ`,
matrix-times-vector `*ᵥ`, the Kronecker product `⊗ₖ`, basis vectors `Pi.single`, finite sums over
`Fin 2` and `Fin 2 × Fin 2`, `Complex.normSq` (|z|²) with real and imaginary parts, and `Real.sqrt`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid γ]`
  is a requirement on `γ` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin 2` | the type `{0, 1}`; its `+` is addition mod 2 (`1 + 1 = 0`) |
| `Fin 2 → ℂ`, `Fin 2 × Fin 2 → ℂ` | a one-qubit and a two-qubit state vector (complex amplitudes) |
| `Matrix (Fin 2) (Fin 2) ℂ` | a 2×2 complex matrix, rows and columns indexed by `Fin 2` |
| `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ` | a 4×4 complex matrix whose rows and columns are indexed by pairs |
| `!![a, b; c, d]` | the 2×2 matrix with rows `a b` and `c d` |
| `M i j` | the entry in row `i`, column `j` |
| `c • M` | scalar `c` times every entry of `M` |
| `of f` | `Matrix.of f`: the matrix whose entry `(i, j)` is `f i j` (R7) |
| `M *ᵥ v` | `Matrix.mulVec M v`: matrix `M` times column vector `v` (R8) |
| `u ⬝ᵥ v` | `dotProduct u v = ∑ i, u i * v i` (R8) |
| `A ⊗ₖ B` | the Kronecker product (`open scoped Kronecker`): `(A ⊗ₖ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ * B i₂ j₂` (R11) |
| `kroneckerMap (fun x1 x2 => x1 * x2) A B` | how Lean prints `A ⊗ₖ B`, the Kronecker product (R11) |
| `1 i j` | entry of the identity matrix `1` (R12) |
| `Pi.single i x` | the vector with `x` at index `i`, `0` elsewhere (R13) |
| `p.1`, `p.2`, `(x, y)` | the two components of a pair, and a pair |
| `∑ x, f x` | `Finset.sum Finset.univ f`, the sum over every element of a finite type |
| `normSq z` | `Complex.normSq z = z.re * z.re + z.im * z.im = \|z\|²` (R16) |
| `z.re`, `z.im` | real and imaginary parts of `z : ℂ`, both real numbers |
| `↑x` | the real number `x` cast into `ℂ` |
| `√x` | `Real.sqrt x`, a real number |
| `(↑√2)⁻¹` | `(√2 : ℂ)⁻¹`, the scalar in `H` |
| `if c then a else b` | `a` when the condition `c` holds, else `b`; `simp` removes it once `c` is decided (R15) |
| `√2 / 2` | what `simp` makes of the real part of `(↑√2)⁻¹` (R18); the balanced goals are polynomials in it |
| `case inl.inr` | after two `rcases`: first split took the left case (`f 0 = 0`), second the right (`f 1 = 1`) |

---

## Part 1 · `deutsch_correct`

Statement: for every `f : Fin 2 → Fin 2`, `∑ y, normSq (deutsch f (1, y))` equals `0` if `f 0 = f 1` and `1`
otherwise. Every object is a finite array of explicit numbers once `f 0` and `f 1` are known, so the proof
is: two facts, a four-way case split, one big `simp`, and real arithmetic with `√2`.

What the definitions mean:

- A qubit state is a vector `Fin 2 → ℂ` (amplitudes of `|0⟩`, `|1⟩`); a two-qubit state is
  `Fin 2 × Fin 2 → ℂ`, indexed by pairs `(x, y)`: first qubit `x`, second qubit `y`.
- `ket b = Pi.single b 1` is the basis vector `|b⟩`; `tensor u v` is the product state `u ⊗ v`,
  `(u ⊗ v)(x, y) = u x * v y`.
- `H = (1/√2)·[[1, 1], [1, -1]]` is the Hadamard gate; `H ⊗ₖ H` applies it to both qubits, `H ⊗ₖ 1` to the
  first only (`1` is the 2×2 identity matrix).
- `Uf f` is the oracle `|x, y⟩ ↦ |x, y + f x⟩`, where `+` in `Fin 2` is addition mod 2 (XOR). As a matrix,
  entry `(p, q)` is `1` when `p.1 = q.1` and `p.2 = q.2 + f q.1`, else `0`.
- `deutsch f` is the final state. The probability that the first qubit reads `1` is
  `∑ y, |deutsch f (1, y)|²` (Born rule), and `|z|² = Complex.normSq z`.
- The theorem: that probability is `0` when `f` is constant (`f 0 = f 1`) and `1` when it is balanced.

### Facts proved first

**R1 · `decide`** **closes** a statement about finitely many concrete values: it evaluates it. `Fin n` has
exactly the elements `0, …, n-1`, so `∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2` is checked by trying each `x`. Not
for `ℝ` or `ℂ`, and not for statements about a variable such as `f`.

**R2 · `rw [show a = b by ring]`** changes the **goal**. `show a = b by ring` is a proof of `a = b` made on the
spot; `rw` replaces `a` by `b`. Use it to regroup a power so a lemma fits, e.g. `x ^ 6` as `(x ^ 2) ^ 3`.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (x ^ 6)` | `⊢ P ((x ^ 2) ^ 3)` |

**R3 · `rw [Real.sq_sqrt]`** changes the **goal list**. The lemma is `Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x`, so
the goal is rewritten and a side goal `0 ≤ x` is added. Write `rw [Real.sq_sqrt (by norm_num)]` to prove the
side goal immediately. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (√x ^ 2)` | `⊢ P x`, `⊢ 0 ≤ x` |

**R4 · `norm_num`** **closes** a goal made of numerals: `(2 : ℝ) ^ 3 * (1 / 8) = 1`, `8 * (1 / 8) = 1`.

### Splitting on the values of `f`

**R5 · `rcases two (g 0) with h0 | h0`** changes the **goal list and the context**. `two (g 0)` is the fact
`two : ∀ x : Fin 2, x = 0 ∨ x = 1` applied to `x := g 0`, a proof of `g 0 = 0 ∨ g 0 = 1`. `rcases … with h0 | h0`
splits the `∨`: one goal per side, each with its own `h0`. The goal itself is unchanged; `g 0` is still
there until you rewrite with `h0`. Placeholders: `(g : Fin 2 → Fin 2) (P : Fin 2 → Prop)`. Two splits joined by
`<;>` give four goals.

| Before | After |
|---|---|
| `⊢ P (g 0)` | `h0 : g 0 = 0 ⊢ P (g 0)`, `h0 : g 0 = 1 ⊢ P (g 0)` |

**R6 · `simp [h0, h1]`** changes the **goal**: hypotheses `h0 : g 0 = 0`, `h1 : g 1 = 1` are used as rewrite
rules, left to right. Once the values are in, `simp` decides the condition `0 = 1` (false) and drops the
`if`. Placeholders: `(g : Fin 2 → Fin 2) (a b : ℂ)`.

| Before | After |
|---|---|
| `h0 : g 0 = 0, h1 : g 1 = 1 ⊢ P (if g 0 = g 1 then a else b)` | `⊢ P b` |

### Unfolding the circuit

Unfold the problem's definitions by naming them in `simp [deutsch, Uf, …]` (TACTIC_STATES, "Rewriting and
simplifying"). `simp` applies R7, R10, R11, R14, R15, R17, R18 by itself. R8, R9 and R16 must be named, or
`simp` stops at `M *ᵥ v`, at a sum over pairs, and at `normSq`. R12 and R13 rewrite `1 i j` and
`Pi.single i x i'` at **any** indices; `simp` alone only handles numeral indices (`1 0 1`, `Pi.single 0 1 1`).
In this problem the indices are numerals once the sums are expanded, so naming R10–R13 is optional, but it
does no harm and keeps the call working if a sum is left unexpanded.

**R7 · `Matrix.of_apply`** changes the **goal**: `Matrix.of f i j = f i j`. `Uf` is written with `Matrix.of`.
Placeholders: `{m n α : Type} (f : m → n → α) (i : m) (j : n)`.

| Before | After |
|---|---|
| `⊢ P (of f i j)` | `⊢ P (f i j)` |

**R8 · `Matrix.mulVec`, then `dotProduct`** change the **goal**: an entry of a matrix-vector product becomes
a sum, $(Mv)_i = \sum_j M_{ij} v_j$. Both are definitions; `simp [Matrix.mulVec, dotProduct]` unfolds both
(after `open Matrix`, `mulVec` is the same name). Placeholders: `{α : Type} [NonUnitalNonAssocSemiring α]`
(α has `+`, `*`, `0`, as `ℂ` does), `(M : Matrix (Fin 2) (Fin 2) α) (v : Fin 2 → α) (i : Fin 2)`.

| Before | After `simp only [Matrix.mulVec]` | After `simp only [dotProduct]` |
|---|---|---|
| `⊢ P ((M *ᵥ v) i)` | `⊢ P ((fun j => M i j) ⬝ᵥ v)` | `⊢ P (∑ x, M i x * v x)` |

**R9 · `Fintype.sum_prod_type`** changes the **goal**: a sum over pairs becomes a double sum,
`∑ x : α × β, f x = ∑ a, ∑ b, f (a, b)`. Needed because the two-qubit vectors are indexed by
`Fin 2 × Fin 2`. Placeholders: `{α β γ : Type} [Fintype α] [Fintype β]` (α, β finite, e.g. `Fin 2`),
`[AddCommMonoid γ]` (γ has `+` and `0`, e.g. `ℂ`), `(f : α × β → γ)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, f x)` | `⊢ P (∑ x, ∑ y, f (x, y))` |

**R10 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms. Placeholders:
`{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R11 · `Matrix.kroneckerMap_apply`** changes the **goal**: an entry of a Kronecker product is a product of
entries, `(A ⊗ₖ B) i j = A i.1 j.1 * B i.2 j.2`, where `i = (i.1, i.2)` and `j = (j.1, j.2)` are pairs.
`⊗ₖ` needs `open scoped Kronecker`, and Lean prints it as `kroneckerMap (fun x1 x2 => x1 * x2) A B`.
Placeholders: `{α : Type} [Mul α] (A B : Matrix (Fin 2) (Fin 2) α) (i j : Fin 2 × Fin 2)`.

| Before | After |
|---|---|
| `⊢ P (kroneckerMap (fun x1 x2 => x1 * x2) A B i j)` | `⊢ P (A i.1 j.1 * B i.2 j.2)` |

**R12 · `Matrix.one_apply`** changes the **goal**: an entry of the identity matrix becomes an `if`,
`(1 : Matrix n n α) i j = if i = j then 1 else 0`. Placeholders: `{α : Type} [Zero α] [One α] (i j : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P (1 i j)` | `⊢ P (if i = j then 1 else 0)` |

**R13 · `Pi.single_apply`** changes the **goal**: an entry of a basis vector becomes an `if`,
`Pi.single i x i' = if i' = i then x else 0`. `ket b` is `Pi.single b 1`. Placeholders:
`{α : Type} [Zero α] (i i' : Fin 2) (x : α)`.

| Before | After |
|---|---|
| `⊢ P (Pi.single i x i')` | `⊢ P (if i' = i then x else 0)` |

**R14 · entry of `c • !![…]`** changes the **goal**. `simp` uses `Matrix.smul_apply` (`(c • M) i j = c • M i j`),
`smul_eq_mul` (`c • z = c * z` for numbers) and `Matrix.of_apply`, `Matrix.cons_val_…` (entries of a
literal). Placeholders: `(c a b d e : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((c • !![a, b; d, e]) 1 0)` | `⊢ P (c * d)` |

**R15 · `Fin 2` arithmetic and `if`** changes the **goal**: `simp` computes with `Fin 2` numerals
(`1 + 1 = 0`: addition mod 2) and replaces `if True then a else b` by `a`, `if False then a else b` by `b`.
This is how the oracle condition `p.2 = q.2 + f q.1` disappears once `f 0`, `f 1` are known.
Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (if 1 + 1 = 0 then a else b)` | `⊢ P a` |

### Probabilities: `normSq`, real and imaginary parts

**R16 · `Complex.normSq_apply`** changes the **goal**: `normSq z = z.re * z.re + z.im * z.im`, i.e. |z|² as
real arithmetic. Placeholders: `(z : ℂ)`, with the goal in `ℝ`.

| Before | After |
|---|---|
| `⊢ P (normSq z)` | `⊢ P (z.re * z.re + z.im * z.im)` |

**R17 · `.re` of real casts** changes the **goal**: `simp` uses `Complex.mul_re`
(`(z * w).re = z.re * w.re - z.im * w.im`), `Complex.ofReal_re` (`(↑x).re = x`) and `Complex.ofReal_im`
(`(↑x).im = 0`), and the product is real again. `add_re`, `neg_re` and the `.im` versions work the same
way. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑x * ↑y).re` | `⊢ P (x * y)` |

**R18 · `.re` of an inverse cast** changes the **goal**: `simp` uses `Complex.inv_re`
(`z⁻¹.re = z.re / normSq z`), `Complex.normSq_ofReal` (`normSq ↑r = r * r`) and `Real.mul_self_sqrt`
(`0 ≤ x → √x * √x = x`), so `(↑√x)⁻¹.re` becomes `√x / x`, and `(↑√x)⁻¹.im` becomes `0`. With `x = 2`
the side condition `0 ≤ 2` is proved by `simp` itself; that is why the entries of `H` turn into `√2 / 2`.
Placeholders: `(x : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `hx : 0 ≤ x ⊢ P (↑√x)⁻¹.re` | `⊢ P (√x / x)` |

**R19 · `ring_nf`** changes the **goal**: it puts every ring expression into a normal form. A product of
copies of `a / 2` becomes one power with a numeric coefficient. After the big `simp`, the balanced cases
are a polynomial in `√2 / 2`, and `ring_nf` turns it into `√2 ^ 6 * (1 / 8) = 1`; then `rw [s6]` and R4.
Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a / 2 * (a / 2 * (a / 2)))` | `⊢ P (a ^ 3 * (1 / 8))` |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: a gate on one qubit of a product state.** `NOT = !![0, 1; 1, 0]` on the first qubit of `|0⟩|0⟩`; the
amplitude of `|1⟩|0⟩` is `1`. Before `simp` the goal prints as

```lean-goal
⊢ (kroneckerMap (fun x1 x2 => x1 * x2) NOT 1 *ᵥ fun p => Pi.single 0 1 p.1 * Pi.single 0 1 p.2) (1, 0) = 1
```

and `simp [NOT, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Pi.single_apply]`
closes it (R8, R9, R11, R13; R7, R12, R14, R15 automatically).

**W2: case split, then `simp [h]`.** `∑ y, if y = g 0 + 1 then 1 else 0 = 1`. After
`rcases two (g 0) with h | h` (R5) both goals still mention `g 0`:

```lean-goal
⊢ (∑ y, if y = g 0 + 1 then 1 else 0) = 1
```

and `all_goals simp [h]` closes them (R6, R15).

**W3: a power of a square root** (R2, R3 with `(by norm_num)`, R4):

```lean-goal
⊢ √3 ^ 4 = 9
⊢ (√3 ^ 2) ^ 2 = 9
⊢ 3 ^ 2 = 9
```

**W4: a probability with `(√3)⁻¹`.** First `have s4 : Real.sqrt 3 ^ 4 = 9` (W3). Then
`simp [Complex.normSq_apply]` (R16–R18), `ring_nf` (R19), `rw [s4]`, `norm_num` (R4):

```lean-goal
⊢ normSq ((↑√3)⁻¹ * (↑√3)⁻¹) * 9 = 1
⊢ √3 / 3 * (√3 / 3) * (√3 / 3 * (√3 / 3)) * 9 = 1
⊢ √3 ^ 4 * (1 / 9) = 1
⊢ 9 * (1 / 9) = 1
```

This is the exercise's ending in miniature: `simp` leaves products of `√x / x`, never a power; `ring_nf`
collects them into one power, which your `have` must match literally.

---

## Traps

- Split on `f 0` and `f 1` **before** `simp`. For an unknown `f`, `simp` cannot decide `f 0 = f 1` or
  `q.2 + f q.1`, and the `if`s stay.
- Prove `two` and `s6` **before** the splits: a `have` after `<;>` must be repeated in every case.
- `Fin 2` addition is XOR: `1 + 1 = 0`. The oracle writes `y + f x`, not `y ⊕ f x`.
- Give `simp` all five definitions (`deutsch, Uf, H, ket, tensor`). A definition it does not unfold stays
  opaque, and no lemma about `*ᵥ` or `⊗ₖ` can fire.
- State `s6` in `ℝ`: `Real.sqrt 2 ^ 6 = 8`. After R16–R18 the goal is real, with `√2`, not `↑√2`; a `have`
  about `(Real.sqrt 2 : ℂ)` will not match. `rw [s6]` needs `√2 ^ 6` to appear literally, so run `ring_nf` first.
- In two of the four cases (the constant ones) `simp` already closes the goal. With `<;>` the later tactics
  run only on the goals that remain, so `… <;> ring_nf <;> rw [s6] <;> norm_num` is fine; with `;` it is not.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `∀ x : Fin 2, x = 0 ∨ x = 1` | `by decide` | R1 |
| regroup a power | `rw [show a = b by ring]` | R2 |
| `√x ^ 2 → x` | `rw [Real.sq_sqrt (by norm_num)]` | R3 |
| numeric goal | `norm_num` | R4 |
| split on the value of `f 0` | `rcases two (f 0) with h0 \| h0` | R5 |
| substitute the values | `simp [h0, h1, …]` | R6 |
| unfold the problem's definitions | `simp [deutsch, Uf, H, ket, tensor, …]` | TACTIC_STATES |
| `M *ᵥ v` → sum | `simp [Matrix.mulVec, dotProduct]` | R8 |
| sum over pairs / over `Fin 2` | `Fintype.sum_prod_type`, `Fin.sum_univ_two` | R9, R10 |
| entry of `A ⊗ₖ B` | `Matrix.kroneckerMap_apply` | R11 |
| entry of `1` / of `Pi.single` | `Matrix.one_apply`, `Pi.single_apply` | R12, R13 |
| entries of `c • !![…]`, `Matrix.of`, `Fin 2` sums, `if` | (simp does it) | R7, R14, R15 |
| `normSq z` → re/im | `Complex.normSq_apply` | R16 |
| re/im of casts and of `(↑√x)⁻¹` | (simp does it) | R17, R18 |
| products of `√2 / 2` → `√2 ^ 6 * (1 / 8)` | `ring_nf` | R19 |
| see the state | infoview | |
