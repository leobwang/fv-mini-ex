# H080 · The swap test: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`have`, `intro`, `rw [h]`, `ring`, `norm_num`, `exact`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's kets and bras (`Ket d`, `Bra d`,
`〈ψ‖φ〉`), Mathlib's complex numbers (`Complex.normSq`, `.re`, the conjugate `starRingEnd ℂ`, the norm
`‖z‖`), real numbers cast into `ℂ` with `Real.sqrt`, finite sums `∑` over a product type `d × d`, and the
tactic `linear_combination`.

The physics. Three registers: an ancilla qubit (`Fin 2 = {0, 1}`) and two copies of a `d`-level system.
A state of all three is a function `v : Fin 2 × d × d → ℂ` (amplitude of basis state `|a⟩|i⟩|j⟩` is
`v (a, i, j)`). The circuit is `hA` (Hadamard on the ancilla), then `cswap` (swap the registers when the
ancilla is 1), then `hA` again. With input `|0⟩|ψ⟩|φ⟩`, the final amplitude at `(0, i, j)` is
$\tfrac12(\psi_i\varphi_j + \psi_j\varphi_i)$, and the probability of reading ancilla 0 is
$\sum_{i,j} \bigl|\tfrac12(\psi_i\varphi_j + \psi_j\varphi_i)\bigr|^2 = \tfrac12\bigl(1 + |\langle\psi|\varphi\rangle|^2\bigr)$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid M]`
  is a requirement on `M` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ket d` | a physlib ket: a unit vector of amplitudes indexed by the finite type `d` (`[Fintype d]`, shown as `inst✝ : Fintype d`) |
| `ψ i` | the `i`-th amplitude of the ket `ψ`, a complex number (a ket coerces to a function `d → ℂ`) |
| `ψ.vec i` | the same amplitude, read through the underlying vector field `vec` (R18) |
| `↑ψ` (where a bra is expected) | the bra `⟨ψ|` = `Ket.to_bra ψ`, whose amplitudes are the conjugates `conj (ψ i)` (R17) |
| `dot (↑ψ) φ` | how Lean prints `〈ψ‖φ〉`, the inner product $\sum_x \overline{\psi_x}\,\varphi_x$ (R13) |
| `(starRingEnd ℂ) z` | Lean's name for the complex conjugate $\bar z$ |
| `Complex.normSq z` | $\lvert z\rvert^2 = (\mathrm{re}\,z)^2 + (\mathrm{im}\,z)^2$, a **real** number |
| `‖z‖` | the norm (absolute value) $\lvert z\rvert$, a real number; `‖z‖ ^ 2 = normSq z` (R23) |
| `z.re`, `z.im` | real and imaginary parts, real numbers |
| `√x` | `Real.sqrt x`, the nonnegative square root of a real `x ≥ 0` (a real number) |
| `↑x`, `↑√2` | the real number `x` (or `Real.sqrt 2`) cast into `ℂ` |
| `2⁻¹` | `1 / 2`; `simp` rewrites `1 / a` to `a⁻¹` |
| `∑ q, f q` | the sum of `f q` over every `q` of a finite type (`Finset.univ`, the set of all elements) |
| `∑ i ∈ s, f i` | the sum over a finite set `s` (lemma statements are written this way; `s = Finset.univ` here) |
| `Fin 2 × d × d` | triples; `×` groups to the right, so it is `Fin 2 × (d × d)` |
| `p.1`, `p.2`, `p.2.1` | projections: for `p = (a, i, j)`, `p.1 = a`, `p.2 = (i, j)`, `p.2.1 = i` |
| `(0, i, j)` | how Lean prints `(0, (i, j))` |
| `x_1`, `x✝` | names Lean invents for bound variables; `x✝` cannot be typed |
| `if 1 = 0 then …` | the `1` and `0` are in `Fin 2`, so the test is false and `simp` takes the `else` branch (R2) |

---

## Part 1 · `swap_amp` (MILESTONE 1)

Statement: the final amplitude at `(0, (i, j))` equals `1 / 2 * (ψ i * φ j + ψ j * φ i)`. You unfold the
three circuit stages, evaluate the `if`s, and use $\tfrac1{\sqrt2}\cdot\tfrac1{\sqrt2} = \tfrac12$.

**R1 · `simp only [f]`** changes the **goal**: a defined name `f := fun p => …` applied to a pair is replaced
by its body, β-reduced, with the projections of the pair evaluated. In the exercise,
`simp only [hA, cswap, input]` unfolds all three stages at once; tests such as `(0, i, j).1 = 0` come out as
`True`. Placeholders: `{α β : Type} (v : α × β → ℂ) (a : α) (b : β)`, with
`swapArg v := fun p => v (p.2, p.1)`.

| Before | After |
|---|---|
| `⊢ P (swapArg v (b, a))` | `⊢ P (v (a, b))` |

**R2 · `simp`** changes the **goal**: it clears the `if`s. `if True then x else y` becomes `x`; `(1 : Fin 2) = 0`
is decided false, so its `if` becomes the `else` branch; `1 * x` and `x * 0`, `0 + x` are cleaned up; `-1 * x`
becomes `-x`. It also writes `1 / 2` as `2⁻¹`. Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((if True then a else b) + (if 1 = 0 then 1 else -1) * b)` | `⊢ P (a + -b)` |

**R3 · `rw [← mul_inv]`** changes the **goal**. The lemma is `mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹`, used right to
left. Placeholders: `{α : Type} [DivisionCommMonoid α] (a b : α)` (α has a commutative `*` and `⁻¹`; `ℂ`, `ℝ`
qualify).

| Before | After |
|---|---|
| `⊢ P (a⁻¹ * b⁻¹)` | `⊢ P (a * b)⁻¹` |

**R4 · `rw [← Complex.ofReal_mul]`** changes the **goal**. The lemma is `↑(x * y) = ↑x * ↑y`; right to left it
moves `*` inside the cast, so a lemma about real numbers can apply. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑x * ↑y)` | `⊢ P ↑(x * y)` |

**R5 · `rw [Real.mul_self_sqrt]`** changes the **goal list**. The lemma is `0 ≤ x → √x * √x = x`: the goal is
rewritten and a side goal `0 ≤ x` is added. `rw [Real.mul_self_sqrt (by norm_num)]` proves it on the spot.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (√x * √x)` | `⊢ P x`, `⊢ 0 ≤ x` |

**R6 · `norm_num`** **closes** a goal made of numerals, `⁻¹`, `/` and casts of numerals, such as
`(↑5)⁻¹ = 1 / 5`. It finishes the √2 fact after R3–R5.

**R7 · `linear_combination c * h`** **closes** an equation `L = R` from a hypothesis `h : l = r` when
`L - R - c * (l - r)` simplifies to `0` by `ring`. Use it when the goal is "`h` times something, rearranged".
Placeholders: `(s t a : ℂ) (h : s * s = t)`, coefficient `a`. In the exercise `h` is the √2 fact and the
coefficient is the symmetrised product.

| Before | After |
|---|---|
| `h : s * s = t ⊢ s * (s * a) = t * a` | no goals |

**W1.** Part 1's pattern on a √3 butterfly (`mixA`, `start` in the guide): after `simp only [mixA, start]` and `simp`, the goal is

```lean-goal
⊢ (↑√3)⁻¹ * ((↑√3)⁻¹ * (a + b) + (↑√3)⁻¹ * (a + -b)) = 2 / 3 * a
```

and `linear_combination (2 * a) * h3` closes it, with `h3 : (√3 : ℂ)⁻¹ * (√3 : ℂ)⁻¹ = 1 / 3`.

---

## Part 2 · `sum_normSq_prod` (MILESTONE 2)

Statement: `∑ q : d × d, Complex.normSq (ψ q.1 * φ q.2) = 1`, i.e.
$\sum_{i,j}|\psi_i|^2|\varphi_j|^2 = \bigl(\sum_i|\psi_i|^2\bigr)\bigl(\sum_j|\varphi_j|^2\bigr) = 1\cdot 1$.

**R8 · `Complex.normSq_mul`** changes the **goal**: `normSq (z * w) = normSq z * normSq w`. Placeholders:
`(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (Complex.normSq (z * w))` | `⊢ P (Complex.normSq z * Complex.normSq w)` |

**R9 · `simp only [Fintype.sum_prod_type]`** changes the **goal**: a sum over pairs becomes a double sum,
`∑ x, f x = ∑ x, ∑ y, f (x, y)`; `simp only` also reduces `(x, y).1` to `x`. Placeholders:
`{α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (f : α → β → M)` (`M` has a commutative `+` with
`0`: `ℝ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ P (∑ q, f q.1 q.2)` | `⊢ P (∑ x, ∑ x_1, f x x_1)` |

**R10 · `simp only [← Finset.sum_mul_sum]`** changes the **goal**. The lemma is
`(∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j`; right to left it factors a double sum whose
term is a product. Placeholders: `{α β R : Type} [Fintype α] [Fintype β] [NonUnitalNonAssocSemiring R]`
(`R` has `+`, `*` and distributivity; `ℝ`, `ℂ` qualify), `(f : α → R) (g : β → R)`.

| Before | After |
|---|---|
| `⊢ P (∑ a, ∑ b, f a * g b)` | `⊢ P ((∑ i, f i) * ∑ j, g j)` |

**R11 · `Ket.normalized`** changes the **goal**: for `ψ : Ket d`, `∑ x, Complex.normSq (ψ x) = 1`.
Placeholders: `{d : Type} [Fintype d] (ψ : Ket d)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, Complex.normSq (ψ x))` | `⊢ P 1` |

**R12 · `mul_one`** changes the **goal**: `a * 1 = a`. Placeholders: `{α : Type} [MulOneClass α] (a : α)`
(α has `*` and `1`). It turns the last `1 * 1 = 1` into `1 = 1`, which `simp only` closes by `rfl`.

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

**W2.** R9, R10, R11, R12 in a row on a ket over `d` and one over `e`:

```lean-goal
⊢ ∑ q, Complex.normSq (ψ q.1) * Complex.normSq (χ q.2) = 1
⊢ ∑ x, ∑ x_1, Complex.normSq (ψ x) * Complex.normSq (χ x_1) = 1
⊢ (∑ i, Complex.normSq (ψ i)) * ∑ j, Complex.normSq (χ j) = 1
⊢ 1 * 1 = 1
```

---

## Part 3 · `cross_term` (MILESTONE 3)

Statement: `∑ q : d × d, (ψ q.1 * φ q.2 * starRingEnd ℂ (ψ q.2 * φ q.1)).re = ‖〈ψ‖φ〉‖ ^ 2`. First prove the
complex identity $\sum_{i,j}\psi_i\varphi_j\overline{\psi_j\varphi_i} = \overline{\langle\psi|\varphi\rangle}\,\langle\psi|\varphi\rangle$
(both sides are $\sum_{i,j} \psi_i\overline{\varphi_i}\,\overline{\psi_j}\varphi_j$), then take real parts.

**R13 · `simp only [Braket.dot]`** changes the **goal**: it unfolds `〈ψ‖φ〉 = ∑ x, ↑ψ x * φ x`, where `↑ψ x` is
the amplitude of the bra, $\overline{\psi_x}$. Placeholders: `{d : Type} [Fintype d] (ψ φ : Ket d)`.

| Before | After |
|---|---|
| `⊢ P (dot (↑ψ) φ)` | `⊢ P (∑ x, ↑ψ x * φ x)` |

**R14 · `simp only [map_sum]`** changes the **goal**: `g (∑ x ∈ s, f x) = ∑ x ∈ s, g (f x)` for any additive map
`g`; conjugation is one. Placeholders: `{ι : Type} [Fintype ι] (f : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (∑ i, f i))` | `⊢ P (∑ x, (starRingEnd ℂ) (f x))` |

**R15 · `simp only [Finset.sum_mul_sum]`** (R10's lemma, left to right) changes the **goal**: a product of two
sums becomes a double sum. Placeholders as in R10.

| Before | After |
|---|---|
| `⊢ P ((∑ a, f a) * ∑ b, g b)` | `⊢ P (∑ i, ∑ j, f i * g j)` |

**R16 · `refine Finset.sum_congr rfl fun i _ => ?_`** changes the **goal and the context**: to prove two sums
over the same set equal, prove the terms equal for each `i`. `Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x)
→ s₁.sum f = s₂.sum g`; `rfl` proves `s₁ = s₂`, and `_` names the membership hypothesis `x✝ : i ∈ Finset.univ`.
For a double sum nest it: `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` (W3).
Placeholders: `{ι M : Type} [Fintype ι] [AddCommMonoid M] (f g : ι → M)`.

| Before | After |
|---|---|
| `⊢ ∑ i, f i = ∑ i, g i` | `i : ι, x✝ : i ∈ Finset.univ ⊢ f i = g i` |

**R17 · `simp [Ket.to_bra, Bra.apply]`** changes the **goal**: the bra amplitude `↑ψ x` becomes
`conj (ψ x)`. `Ket.to_bra ψ` is the bra with vector `conj ψ`; `Bra.apply` reads a bra's amplitude through its
vector. Placeholders: `{d : Type} [Fintype d] (ψ : Ket d) (x : d)`.

| Before | After |
|---|---|
| `⊢ P (↑ψ x)` | `⊢ P ((starRingEnd ℂ) (ψ x))` |

**R18 · `Ket.apply`** changes the **goal**: `ψ x = ψ.vec x`. Add it to the R17 `simp` call so every amplitude
is written the same way, `ψ.vec x`, and `ring` sees equal terms as equal. Placeholders as in R17.

| Before | After |
|---|---|
| `⊢ P (ψ x)` | `⊢ P (ψ.vec x)` |

**R19 · `map_mul`** changes the **goal**: `conj (a * b) = conj a * conj b` (any multiplicative map). `simp`
applies it by itself, so the R17 `simp` call does this too. Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (a * b))` | `⊢ P ((starRingEnd ℂ) a * (starRingEnd ℂ) b)` |

**W3.** R15, then R16 nested twice; the term goal is closed by `ring`:

```lean-goal
⊢ ∑ i, ∑ j, b j * a i = (∑ i, a i) * ∑ j, b j
⊢ ∑ i, ∑ j, b j * a i = ∑ i, ∑ j, a i * b j
⊢ b j * a i = a i * b j
```

With the complex identity `h` in hand, take real parts:

**R20 · `rw [← Complex.re_sum]`** changes the **goal**. The lemma is `(∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re`;
right to left it pulls `.re` out of the sum, so `rw [h]` can then replace the complex sum. Placeholders:
`{ι : Type} [Fintype ι] (f : ι → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, (f i).re)` | `⊢ P (∑ i, f i).re` |

**R21 · `rw [← Complex.normSq_eq_conj_mul_self]`** changes the **goal**. The lemma is
`↑(normSq z) = conj z * z` (the cast of a real into `ℂ`); right to left it recognises $\bar z z$.
Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) z * z)` | `⊢ P ↑(Complex.normSq z)` |

**R22 · `Complex.ofReal_re`** changes the **goal**: `(↑r).re = r`. Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑r).re` | `⊢ P r` |

**R23 · `Complex.sq_norm`** changes the **goal**: `‖z‖ ^ 2 = normSq z`. After it both sides are the same and
`rw` closes the goal by `rfl`. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (‖z‖ ^ 2)` | `⊢ P (Complex.normSq z)` |

**W4.** R21, R22, R23 in a row (the last `rw` closes the goal):

```lean-goal
⊢ ((starRingEnd ℂ) z * z).re = ‖z‖ ^ 2
⊢ (↑(Complex.normSq z)).re = ‖z‖ ^ 2
⊢ Complex.normSq z = ‖z‖ ^ 2
```

---

## Part 4 · `swap_test`

Statement: `∑ q : d × d, Complex.normSq (hA (cswap (hA (input ψ φ))) (0, q)) = (1 + ‖〈ψ‖φ〉‖ ^ 2) / 2`. Expand
each term with `swap_amp` and $|x+y|^2 = |x|^2 + |y|^2 + 2\,\mathrm{Re}(x\bar y)$, then the three milestones
evaluate the three sums: $\tfrac14(1 + 1 + 2|\langle\psi|\varphi\rangle|^2)$.

**R24 · `Complex.normSq_add`** changes the **goal**:
`normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re`. Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (Complex.normSq (z + w))` | `⊢ P (Complex.normSq z + Complex.normSq w + 2 * (z * (starRingEnd ℂ) w).re)` |

**R25 · `norm_num` on `normSq` of a numeral** changes the **goal**: `normSq (1 / 2)` becomes `1 / 4`. On the
per-term goal of `swap_test` it also splits the remaining `normSq (a * b)` into `normSq a * normSq b` and
expands `.re` of a product into real and imaginary parts (`(z * w).re = z.re * w.re - z.im * w.im`, and
`conj` flips the sign of `.im`); both sides expand the same way, and `ring` closes the result.

| Before | After |
|---|---|
| `⊢ P (Complex.normSq (1 / 2))` | `⊢ P (1 / 4)` |

**R26 · `exact Fintype.sum_equiv (Equiv.prodComm α β) _ _ fun _ => rfl`** **closes** an equation between a sum
over `α × β` and the same sum over `β × α` with the pair flipped. `Equiv.prodComm α β : α × β ≃ β × α` is the
bijection `(a, b) ↦ (b, a)` (`≃` means a bijection with its inverse). `Fintype.sum_equiv e f g hfg` proves
`∑ x, f x = ∑ y, g y` from `hfg : ∀ x, f x = g (e x)`; here each `hfg x` holds by `rfl`. With `α = β = d` it
shows that the swapped norm sum equals the unswapped one. Placeholders:
`{α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (f : α → β → M)`.

| Before | After |
|---|---|
| `⊢ ∑ q, f q.1 q.2 = ∑ q, f q.2 q.1` | no goals |

**R27 · `simp only [e]`** with `e : ∀ q, f q = g q` changes the **goal**: it rewrites **inside** a `∑`, under
the bound variable, which `rw [e]` cannot do (`rw` reports that it did not find the pattern: inside `∑ q, f q`
the `q` is a bound variable, and `rw` does not rewrite terms that mention one). Placeholders: `{ι : Type} [Fintype ι] (f g : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ q, f q)` | `⊢ P (∑ x, g x)` |

**R28 · `simp only [← Finset.sum_div]`** changes the **goal**. The lemma is
`(∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a`; right to left it pulls a common `/ a` out. Placeholders:
`{ι : Type} [Fintype ι] (f : ι → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i / a)` | `⊢ P ((∑ i, f i) / a)` |

**R29 · `simp only [Finset.sum_add_distrib]`** changes the **goal**:
`∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑ x ∈ s, g x`. Placeholders:
`{ι M : Type} [Fintype ι] [AddCommMonoid M] (f g : ι → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, (f i + g i))` | `⊢ P (∑ x, f x + ∑ x, g x)` |

**R30 · `simp only [← Finset.mul_sum]`** changes the **goal**. The lemma is
`a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; right to left it pulls a constant factor out. Placeholders:
`{ι : Type} [Fintype ι] (f : ι → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, a * f i)` | `⊢ P (a * ∑ i, f i)` |

**W5.** R27, R28, R29, then R30 (which closes this goal):

```lean-goal
⊢ ∑ i, u i = (∑ i, f i + 2 * ∑ i, g i) / 4
⊢ ∑ x, (f x + 2 * g x) / 4 = (∑ i, f i + 2 * ∑ i, g i) / 4
⊢ (∑ i, (f i + 2 * g i)) / 4 = (∑ i, f i + 2 * ∑ i, g i) / 4
⊢ (∑ x, f x + ∑ x, 2 * g x) / 4 = (∑ x, f x + 2 * ∑ i, g i) / 4
```

After R27–R30 and substituting the three milestones, `simp only [cross_term, sum_normSq_prod, h1]` leaves
`(1 + 1 + 2 * ‖dot (↑ψ) φ‖ ^ 2) / 4 = (1 + ‖dot (↑ψ) φ‖ ^ 2) / 2`, which `ring` closes.

---

## Traps

- `rw [e]` with `e : ∀ q, …` does not rewrite under `∑ q, …`: use `simp only [e]` (R27).
- Do not type `(ψ : Bra d) x` yourself: Lean then reads `x` as a ket (a bra applied to a ket is `〈ψ‖x〉`). The
  bra amplitude `↑ψ x` only appears by unfolding `Braket.dot` (R13), and `simp [Ket.to_bra, Bra.apply]`
  evaluates it (R17).
- `Finset.sum_mul_sum` goes both ways: right to left factors a double sum (Part 2, R10), left to right expands
  a product of sums (Part 3, R15). Using the wrong direction makes `simp only` fail with no progress.
- After R17–R19 mix `ψ x` and `ψ.vec x`, `ring` treats them as different unknowns. Add `Ket.apply` (R18) so
  only `ψ.vec x` remains.
- `rw [← sum_normSq_prod ψ φ]` rewrites **every** `1` in the goal into the sum. It works for
  `… = 1` only because the goal has exactly one `1`.
- `simp` writes `1 / 2` as `2⁻¹`; `linear_combination` does not care (its final check is `ring`), but `rw [h]`
  with an `h` stated with `1 / 2` would no longer match.
- The `have h2` (√2 fact) and `have e` / `have h1` belong to one proof only: a milestone's `have` is not
  visible in `swap_test`.
- `Complex.normSq` is real-valued, so the sums in Parts 2 and 4 live in `ℝ`, and `cross_term` takes `.re`
  of a complex sum: pull `.re` out (R20) before rewriting with the complex identity.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold the circuit stages | `simp only [hA, cswap, input]` | R1 |
| clear `if True`, `if 1 = 0` on `Fin 2` | `simp` | R2 |
| $(\sqrt2)^{-1}(\sqrt2)^{-1} = 1/2$ | `rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num` | R3–R6 |
| close "goal = c · hypothesis, rearranged" | `linear_combination c * h` | R7 |
| `normSq (z * w)` | `Complex.normSq_mul` | R8 |
| `normSq (z + w)` | `Complex.normSq_add` | R24 |
| sum over `α × β` → double sum | `simp only [Fintype.sum_prod_type]` | R9 |
| factor / expand `(∑ f) * (∑ g)` | `← Finset.sum_mul_sum` / `Finset.sum_mul_sum` | R10, R15 |
| `∑ normSq (ψ x) = 1` | `Ket.normalized` | R11 |
| `a * 1` | `mul_one` | R12 |
| unfold `〈ψ‖φ〉` | `simp only [Braket.dot]` | R13 |
| conj of a sum / product | `map_sum` / `map_mul` | R14, R19 |
| sums equal termwise | `refine Finset.sum_congr rfl fun i _ => ?_` | R16 |
| evaluate bra and ket amplitudes | `simp [Ket.to_bra, Bra.apply, Ket.apply]` | R17, R18 |
| `.re` out of a sum | `rw [← Complex.re_sum]` | R20 |
| `conj z * z` → `‖z‖ ^ 2` | `rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.sq_norm]` | R21–R23 |
| `normSq (1 / 2)` | `norm_num` | R25 |
| reindex a sum by `(i, j) ↦ (j, i)` | `Fintype.sum_equiv (Equiv.prodComm d d) _ _ fun _ => rfl` | R26 |
| rewrite under `∑` | `simp only [e]` | R27 |
| pull `/ a`, split `+`, pull `a *` | `← Finset.sum_div`, `Finset.sum_add_distrib`, `← Finset.mul_sum` | R28–R30 |
| see the state | infoview | |
