# M127 · Z-rotations and the 2π sign: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`have`, `ext`, `fin_cases`, `rw [h]`, `norm_num`, `<;>`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). M126 (Hadamard gate) helps but is not required: every
matrix entry used here is repeated below. **New here:** Mathlib's complex exponential `Complex.exp`, real
numbers cast into `ℂ` and `push_cast`, `Real.pi`, complex conjugation as a ring map (`starRingEnd ℂ`), and
the unitary group of matrices.

The maths: $R_z(\theta) = \mathrm{diag}(e^{-i\theta/2}, e^{i\theta/2})$, a 2×2 complex matrix for a real angle
$\theta$. Diagonal matrices multiply entrywise and $e^{x}e^{y} = e^{x+y}$, so $R_z(a)R_z(b) = R_z(a+b)$. At
$\theta = 2\pi$ both entries are $e^{\mp i\pi} = -1$, so a full turn gives $-1$, not $1$ (the spinor sign).
$R_z(\theta)R_z(\theta)^\dagger = 1$ because $\overline{e^{z}} = e^{\bar z}$ and $\overline{i\theta/2} = -i\theta/2$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix (Fin 2) (Fin 2) ℂ` | 2×2 matrices with complex entries. Rows and columns are indexed by `Fin 2 = {0, 1}` |
| `!![a, b; c, d]` | the matrix with rows `a b` and `c d` |
| `M i j` | the entry in row `i`, column `j`, counted from 0 |
| `cexp z` | `Complex.exp z`, the complex exponential $e^z$ |
| `I` | `Complex.I`, the imaginary unit ($I^2 = -1$); in scope because of `open Complex` |
| `↑θ` | the real number `θ : ℝ` cast into `ℂ` (`Complex.ofReal θ`) |
| `(θ / 2 : ℂ)` in the source | cast `θ` to `ℂ` first, then halve it in `ℂ`; printed `↑θ / 2` |
| `↑(a + b)` vs `↑a + ↑b` | cast of a real sum vs sum of casts: equal (R4), but different text for `rw` and `ring` |
| `Real.pi`, `↑Real.pi` | the real number π, and its cast into `ℂ` |
| `-1` (a matrix) | minus the identity matrix `1`; after R6 it prints `-!![1, 0; 0, 1]` |
| `z⁻¹` | the inverse `1 / z`; `(cexp x)⁻¹` appears after R8 |
| `∑ j, f j` | the sum of `f j` over all `j : Fin 2`, i.e. `f 0 + f 1` (R13, R14) |
| `v ᵥ* M`, `![a, b]` | row vector `v` times matrix `M`; `![a, b]` is the vector with entries `a b`. Seen only if `simp` is not given R13, R14 (Traps) |
| `star M`, `Mᴴ` | the conjugate transpose: `Mᴴ i j = star (M j i)` |
| `(starRingEnd ℂ) z` | Lean's name for the complex conjugate `conj z`; `star z` on `ℂ` is the same thing |
| `unitaryGroup (Fin 2) ℂ` | the set of 2×2 complex `U` with `U * star U = 1` (R11) |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases` |
| `case «0».«1»` | the goal for entry (0, 1) |

---

## Part 1 · `Rz_add`

Statement: `Rz a * Rz b = Rz (a + b)` for real `a b`. Both sides are 2×2 literals after unfolding, so the
work is: multiply the literals, merge the products of exponentials, make the exponents agree.

**R1 · `simp only [D]` (or `rw [D]`)** changes the **goal**: a defined name applied to an argument is replaced
by its body with the argument substituted. Placeholders: `(t : ℝ)`, `D` defined by
`def D (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(t : ℂ), 0; 0, 1]`. `simp only [D]` unfolds every `D _`;
`rw [D]` unfolds the first one it finds (and every copy with the same argument).

| Before | After |
|---|---|
| `⊢ P (D t)` | `⊢ P !![↑t, 0; 0, 1]` |

**R2 · `Matrix.mul_fin_two`** changes the **goal**: the product of two `!![…]` literals becomes one literal
whose entries are the row-times-column sums. Lemma:
`!![a, b; c, d] * !![p, q; r, s] = !![a * p + b * r, a * q + b * s; c * p + d * r, c * q + d * s]`.
Placeholders: `{α : Type} [AddCommMonoid α] [Mul α] (a b c d p q r s : α)` (α has `+`, `0`, `*`; `ℂ`
qualifies). The `0` entries of a diagonal matrix survive as `x * 0`, `0 * 0` junk; `ring_nf` (R5) or `simp`
cleans it.

| Before | After |
|---|---|
| `⊢ P (!![a, b; c, d] * !![p, q; r, s])` | `⊢ P !![a * p + b * r, a * q + b * s; c * p + d * r, c * q + d * s]` |

**R3 · `rw [← Complex.exp_add]`** changes the **goal**. The lemma is `Complex.exp_add : cexp (x + y) = cexp x * cexp y`
and `←` uses it right to left, merging a product of exponentials into one. Placeholders: `(x y : ℂ)`. In
`simp only [..., ← Complex.exp_add]` it merges every such product at once.

| Before | After |
|---|---|
| `⊢ P (cexp x * cexp y)` | `⊢ P (cexp (x + y))` |

**R4 · `push_cast`** changes the **goal**: it moves the cast `ℝ → ℂ` inward through `+`, `*`, numerals, …
(lemmas `Complex.ofReal_add : ↑(r + s) = ↑r + ↑s`, `Complex.ofReal_mul`, `Complex.ofReal_ofNat`).
Placeholders: `(r s : ℝ)`. After unfolding `Rz (a + b)` the goal holds `↑(a + b)`; after unfolding
`Rz (2 * Real.pi)` it holds `↑(2 * Real.pi)`. Both must be pushed before `ring_nf` or a `have` can match.

| Before | After |
|---|---|
| `⊢ P ↑(r + s)` | `⊢ P (↑r + ↑s)` |
| `⊢ P ↑(2 * r)` | `⊢ P (2 * ↑r)` |

**R5 · `ring_nf`** changes the **goal**, here **closing** it. It rewrites every subterm built from `+ * - / ^`
and numerals into a normal form, also inside function arguments such as `cexp (…)` and inside `!![…]`
entries, and closes the goal when both sides become identical. Placeholders: `(f : ℂ → ℂ) (x y : ℂ)`.
Unlike `ring`, it does not fail when the goal is not a pure ring identity; it just normalises.

| Before | After |
|---|---|
| `⊢ f (x / 2 + y / 2) + 0 * 0 = f ((x + y) / 2)` | closed |

**W1** chains R1 → R2 → R3, then R4, then R5 on a phase gate `Ph φ = !![1, 0; 0, cexp (↑φ * I)]`. After the
`simp only` and `push_cast` the goal is (one line here, two in the infoview):

```lean-goal
⊢ !![1 * 1 + 0 * 0, 1 * 0 + 0 * cexp (↑b * I); 0 * 1 + cexp (↑a * I) * 0, 0 * 0 + cexp (↑a * I + ↑b * I)] = !![1, 0; 0, cexp ((↑a + ↑b) * I)]
```

and `ring_nf` closes it.

---

## Part 2 · `Rz_two_pi`

Statement: `Rz (2 * Real.pi) = -1`. Turn both sides into literals (R1 via `rw [Rz]`, R6), push the cast (R4),
prove that each diagonal exponential is `-1` as a separate `have`, substitute, and compare entries.

**R6 · `rw [Matrix.one_fin_two]`** changes the **goal**: the identity matrix `1` becomes the literal
`!![1, 0; 0, 1]`. Placeholders: `{α : Type} [Zero α] [One α]` (`ℂ` qualifies). In `-1` it rewrites the `1`,
leaving `-!![1, 0; 0, 1]`.

| Before | After |
|---|---|
| `⊢ P 1` | `⊢ P !![1, 0; 0, 1]` |

**R7 · `rw [show x = y by ring]`** changes the **goal**: it proves the equation `x = y` on the spot with `ring`
and rewrites with it. Use it to bring an exponent into the exact shape a lemma wants, here `↑π * I` for R9.
Placeholders: `(a : ℂ)`. The left side `x` must appear literally in the goal, so copy it from the infoview.

| Before | After |
|---|---|
| `⊢ P (2 * a / 2 * I)` | `⊢ P (a * I)` |

**R8 · `rw [Complex.exp_neg]`** changes the **goal**. Lemma: `cexp (-x) = (cexp x)⁻¹`. Placeholders: `(x : ℂ)`.
For the entry `cexp (-(…) * I)` first move the minus outside with R7: `-(t) * I = -(t * I)`.

| Before | After |
|---|---|
| `⊢ P (cexp (-x))` | `⊢ P (cexp x)⁻¹` |

**R9 · `rw [Complex.exp_pi_mul_I]`** changes the **goal**. Lemma (Euler): `cexp (↑Real.pi * I) = -1`. No
placeholders. The exponent must be exactly `↑Real.pi * I`, not `I * ↑Real.pi` or `2 * ↑Real.pi / 2 * I` (R7).
After R8 and R9 the goal is `(-1)⁻¹ = -1`, which `norm_num` closes.

| Before | After |
|---|---|
| `⊢ P (cexp (↑Real.pi * I))` | `⊢ P (-1)` |

**R10 · `simp` on an entry of `-!![…]`** changes the **goal**: `Matrix.neg_apply` (`(-M) i j = -M i j`) and the
literal-entry lemmas (`Matrix.of_apply`, `Matrix.cons_val_…`) evaluate the entry. Placeholders:
`{α : Type} [Neg α] (a b c d : α)`. After `ext i j; fin_cases i <;> fin_cases j` this is how each entry of
`-!![1, 0; 0, 1]` is computed; `simp` then also closes `-1 = -1` and `0 = -0`.

| Before | After |
|---|---|
| `⊢ P ((-!![a, b; c, d]) 0 1)` | `⊢ P (-b)` |

**W2** (two quarter turns of the phase) chains R3 → R7 → R9:

```lean-goal
⊢ cexp (↑Real.pi / 2 * I) * cexp (↑Real.pi / 2 * I) = -1
⊢ cexp (↑Real.pi / 2 * I + ↑Real.pi / 2 * I) = -1
⊢ cexp (↑Real.pi * I) = -1
```

and the last `rw` closes the goal by `rfl`.

---

## Part 3 · `Rz_unitary`

Statement: `Rz θ ∈ Matrix.unitaryGroup (Fin 2) ℂ`. Turn the membership into `Rz θ * (Rz θ)ᴴ = 1` (R11, R12),
split into entries (`ext`, `fin_cases`), and let one `simp` call per entry multiply out (R13, R14, R15),
push the conjugation inside the exponential (R16–R19), merge (R3) and cancel (R20, R21).

**R11 · `rw [Matrix.mem_unitaryGroup_iff]`** changes the **goal**: membership becomes an equation.
Placeholders: `(M : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `⊢ M ∈ unitaryGroup (Fin 2) ℂ` | `⊢ M * star M = 1` |

**R12 · `rw [Matrix.star_eq_conjTranspose]`** changes the **goal**: `star M` is written as the conjugate
transpose `Mᴴ`. Placeholders: `(M : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `⊢ P (star M)` | `⊢ P Mᴴ` |

**R13 · `Matrix.mul_apply`** changes the **goal**: an entry of a product becomes a sum over the middle index,
$(MN)_{ik} = \sum_j M_{ij} N_{jk}$. Placeholders: `{α : Type} [Mul α] [AddCommMonoid α]`
(`ℂ` qualifies), `(M N : Matrix (Fin 2) (Fin 2) α) (i k : Fin 2)`. Give it to `simp` by name.

| Before | After |
|---|---|
| `⊢ P ((M * N) i k)` | `⊢ P (∑ j, M i j * N j k)` |

**R14 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms. Placeholders:
`{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`. Give it to `simp` by name.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R15 · `Matrix.conjTranspose_apply`** changes the **goal**: entry `(i, j)` of `Mᴴ` becomes the conjugate of
entry `(j, i)`. `simp` applies it by itself. Placeholders: `(M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2)`.

| Before | After |
|---|---|
| `⊢ P (Mᴴ i j)` | `⊢ P (star (M j i))` |

**R16 · `rw [← Complex.exp_conj]`** changes the **goal**. Lemma: `Complex.exp_conj : cexp (conj x) = conj (cexp x)`;
right to left it moves the conjugate inside the exponential, where R17–R19 can evaluate it. `simp` does not
do this by itself (it would go the other way): pass `← Complex.exp_conj`. Placeholders: `(x : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (cexp x))` | `⊢ P (cexp ((starRingEnd ℂ) x))` |

**R17 · `map_neg`, `map_mul`, `map_div₀`** change the **goal**: conjugation is a ring map (a function that
respects `+`, `*`, `-`, `/`), so it distributes. `simp` applies them by itself. Lemmas, for a ring map `f`:
`f (-x) = -f x`, `f (x * y) = f x * f y`, `f (x / y) = f x / f y`. Placeholders: `(x y z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (-(x / y * z)))` | `⊢ P (-((starRingEnd ℂ) x / (starRingEnd ℂ) y * (starRingEnd ℂ) z))` |

**R18 · `Complex.conj_ofReal`, `Complex.conj_I`** change the **goal**: `conj ↑r = ↑r` (a real number is its own
conjugate) and `conj I = -I`. `simp` applies them by itself. Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) ↑r * (starRingEnd ℂ) I)` | `⊢ P (↑r * -I)` |

**R19 · `map_ofNat`** changes the **goal**: a ring map fixes every numeral literal `2, 3, …`, so
`conj 2 = 2`. `simp` does **not** apply it by itself: name it. Placeholders: none (the numeral is `2` here,
from the `/ 2` in the exponent).

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) 2)` | `⊢ P 2` |

**R20 · `neg_add_cancel`** (and `add_neg_cancel`) change the **goal**: `-a + a = 0` (and `a + -a = 0`).
`simp` applies them by itself once the two exponents are merged by R3. Placeholders: `{α : Type} [AddGroup α] (a : α)`
(α has `+`, `-`, `0`; `ℂ` qualifies).

| Before | After |
|---|---|
| `⊢ P (-a + a)` | `⊢ P 0` |

**R21 · `Complex.exp_zero`** changes the **goal**: `cexp 0 = 1`. `simp` applies it by itself.

| Before | After |
|---|---|
| `⊢ P (cexp 0)` | `⊢ P 1` |

**W3: the `map_ofNat` trap.** On `cexp (↑t / 3 * I) * conj (cexp (↑t / 3 * I)) = 1`, `simp [← Complex.exp_conj]`
does R16–R18 but stops at the numeral:

```lean-goal
⊢ cexp (↑t / 3 * I) * cexp (-(↑t / (starRingEnd ℂ) 3 * I)) = 1
```

`simp [map_ofNat, ← Complex.exp_add]` (R19, R3, then R20, R21) closes it. Passing all of them in one `simp`
call from the start works too.

---

## Traps

- `cexp` is only notation for `Complex.exp`; search lemmas under `Complex.exp_…`.
- `↑(a + b)` and `↑a + ↑b` are different text. `ring_nf` treats `↑(a + b)` as an unknown, so run
  `push_cast` (R4) first, or `ring_nf` leaves two sides that look equal but are not syntactically equal.
- In a `have` about the goal, write the cast out: `(Real.pi : ℂ)`. A bare `Real.pi` stays in `ℝ` and the
  `have` will not match the complex goal.
- A `have` must match the goal **after** `push_cast`: copy the entry from the infoview
  (`cexp (-(2 * ↑Real.pi / 2) * I)`), not from the definition of `Rz`.
- `Complex.exp_pi_mul_I` needs exactly `↑Real.pi * I`. Reshape with `rw [show … by ring]` (R7).
  For the negative entry, the minus must end up outside the product before R8: `-(↑Real.pi * I)`.
- `simp` stops at `(starRingEnd ℂ) 2` unless you give it `map_ofNat` (R19, W3).
- In `Rz_unitary`, a plain `simp [Rz]` turns each entry into a row-vector product it cannot finish,
  `(![cexp (-(↑θ / 2 * I)), 0] ᵥ* !![…]ᴴ) 0 = 1`. Name `Matrix.mul_apply` and `Fin.sum_univ_two` (R13, R14)
  in the same `simp` call so the product is expanded entrywise instead.
- `simp` also rewrites `-(x) * I` to `-(x * I)` on its own, so in `Rz_unitary` the exponents appear as
  `-(↑θ / 2 * I)`, not in the `-(↑θ / 2) * I` form of the definition.
- `simp` pushes `conj` outward through `cexp` by default; give it `← Complex.exp_conj` (R16) so the
  conjugate goes inside where the exponents can cancel.
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases`, use `<;>` or `all_goals`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold `Rz θ` | `simp only [Rz]` / `rw [Rz]` | R1 |
| multiply two `!![…]` literals | `Matrix.mul_fin_two` | R2 |
| `cexp x * cexp y → cexp (x + y)` | `← Complex.exp_add` | R3 |
| `↑(a + b) → ↑a + ↑b`, `↑(2 * x) → 2 * ↑x` | `push_cast` | R4 |
| make exponents agree, clear `0 * 0` | `ring_nf` | R5 |
| `1 → !![1, 0; 0, 1]` | `rw [Matrix.one_fin_two]` | R6 |
| reshape an exponent | `rw [show x = y by ring]` | R7 |
| `cexp (-x) → (cexp x)⁻¹` | `rw [Complex.exp_neg]` | R8 |
| `cexp (↑π * I) → -1` | `rw [Complex.exp_pi_mul_I]` | R9 |
| `(-1)⁻¹ = -1` | `norm_num` | TACTIC_STATES |
| entries of `-!![…]` | `ext i j; fin_cases i <;> fin_cases j <;> simp` | R10 |
| unitary → equation | `rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]` | R11, R12 |
| entries of products | `simp [names, Matrix.mul_apply, Fin.sum_univ_two]` | R13, R14 |
| `Mᴴ i j → star (M j i)` | automatic in `simp` | R15 |
| `conj (cexp x) → cexp (conj x)` | `← Complex.exp_conj` | R16 |
| conj of `-`, `*`, `/`, `↑r`, `I` | automatic in `simp` | R17, R18 |
| `conj 2 → 2` | `map_ofNat` | R19 |
| `-a + a → 0`, `cexp 0 → 1` | automatic in `simp` | R20, R21 |
| see the state | infoview | |
