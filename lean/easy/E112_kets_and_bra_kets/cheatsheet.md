# E112 · Kets and bra-kets: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's pure states `Ket d` and `Bra d`
(file `QuantumInfo.States.Pure.Braket`), the bra-ket `〈φ‖ψ〉`, the basis kets `Ket.basis i`, and the
Mathlib pieces they are built from: complex numbers `ℂ`, complex conjugation, the norm `‖z‖`, `Real.sqrt`,
and finite sums `∑ x, f x`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{d : Type}` is any type. A bracket such as `[Fintype d]` is a
  requirement on `d` (a *type class*): `[Fintype d]` says `d` is finite, so `∑ x : d` exists;
  `[DecidableEq d]` says `i = j` can be decided, so `if i = j then … else …` can be written. `Fin n`
  (the numbers `0, …, n-1`) meets both. Each entry says which familiar types meet its other brackets.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

physlib models a `d`-level quantum system by a finite index type `d` (for a qubit, `d = Fin 2`, basis
`|0⟩, |1⟩`). A state is a complex vector `v : d → ℂ` with $\sum_x |v_x|^2 = 1$.

| You see | It means |
|---|---|
| `Ket d` | a structure with fields `vec : d → ℂ` and `normalized' : ∑ x, ‖vec x‖ ^ 2 = 1`: a unit column vector \|ψ⟩ |
| `Bra d` | the same two fields, kept as a separate type: a unit row vector ⟨ξ\| (its entries are already conjugated) |
| `ψ x` | entry `x` of `ψ`, i.e. `ψ.vec x` (`Ket.apply`, `Bra.apply`, R3). A ket can be applied like a function |
| `⇑ψ` | `ψ` used as the function `d → ℂ` (the coercion that makes `ψ x` work) |
| `↑φ` | the ket `φ` turned into a bra: `Ket.to_bra φ`, entries conjugated (R2) |
| `{ vec := v, normalized' := ⋯ }` | the structure literal with vector `v`; `⋯` hides the normalization proof |
| `⟨v, h⟩` | how you *write* that literal: anonymous constructor, fields in order (R13) |
| `fun j_1 => if j = j_1 then …` | a bound variable renamed `j_1` because `j` is already in the context; same function as `fun x => if j = x then …` |
| `〈ξ‖ψ〉`, printed `dot ξ ψ` | `Braket.dot ξ ψ = ∑ x, ξ x * ψ x`, the bra-ket ⟨ξ\|ψ⟩. With a ket `φ` on the left: `dot (↑φ) ψ` |
| `Ket.basis i` | the basis ket \|i⟩, vector `fun j => if i = j then 1 else 0` (R5) |
| `∑ x, f x` | $\sum_{x \in d} f(x)$, the sum over all of `d` (`Finset.univ`, the finite set of every element of `d`) |
| `Finset.univ.card`, `Fintype.card d` | the number of elements of `d` |
| `n • c` | `c` added to itself `n` times (`n : ℕ`, "n-fold sum") |
| `(starRingEnd ℂ) z` | Lean's name for the complex conjugate $\bar z$ |
| `(starRingEnd (d → ℂ)) f` | the vector `f` conjugated entry by entry (R4) |
| `‖z‖` | the norm: for `z : ℂ` the modulus $\lvert z\rvert$, for `r : ℝ` the absolute value |
| `\|r\|` | the absolute value of a real `r` |
| `√x`, `↑√2` | `Real.sqrt x`, a real number; `↑√2` is that real cast into `ℂ` |
| `(↑√2)⁻¹` | $1/\sqrt 2$ as a complex number |
| `![a, b]` | the vector with entries `a, b` (Part W) |

---

## Part 1 · `basis_orthonormal`

Statement: for basis kets of any finite `d`, `〈Ket.basis i‖Ket.basis j〉 = if i = j then 1 else 0`, i.e.
$\langle i|j\rangle = \delta_{ij}$. Unfold the bra-ket into a sum (R1), unfold the bra and the kets into
their vectors (R2–R5), then evaluate the sum (R6–R12). In practice all of this is **one** `simp` call that
names the definitions of R1–R3 and R5; `simp` applies R4 and R6–R12 by itself.

### A bra-ket → a sum of entries

**R1 · `Braket.dot`** changes the **goal**: unfolding the definition turns the bra-ket into a finite sum.
Definition: `dot ξ ψ = ∑ x, ξ x * ψ x`. Placeholders: `{d : Type} [Fintype d] (φ ψ : Ket d)`.

| Before | After |
|---|---|
| `⊢ P (dot (↑φ) ψ)` | `⊢ P (∑ x, ↑φ x * ψ x)` |

**R2 · `Ket.to_bra`** changes the **goal**: unfolding the coercion `↑φ` gives the literal bra whose vector
is `φ` conjugated. Definition: `Ket.to_bra ψ = ⟨conj ψ, _⟩`. Placeholders: `(φ : Ket d) (x : d)`.

| Before | After |
|---|---|
| `⊢ P (↑φ x)` | `⊢ P ({ vec := (starRingEnd (d → ℂ)) ⇑φ, normalized' := ⋯ } x)` |

**R3 · `Ket.apply`, `Bra.apply`** change the **goal**: `ψ x = ψ.vec x`. On a literal `{ vec := v, … }`,
`simp` then reads off the field, so the entry becomes `v x`. Without them `simp` stays stuck at
`{ vec := … } x`. Placeholders: `(ψ : Ket d) (x : d)`, or `(v : d → ℂ) (hv : ∑ x, ‖v x‖ ^ 2 = 1)`.

| Before | After |
|---|---|
| `⊢ P (ψ x)` | `⊢ P (ψ.vec x)` |
| `⊢ P ({ vec := v, normalized' := hv } x)` | `⊢ P (v x)` |

**R4 · `Pi.conj_apply`** changes the **goal**: entry `x` of a conjugated vector is the conjugate of entry
`x`. Statement: `(starRingEnd (d → ℂ)) f x = (starRingEnd ℂ) (f x)`. Placeholders: `(f : d → ℂ) (x : d)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd (d → ℂ)) f x)` | `⊢ P ((starRingEnd ℂ) (f x))` |

**R5 · `Ket.basis`** changes the **goal**: the basis ket becomes its literal. Definition:
`Ket.basis i = ⟨fun j => if i = j then 1 else 0, _⟩`. Followed by R3, entry `x` becomes an `if`.
Placeholders: `(i x : d)`.

| Before | After `simp only [Ket.basis]` | After `simp only [Ket.apply]` |
|---|---|---|
| `⊢ P ((Ket.basis i) x)` | `⊢ P ({ vec := fun j => if i = j then 1 else 0, normalized' := ⋯ } x)` | `⊢ P (if i = x then 1 else 0)` |

physlib writes this `if` with *classical* decidability (`Classical.propDecidable`), not with your
`[DecidableEq d]`. The two `if`s print the same; see R12.

### Evaluating the sum (`simp` applies these by itself)

**R6 · `MonoidWithZeroHom.map_ite_one_zero`** changes the **goal**: the conjugate of `if p then 1 else 0` is
itself (conjugation fixes `0` and `1`). Statement: `f (if p then 1 else 0) = if p then 1 else 0` for a map
`f` that preserves `*`, `0`, `1`, such as `starRingEnd ℂ`. Placeholders: `(p : Prop) [Decidable p]`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (if p then 1 else 0))` | `⊢ P (if p then 1 else 0)` |

**R7 · `mul_ite`** changes the **goal**: a factor moves into both branches. Statement:
`(a * if p then b else c) = if p then a * b else a * c`. Placeholders: `{α : Type} [Mul α] (a b c : α)
(p : Prop) [Decidable p]` (`ℂ` has `*`).

| Before | After |
|---|---|
| `⊢ P (a * if p then b else c)` | `⊢ P (if p then a * b else a * c)` |

**R8 · `ite_mul`** changes the **goal**: the same with the `if` on the left. Statement:
`(if p then a else b) * c = if p then a * c else b * c`. Placeholders as in R7.

| Before | After |
|---|---|
| `⊢ P ((if p then a else b) * c)` | `⊢ P (if p then a * c else b * c)` |

**R9 · `mul_one`, `mul_zero`** (and `one_mul`, `zero_mul`) change the **goal**: `a * 1 = a`, `a * 0 = 0`.
Placeholders: `{α : Type} [MulZeroOneClass α] (a : α)` (α has `*`, `0`, `1`; `ℂ` and `ℝ` qualify).

| Before | After |
|---|---|
| `⊢ P (if p then a * 1 else a * 0)` | `⊢ P (if p then a else 0)` |

**R10 · `Finset.sum_ite_eq`** changes the **goal**: a sum whose terms vanish except at `x = a` is the
term at `a`. Statement: `(∑ x ∈ s, if a = x then b x else 0) = if a ∈ s then b a else 0`; here `s` is
`Finset.univ`, printed as `∑ x, …`. For `if x = a` use `Finset.sum_ite_eq'`. Placeholders:
`[DecidableEq d] (a : d) (b : d → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, if a = x then b x else 0)` | `⊢ P (if a ∈ Finset.univ then b a else 0)` |

**R11 · `Finset.mem_univ`, then `↓reduceIte`** change the **goal**: every `a` is in `Finset.univ`, so the
condition is `True` and `simp`'s `↓reduceIte` takes the `then` branch. Placeholders: `(a : d) (u v : α)`.

| Before | After `simp only [Finset.mem_univ]` | After `simp only [↓reduceIte]` |
|---|---|---|
| `⊢ P (if a ∈ Finset.univ then u else v)` | `⊢ P (if True then u else v)` | `⊢ P u` |

**R12 · `ite_eq_ite`** **closes** `(if p then x else y) = if p then x else y` even when the two sides decide
`p` with different instances. That is the last goal of Part 1: the left `if` comes from `Ket.basis`
(classical), the right one from the statement (`[DecidableEq d]`), so `rfl` fails but `simp` succeeds.
Placeholders: `(p : Prop) (h₁ h₂ : Decidable p) (x y : α)`.

| Before | After |
|---|---|
| `⊢ (if p then x else y) = if p then x else y` | no goals |

---

## Part 2 · `plus`

Statement: define the ket $|+\rangle = (|0\rangle + |1\rangle)/\sqrt 2$ as a `Ket (Fin 2)`: both entries
are $1/\sqrt 2$. A `Ket` is not a vector space (no `+` on kets), so you give the vector directly and prove
$\sum_x \lVert 1/\sqrt 2\rVert^2 = 2 \cdot \tfrac12 = 1$. `by simp` proves it; R14–R22 are the steps it takes.

**R13 · anonymous constructor `⟨v, ?_⟩`** changes the **goal**: to build a `Ket d` give its vector; what is
left is the normalization proof. In a definition write `⟨v, by tac⟩`: `tac` sees the same goal, with `v`
already applied (`‖(↑√2)⁻¹‖`, not `‖(fun x => …) x‖`). Placeholders: `(v : d → ℂ)`.

| Before | After |
|---|---|
| `⊢ Ket d` | `⊢ ∑ x, ‖v x‖ ^ 2 = 1` |

### The normalization sum (`simp` applies these by itself)

**R14 · `norm_inv`** changes the **goal**. Statement: `‖a⁻¹‖ = ‖a‖⁻¹`. Placeholders:
`{α : Type} [NormedDivisionRing α] (a : α)` (a field with a norm; `ℂ` and `ℝ` qualify).

| Before | After |
|---|---|
| `⊢ P ‖a⁻¹‖` | `⊢ P ‖a‖⁻¹` |

**R15 · `Complex.norm_real`** changes the **goal**: the modulus of a real number cast into `ℂ` is its real
norm. Statement: `‖(↑r : ℂ)‖ = ‖r‖`. Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ‖↑r‖` | `⊢ P ‖r‖` |

**R16 · `Real.norm_eq_abs`** changes the **goal**. Statement: `‖r‖ = |r|` for `r : ℝ`. Placeholders: `(r : ℝ)`.
(Goal block instead of a table: `|` would split a table cell.)

```lean-goal
⊢ P ‖r‖
⊢ P |r|
```

**R17 · `inv_pow`** changes the **goal**. Statement: `a⁻¹ ^ n = (a ^ n)⁻¹`. Placeholders:
`{α : Type} [DivisionMonoid α] (a : α) (n : ℕ)` (`ℂ`, `ℝ` qualify).

| Before | After |
|---|---|
| `⊢ P (a⁻¹ ^ n)` | `⊢ P (a ^ n)⁻¹` |

**R18 · `sq_abs`** changes the **goal**. Statement: `|a| ^ 2 = a ^ 2`. Placeholders: `(a : ℝ)`.

```lean-goal
⊢ P (|a| ^ 2)
⊢ P (a ^ 2)
```

**R19 · `Real.sq_sqrt`** changes the **goal list**. Statement: `0 ≤ x → √x ^ 2 = x`: the goal is rewritten
and a side goal `0 ≤ x` is added (`simp` proves it for a numeral). Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (√x ^ 2)` | `⊢ P x`, `⊢ 0 ≤ x` |

**R20 · `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`** change the **goal**: a sum of a
constant is (number of terms) `•` constant. Statements: `∑ _x ∈ s, c = s.card • c`,
`Finset.univ.card = Fintype.card α`, `Fintype.card (Fin n) = n`. Placeholders:
`{β : Type} [AddCommMonoid β] (n : ℕ) (c : β)` (β has `+` and `0`; `ℝ` qualifies).

| Before | After `rw [Finset.sum_const]` | After `rw [Finset.card_univ]` | After `rw [Fintype.card_fin]` |
|---|---|---|---|
| `⊢ P (∑ _x, c)` | `⊢ P (Finset.univ.card • c)` | `⊢ P (Fintype.card (Fin n) • c)` | `⊢ P (n • c)` |

**R21 · `nsmul_eq_mul`, then `Nat.cast_ofNat`** change the **goal**: `n • c = ↑n * c`, and the cast of a
numeral `↑2` is the numeral `2`. Placeholders: `(c : ℝ)`.

| Before | After `rw [nsmul_eq_mul]` | After `rw [Nat.cast_ofNat]` |
|---|---|---|
| `⊢ P (2 • c)` | `⊢ P (↑2 * c)` | `⊢ P (2 * c)` |

**R22 · `mul_inv_cancel₀`** **closes** `a * a⁻¹ = 1` and leaves the side goal `a ≠ 0`. Placeholders:
`{α : Type} [GroupWithZero α] (a : α)` (`*` with inverses of nonzero elements; `ℝ`, `ℂ` qualify).

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ a * a⁻¹ = 1` | `ha : a ≠ 0 ⊢ a ≠ 0` |

---

## Part 3 · `plus_apply`

Statement: every entry of `plus` is $1/\sqrt 2$: `plus i = ((Real.sqrt 2)⁻¹ : ℂ)`.

**R23 · `rfl`** **closes** an equation that holds by unfolding definitions. `plus` unfolds to your literal,
its entry `i` unfolds (via the coercion, as `Ket.apply` says) to the vector's entry, and your vector is
constant. As a term, write `:= rfl`. Placeholders: `(v : d → ℂ) (hv : ∑ x, ‖v x‖ ^ 2 = 1) (i : d)`.

| Before | After |
|---|---|
| `⊢ { vec := v, normalized' := hv } i = v i` | no goals |

---

## Part 4 · `plus_overlap`

Statement: `〈Ket.basis i‖plus〉 = (√2)⁻¹` for both `i : Fin 2`, i.e. $\langle i|+\rangle = 1/\sqrt 2$.
The same route as Part 1, with `plus` unfolded as well (`simp [plus]`, like R5). The basis ket is now the
*left* factor, so `simp` uses R8 and `one_mul`, `zero_mul` (R9) instead of R7, and the last `if` is
removed by R10 and R11. No √2 arithmetic is needed: the entry `(↑√2)⁻¹` is carried through unchanged.

### Worked combinations (W1–W5, on objects that are not the exercise's)

`q = ⟨![3 / 5, 4 / 5], _⟩ : Ket (Fin 2)`, the state $\tfrac35|0\rangle + \tfrac45|1\rangle$.

**W1.** `q 1 = 4 / 5` holds by `rfl` (R23).

**W2: a bra-ket step by step.** `simp only` with R1; R2, R5 and `q`; R3; R4; R3; R6; R8, R9; R10; R11; a
final `simp` reads the vector literal:

```lean-goal
⊢ dot (↑(Ket.basis 1)) q = 4 / 5
⊢ ∑ x, ↑(Ket.basis 1) x * q x = 4 / 5
⊢ ∑ x, (starRingEnd ℂ) ({ vec := fun j => if 1 = j then 1 else 0, normalized' := ⋯ } x) * ![3 / 5, 4 / 5] x = 4 / 5
⊢ ∑ x, (starRingEnd ℂ) (if 1 = x then 1 else 0) * ![3 / 5, 4 / 5] x = 4 / 5
⊢ ∑ x, (if 1 = x then 1 else 0) * ![3 / 5, 4 / 5] x = 4 / 5
⊢ (∑ x, if 1 = x then ![3 / 5, 4 / 5] x else 0) = 4 / 5
⊢ (if 1 ∈ Finset.univ then ![3 / 5, 4 / 5] 1 else 0) = 4 / 5
⊢ ![3 / 5, 4 / 5] 1 = 4 / 5
```

**W3: the same in one call.** `simp [Braket.dot, Ket.basis, Ket.to_bra, Ket.apply, Bra.apply, q]` closes
`〈Ket.basis (0 : Fin 2)‖q〉 = 3 / 5`.

**W4: a normalization sum step by step** (for `(√3)⁻¹` on `Fin 3`): R20, R14, R15, R16, R17, R18, R19,
R21, R22:

```lean-goal
⊢ ∑ _x, ‖(↑√3)⁻¹‖ ^ 2 = 1
⊢ 3 • ‖(↑√3)⁻¹‖ ^ 2 = 1
⊢ 3 • ‖↑√3‖⁻¹ ^ 2 = 1
⊢ 3 • ‖√3‖⁻¹ ^ 2 = 1
⊢ 3 • |√3|⁻¹ ^ 2 = 1
⊢ 3 • (|√3| ^ 2)⁻¹ = 1
⊢ 3 • (√3 ^ 2)⁻¹ = 1
⊢ 3 • 3⁻¹ = 1
⊢ 3 * 3⁻¹ = 1
```

**W5.** `simp` alone closes that sum.

---

## Traps

- The bra-ket brackets are `〈` (U+3008), `‖` (U+2016) and `〉` (U+3009), not `⟨ | ⟩`. Copy them from the
  spec. The notation needs `open Braket` (the spec already opens it).
- A numeral index defaults to `ℕ`: `Ket.basis 1` fails with "failed to synthesize `Fintype ℕ`". In your own
  experiments write `Ket.basis (1 : Fin 2)`.
- Name all of `Braket.dot, Ket.basis, Ket.to_bra, Ket.apply, Bra.apply` in the `simp` call. `Ket.to_bra`
  without `Bra.apply` leaves `simp` stuck at `{ vec := … } j` (R3); without `Ket.apply` it stays stuck at
  `{ vec := … } x`; without `Ket.to_bra` it stays stuck at `(↑{ vec := … }).vec j` (R2).
- `Ket.basis` decides `i = j` classically, the statement with `[DecidableEq d]`: the two `if`s print the
  same but are not `rfl`-equal (R12). Let `simp` finish.
- `plus` must be `noncomputable` (the spec says so) because `Real.sqrt` cannot be evaluated. Type the entry
  as a complex number: `((Real.sqrt 2)⁻¹ : ℂ)`.
- There is no `+` on kets: `Ket.basis 0 + Ket.basis 1` does not exist. Build the vector, then the ket (R13).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| bra-ket → sum | `simp [Braket.dot, …]` | R1 |
| bra of a ket, entries of a ket/bra | `Ket.to_bra, Bra.apply, Ket.apply` in the `simp` set | R2, R3 |
| entry of a conjugated vector | `Pi.conj_apply` (automatic) | R4 |
| basis ket → its `if` | `Ket.basis` in the `simp` set | R5 |
| conj of `if p then 1 else 0` | `MonoidWithZeroHom.map_ite_one_zero` (automatic) | R6 |
| factor into an `if` | `mul_ite` / `ite_mul` (automatic) | R7, R8 |
| drop `* 1`, `* 0` | `mul_one, mul_zero, one_mul, zero_mul` (automatic) | R9 |
| sum with one nonzero term | `Finset.sum_ite_eq` / `Finset.sum_ite_eq'` (automatic) | R10 |
| `if a ∈ Finset.univ …` | `Finset.mem_univ`, `↓reduceIte` (automatic) | R11 |
| two equal `if`s, different instances | `simp` (`ite_eq_ite`) | R12 |
| build a ket | `⟨v, by simp⟩` | R13 |
| norm of `(↑r)⁻¹` | `norm_inv, Complex.norm_real, Real.norm_eq_abs` (automatic) | R14–R16 |
| `\|√x\|⁻¹ ^ 2 → x⁻¹` | `inv_pow, sq_abs, Real.sq_sqrt` (automatic) | R17–R19 |
| constant sum over `Fin n` | `Finset.sum_const, Finset.card_univ, Fintype.card_fin` (automatic) | R20 |
| `n • c`, `a * a⁻¹` | `nsmul_eq_mul, Nat.cast_ofNat`, `mul_inv_cancel₀` (automatic) | R21, R22 |
| entry of a defined ket | `rfl` | R23 |
| see the state | infoview | |
