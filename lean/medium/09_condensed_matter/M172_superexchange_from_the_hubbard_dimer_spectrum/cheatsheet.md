# M172 · Superexchange from the Hubbard dimer spectrum: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's matrices and vectors over `ℝ`
(`Matrix`, `![…]`, `!![…]`, `*ᵥ`, `⬝ᵥ`, finite sums `∑`), and the arithmetic deciders `linear_combination`,
`linarith`, `nlinarith`, `field_simp`, with the division lemmas `le_div_iff₀`, `div_le_iff₀`.

**Physics.** Two sites, two electrons, total `S_z = 0`. The basis is `|↑↓,0⟩, |0,↑↓⟩, |↑,↓⟩, |↓,↑⟩`
(indices `0, 1, 2, 3`): both electrons on site 1, both on site 2, one on each site with site 1 holding ↑,
then site 1 holding ↓. `t` is the hopping amplitude, `U > 0` the on-site repulsion. `H t U` is the 4×4
Hamiltonian in this basis. The sign convention `|↓,↑⟩ := c†₂↑ c†₁↓ |0⟩` (`c†` creates an electron) makes the
spin triplet `|↑,↓⟩ - |↓,↑⟩ = ![0, 0, 1, -1]` and puts the singlet `|↑,↓⟩ + |↓,↑⟩` in the block that hops
into the doubly occupied states. The lowest (singlet) energy is `E = (U - √(U² + 16t²))/2 < 0`; the gap to
the triplet (energy 0) is `J = 0 - E ≈ 4t²/U` for `U ≫ |t|` (superexchange). No square root is needed in
the proofs: everything follows from `E² - U E - 4t² = 0`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- `G` with a hypothesis `k : T → G` is "any goal": `k` is there only to use the new fact `T`.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid β]`
  is a requirement on `β` (a *type class*); each entry says which familiar types meet it.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (`Real`) |
| `a / b` (in `ℝ`) | real division; Lean defines `a / 0 = 0`, so lemmas about `/` ask for `0 < b` or `b ≠ 0` |
| `-E * x`, `-(t * x)` | `(-E) * x` (prefix `-` binds tighter than `*`), and minus the product `t * x` |
| `0 - E` | literally `0 - E`; Lean does not rewrite it to `-E` (`linarith` treats both the same) |
| `¬E ^ 2 - U * E - 4 * t ^ 2 = 0` | `¬ (E ^ 2 - U * E - 4 * t ^ 2 = 0)`: `¬` applies to the whole equation |
| `Fin 4` | the type `{0, 1, 2, 3}` of indices |
| `Fin 4 → ℝ` | a real vector with 4 components; `v i` is component `i` |
| `Matrix (Fin 4) (Fin 4) ℝ` | 4×4 real matrices; `M i j` is row `i`, column `j`, counted from 0 |
| `![a, b, c, d]` | the vector with components `a, b, c, d` |
| `!![a, b; c, d]` | the matrix with rows `a b` and `c d` (rows split by `;`) |
| `M *ᵥ v` | `Matrix.mulVec`: the matrix `M` times the column vector `v` |
| `u ⬝ᵥ v` | `dotProduct`: `∑ i, u i * v i` |
| `∑ i, f i` | the sum of `f i` over all `i` of the index type (here `Fin 4`) |
| `c • v` | scalar `c` times every component of `v` (`E • v` is `E v`) |
| `0` (a vector), `0 i` | the zero vector, and its component `i` (which is `0 : ℝ`) |
| `(fun i => i) ⟨2, ⋯⟩` | the index `2`, printed this way after `fin_cases` |
| `v ≠ 0` | `¬ (v = 0)`, that is `v = 0 → False` |
| `vecHead v`, `vecTail v` | component `0` of `v`, and `v` with component `0` dropped; appears when `simp` is not given `dotProduct`, `Fin.sum_univ_four` (Traps) |
| `hE.ne` | dot notation: `LT.lt.ne hE`, since `hE : E < 0` has type `LT.lt E 0` (R18) |
| `inst✝ : AddCommMonoid β` | an unnamed type-class assumption from a `[…]` bracket |
| `left✝` | an unnamed hypothesis (from `_` in an `obtain` pattern) |
| `case «2»` | the goal for index `2` |

---

## Part 1 · `triplet_energy`

Statement: `H t U *ᵥ ![0, 0, 1, -1] = 0`, i.e. the triplet vector is an eigenvector with eigenvalue 0. A
vector equation is four number equations, one per component; each one evaluates to `0 = 0` by `simp`.

**R1 · `ext i`** changes the **goal and the context**. A vector `Fin 4 → ℝ` is a function, and `funext`
says two functions are equal when they agree at every input. Placeholders: `(v w : Fin 4 → ℝ)`.

| Before | After |
|---|---|
| `⊢ v = w` | `i : Fin 4 ⊢ v i = w i` |

**R2 · `fin_cases i`** changes the **goal list and the context**: `i` leaves the context, and there is one
goal for each of `0, 1, 2, 3`. Placeholders: `(P : Fin 4 → Prop)`. Follow it with `<;> tac` to run `tac`
on all four.

| Before | After |
|---|---|
| `i : Fin 4 ⊢ P i` | `⊢ P ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩)`, `⊢ P ((fun i => i) ⟨2, ⋯⟩)`, `⊢ P ((fun i => i) ⟨3, ⋯⟩)` |

Name `mulVec`, `dotProduct` and `Fin.sum_univ_four` in the `simp` call (R3–R5); `simp` applies R6–R8 by
itself. (Here both the matrix and the vector are literals, so `simp [H]` alone also happens to finish; with
the general vector `v` of Part 2 it does not, see Traps.)

**R3 · `Matrix.mulVec`** (unfold) changes the **goal**: component `i` of `M *ᵥ v` is row `i` of `M`
dotted with `v`, $(Mv)_i = \sum_j M_{ij} v_j$. Placeholders:
`(M : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) (i : Fin 4)`.

| Before | After `simp only [Matrix.mulVec]` |
|---|---|
| `⊢ P ((M *ᵥ v) i)` | `⊢ P ((fun j => M i j) ⬝ᵥ v)` |

**R4 · `dotProduct`** (unfold) changes the **goal**: a dot product becomes a sum. Placeholders:
`(u v : Fin 4 → ℝ)`.

| Before | After `simp only [dotProduct]` |
|---|---|
| `⊢ P (u ⬝ᵥ v)` | `⊢ P (∑ i, u i * v i)` |

**R5 · `Fin.sum_univ_four`** changes the **goal**. The lemma is `∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3`.
Placeholders: `{β : Type} [AddCommMonoid β] (f : Fin 4 → β)` (β has `+` and `0`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1 + f 2 + f 3)` |

**R6 · component of a literal vector** changes the **goal**. `simp` uses the `Matrix.cons_val_…` lemmas.
Placeholders: `{α : Type} (a b c d : α)`.

| Before | After `simp` |
|---|---|
| `⊢ P (![a, b, c, d] 2)` | `⊢ P c` |

**R7 · entry of a literal matrix** changes the **goal**. `simp` uses `Matrix.of_apply` and
`Matrix.cons_val_…`; 4×4 literals such as the one in `H` work the same. Placeholders: `{α : Type} (a b c d : α)`.

| Before | After `simp` |
|---|---|
| `⊢ P (!![a, b; c, d] 1 0)` | `⊢ P c` |

**R8 · `Pi.zero_apply`** changes the **goal**: a component of the zero vector is `0`. Placeholders:
`(i : Fin 4)`.

| Before | After |
|---|---|
| `⊢ P (0 i)` | `⊢ P 0` |

**W1** (guide): `ext i`, `fin_cases i`, then `all_goals simp [K, mulVec, dotProduct, Fin.sum_univ_four]`
proves `K a *ᵥ ![1, -1, 0, 0] = ![-a, a, 0, 0]` for another 4×4 matrix `K a`. After R1 and R2 one goal is

```lean-goal
⊢ (K a *ᵥ ![1, -1, 0, 0]) ((fun i => i) ⟨0, ⋯⟩) = ![-a, a, 0, 0] ((fun i => i) ⟨0, ⋯⟩)
```

---

## Part 2 · `char_eq`

Statement: if `U > 0`, `E < 0`, and some nonzero `v` has `H t U *ᵥ v = E • v`, then
`E ^ 2 - U * E - 4 * t ^ 2 = 0`. Plan: write out the four component equations `h0 … h3`; assume the bracket
`q := E² - U E - 4t²` is nonzero and show `v = 0`, contradicting `v ≠ 0`. With `s = v 0 + v 1`:

- `-E·(h0 + h1) + 2t·(h2 + h3)` is exactly `q · s = 0`, so `s = 0`;
- `h3 - h2` gives `E (v 2 - v 3) = 0`, so `v 2 = v 3` (as `E ≠ 0`);
- `h2` with `s = 0` gives `E · v 2 = 0`, so `v 2 = 0`, hence `v 3 = 0`;
- `h0` then gives `(U - E) · v 0 = 0`, so `v 0 = 0` (as `U - E > 0`), and `v 1 = -v 0 = 0`.

After the `simp … at`, `h2` reads `-(t * v 0) + -(t * v 1) = E * v 2`: `simp` writes `-t * x` as `-(t * x)`
and drops the zero entries.

### Unpacking the hypothesis

**R9 · `obtain ⟨x, hx1, hx2⟩ := h`** changes the **context**: an `∃` with an `∧` inside is split into the
witness and the two facts. Placeholders: `{α : Type} (A B : α → Prop)`.

| Before | After |
|---|---|
| `⊢ G` with `h : ∃ x, A x ∧ B x` | `x : α, hx1 : A x, hx2 : B x ⊢ G` (`h` is gone) |

**R10 · `have h0 := congrFun hfg 0`** changes the **context**. `congrFun : f = g → ∀ i, f i = g i` reads
off one component of a vector equation. Placeholders: `(f g : Fin 4 → ℝ) (hfg : f = g)`.

| Before | After |
|---|---|
| `hfg : f = g ⊢ G` | `h0 : f 0 = g 0 ⊢ G` |

**R11 · `Pi.smul_apply`, then `smul_eq_mul`** change the **goal**: component `i` of `c • v` is `c * v i`.
`simp` applies both by itself. Placeholders: `(c : ℝ) (v : Fin 4 → ℝ) (i : Fin 4)`.

| Before | After `rw [Pi.smul_apply]` | After `rw [smul_eq_mul]` |
|---|---|---|
| `⊢ P ((c • v) i)` | `⊢ P (c • v i)` | `⊢ P (c * v i)` |

**R12 · `simp [names] at h`** changes the **context**: it simplifies the hypothesis `h` (with the same
lemmas as for a goal) and leaves the goal alone. `simp […] at h0 h1 h2 h3` does four at once. Placeholders:
`(u v : Fin 4 → ℝ) (c : ℝ)`.

| Before | After `simp [dotProduct, Fin.sum_univ_four] at h` |
|---|---|
| `h : u ⬝ᵥ v = (c • u) 0 ⊢ G` | `h : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = c * u 0 ⊢ G` |

### Arguing by contradiction

**R13 · `by_contra hne`** changes the **goal and the context**: assume the negation, prove `False`.
Placeholders: `(G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hne : ¬G ⊢ False` |

**R14 · `apply hv0`** with `hv0 : v ≠ 0` changes the **goal**: `v ≠ 0` is `v = 0 → False`, so applying it
to the goal `False` leaves `v = 0`. Placeholders: `(v : Fin 4 → ℝ)`.

| Before | After |
|---|---|
| `hv0 : v ≠ 0 ⊢ False` | `⊢ v = 0` |

### Combining the equations

**R15 · `linear_combination e₁ * h₁ + … + eₙ * hₙ`** **closes** an equation `lhs = rhs` when
`lhs - rhs = Σ eₖ · (lhsₖ - rhsₖ)` holds as a polynomial identity (it calls `ring` to check). The
coefficients `eₖ` may contain variables. Placeholders: `(x y a b c : ℝ)`.

| Before | After `linear_combination c * h1 + c * h2` |
|---|---|
| `h1 : x + y = a, h2 : x - y = b ⊢ c * (2 * x) = c * (a + b)` | no goals |

To find the coefficients by hand: write each `hₖ` as `lhsₖ - rhsₖ = 0` and match the goal's `lhs - rhs`.

**R16 · `mul_eq_zero`** is `a * b = 0 ↔ a = 0 ∨ b = 0`; `.mp` is the left-to-right direction. Placeholders:
`{M₀ : Type} [MulZeroClass M₀] [NoZeroDivisors M₀] (a b : M₀)` (a product is zero only if a factor is;
`ℝ` qualifies). It changes the **context** when used in a `have`.

| Before | After `have h := mul_eq_zero.mp hab` |
|---|---|
| `hab : a * b = 0 ⊢ G` | `h : a = 0 ∨ b = 0 ⊢ G` |

**R17 · `Or.resolve_left`** is `A ∨ B → ¬A → B`. With R16: `(mul_eq_zero.mp hab).resolve_left ha`, where
`ha : a ≠ 0`, proves `b = 0`. Placeholders: `(A B : Prop)`.

| Before | After `exact hab.resolve_left hna` |
|---|---|
| `hab : A ∨ B, hna : ¬A ⊢ B` | no goals |

**R18 · `LT.lt.ne`** is `a < b → a ≠ b`; for `hE : E < 0`, `hE.ne : E ≠ 0`. For `x ≠ 0` from `0 < x` use
`hx.ne'`. Placeholders: `(x : ℝ) (hx : x < 0)`.

| Before | After `have h := hx.ne` |
|---|---|
| `hx : x < 0 ⊢ G` | `h : x ≠ 0 ⊢ G` |

**R19 · `Eq.symm`, `Eq.trans`**: `h.symm : b = a`, and `h.symm.trans h' : b = c` for `h : a = b`,
`h' : a = c`. Useful to feed a derived equation (here `v 3 = 0`) to R15 without a separate `have`.

| Before | After `have hbc := h.symm.trans h'` |
|---|---|
| `h : a = b, h' : a = c ⊢ G` | `hbc : b = c ⊢ G` |

**R20 · `linarith`** **closes** a goal `=`, `≤`, `<` (or `False`) that follows from the hypotheses by adding
them with nonnegative constant coefficients. It treats products such as `E * v 2` as opaque atoms; use it
for steps like `U - E ≠ 0` from `0 < U` and `E < 0` (as `by linarith` inside the term) or `v 1 = 0` from
`v 0 + v 1 = 0` and `v 0 = 0`.

| Before | After |
|---|---|
| `h1 : x - y = 0, h2 : y = 0 ⊢ x = 0` | no goals |

**W2** (guide): `M2 a = !![0, a; a, 0]` with `M2 a *ᵥ v = E • v`. After R9, R10 (twice) and R12:

| Before `simp … at h0 h1` | After |
|---|---|
| `h0 : (M2 a *ᵥ v) 0 = (E • v) 0, h1 : (M2 a *ᵥ v) 1 = (E • v) 1 ⊢ ∃ v, (E ^ 2 - a ^ 2) * v 0 = 0` | `h0 : a * v 1 = E * v 0, h1 : a * v 0 = E * v 1 ⊢ ∃ v, (E ^ 2 - a ^ 2) * v 0 = 0` |

and `linear_combination (-E) * h0 + (-a) * h1` proves `(E ^ 2 - a ^ 2) * v 0 = 0`.

**W3** (guide): `(mul_eq_zero.mp h).resolve_left hx.ne` turns `h : x * y = 0` and `hx : x < 0` into `y = 0`
(R16, R17, R18 in one term).

---

## Part 3 · `superexchange`

Statement: from `U > 0`, `E < 0` and `E ^ 2 - U * E - 4 * t ^ 2 = 0`, the gap `J = 0 - E` satisfies
`4t²/U - 16t⁴/U³ ≤ J ≤ 4t²/U`. With `J = -E > 0` the quadratic reads `J (U + J) = 4t²`.

- Upper: `J U ≤ J U + J² = 4t²`, so `J ≤ 4t²/U`.
- Lower: `J U = 4t² - J² ≥ 4t² - (4t²/U)²` (square the upper bound; needs `0 ≤ J`), and the left side of
  the goal equals `(4t² - (4t²/U)²)/U`.

`0 - E` is not simplified to `-E` automatically; `linarith`/`nlinarith` do not care.

**R21 · `le_div_iff₀`** is `0 < c → (a ≤ b / c ↔ a * c ≤ b)`. `rw [le_div_iff₀ hc]` changes the **goal**.
Placeholders: `{G₀ : Type} [GroupWithZero G₀] [PartialOrder G₀] … (a b c : G₀)`; `ℝ` qualifies.

| Before | After |
|---|---|
| `⊢ a ≤ b / c` | `⊢ a * c ≤ b` |

**R22 · `nlinarith`** **closes** a polynomial (in)equality. It is `linarith` after adding products of pairs
of hypotheses (and of the negated goal), so a hypothesis `0 < x` times itself supplies `0 < x * x`. Extra
facts go in brackets: `nlinarith [h, sq_nonneg (x - y)]`. Placeholders: `(x y c : ℝ)`.

| Before | After |
|---|---|
| `hx : 0 < x, h : x * (y + x) = c ⊢ x * y ≤ c` | no goals |

**R23 · `field_simp`** changes the **goal**: it multiplies out every denominator it can prove nonzero (from
`hc : 0 < c` or `hc : c ≠ 0` in the context) and cross-multiplies an equation. It may close the goal; when it
leaves a polynomial identity, `ring` finishes. Placeholders: `(a c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ 3 * a / c = (a + 2 * a) / c` | `⊢ 3 * a = a * (1 + 2)` |

**R24 · `div_le_iff₀`** is `0 < c → (b / c ≤ a ↔ b ≤ a * c)`. `rw [div_le_iff₀ hc]` changes the **goal**.
Same placeholders as R21.

| Before | After |
|---|---|
| `⊢ b / c ≤ a` | `⊢ b ≤ a * c` |

**R25 · `pow_le_pow_left₀`** is `0 ≤ a → a ≤ b → ∀ n, a ^ n ≤ b ^ n`: raise both sides of an inequality
between nonnegatives to the power `n`. Placeholders: `{M₀ : Type} [MonoidWithZero M₀] [Preorder M₀] …
(a b : M₀) (n : ℕ)`; `ℝ` qualifies. Its first argument can be `(by linarith)`.

| Before | After `have h := pow_le_pow_left₀ ha hab 2` |
|---|---|
| `ha : 0 ≤ a, hab : a ≤ b ⊢ G` | `h : a ^ 2 ≤ b ^ 2 ⊢ G` |

**W4** (guide): rewrite one side as a single fraction inside a `have` (R23), `rw` with it, clear the
denominator (R24), finish with R20:

```lean-goal
⊢ a / c - b / c ≤ 1
⊢ a - b ≤ 1 * c
```

---

## Traps

- On a general vector `v`, `simp [H] at h0` leaves `h0` in terms of `vecHead v`, `vecTail (vecTail v)`, …
  instead of `v 0, v 2, …`, and `linear_combination` cannot match those. Name `dotProduct` and
  `Fin.sum_univ_four` (and `mulVec`) too (R3–R5); then `h0 : U * v 0 + -(t * v 2) + -(t * v 3) = E * v 0`.
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases`, use `<;>` or `all_goals`.
- The four component equations must be **hypotheses** (`have hk := congrFun hv k`, then `simp … at`), not
  goals: `ext` on the eigen-equation would ask you to prove it.
- `linear_combination` fails with "ring failed" when a coefficient is wrong; the leftover goal it prints is
  `lhs - rhs - Σ eₖ (lhsₖ - rhsₖ) = 0`, which tells you what is missing.
- `linarith` cannot divide by a variable: to get `v 2 = 0` from `E * v 2 = 0` use R16–R18, not `linarith`.
- `rw [le_div_iff₀ hU]` needs the goal to be literally `a ≤ b / U`; `rw [div_le_iff₀ hU]` needs
  `b / U ≤ a`. Rewrite the left side of the lower bound into one fraction `(…) / U` first.
- `nlinarith` only multiplies hypotheses it can see: put the squared bound `(-E) ^ 2 ≤ (4 * t ^ 2 / U) ^ 2`
  (R25) in the context before calling it.
- Basis order is `|↑↓,0⟩, |0,↑↓⟩, |↑,↓⟩, |↓,↑⟩`: index `2` is `|↑,↓⟩`, index `3` is `|↓,↑⟩`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| vector equation → 4 components | `ext i; fin_cases i` | R1, R2 |
| evaluate `M *ᵥ v` entries | `simp [M, mulVec, dotProduct, Fin.sum_univ_four]` | R3–R8 |
| unpack `∃ v, A ∧ B` | `obtain ⟨v, hA, hB⟩ := h` | R9 |
| component `k` of `f = g` as a hypothesis | `have hk := congrFun h k` | R10 |
| `(c • v) i → c * v i` | `simp` (`Pi.smul_apply`, `smul_eq_mul`) | R11 |
| simplify hypotheses | `simp […] at h0 h1` | R12 |
| proof by contradiction | `by_contra hne` | R13 |
| `False` from `v ≠ 0` | `apply hv0` | R14 |
| equation = combination of equations | `linear_combination e₁ * h₁ + e₂ * h₂` | R15 |
| `a * b = 0`, `a ≠ 0` → `b = 0` | `(mul_eq_zero.mp h).resolve_left ha` | R16, R17 |
| `E < 0` → `E ≠ 0` | `hE.ne` | R18 |
| chain equalities | `h.symm.trans h'` | R19 |
| linear arithmetic | `linarith` | R20 |
| `a ≤ b / c` | `rw [le_div_iff₀ hc]` | R21 |
| polynomial inequality | `nlinarith [facts]` | R22 |
| clear denominators in an equation | `field_simp; ring` | R23 |
| `b / c ≤ a` | `rw [div_le_iff₀ hc]` | R24 |
| square an inequality | `pow_le_pow_left₀ h0 h 2` | R25 |
| split `A ∧ B`, close one now | `refine ⟨?_, by linarith⟩` | TACTIC_STATES |
| see the state | infoview | |
