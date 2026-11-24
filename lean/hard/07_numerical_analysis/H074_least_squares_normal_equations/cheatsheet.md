# H074 · Least squares and the normal equations: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`intro`, `have`, `exact`, `rw [h]`, `simp only [...] at h`, `refine`,
`<;>`, `·`) are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `by`, `intro`, `rw`, `simp`, `exact`, `have`,
`refine`, `∧`/`↔`/`¬`, functions as values.
**New here:** Mathlib's vectors `Fin n → ℝ` and matrices (`*ᵥ`, `ᵥ*`, `⬝ᵥ`, `ᵀ`, `•`, `star`),
`Function.Injective`, and the tactics `abel`, `ring`, `linarith`, `nlinarith`, `positivity`, `set`,
`change`, `by_contra`.

**The mathematics.** `A` is a real `m × n` matrix, `b ∈ ℝᵐ`, `x, y, d ∈ ℝⁿ`. Write
`f(y) = ‖A y − b‖²` (the squared residual; `‖v‖² = v ⬝ᵥ v = Σᵢ vᵢ²`), `r = A x − b` (the residual at `x`)
and `g = Aᵀ r` (half the gradient of `f` at `x`).

- *Expansion* (milestone `expand`). `A(x + d) − b = r + A d`, so
  `f(x + d) = ‖r‖² + 2⟨r, A d⟩ + ‖A d‖² = f(x) + 2⟨g, d⟩ + ‖A d‖²`, using `⟨A d, r⟩ = ⟨Aᵀ r, d⟩`
  (milestone `cross_term`).
- *(→)* If `g = 0`, put `d = y − x`: `f(y) = f(x) + ‖A d‖² ≥ f(x)`.
- *(←)* If `g ≠ 0`, then `G := ‖g‖² > 0`. Let `Q := ‖A g‖² ≥ 0` and step against the gradient,
  `d = −t g` with `t > 0`: `f(x − t g) = f(x) − 2tG + t²Q`. Minimality gives `0 ≤ −2tG + t²Q`, so
  `2G ≤ tQ`. With `t = G/(Q + 1)`, `tQ = GQ/(Q + 1) < G`, so `2G < G`, contradicting `G > 0`.
- *Uniqueness.* If both `x` and `x'` solve the normal equations, expanding from each toward the other
  gives `f(x') = f(x) + ‖A(x' − x)‖²` and `f(x) = f(x') + ‖A(x − x')‖²`. Both squares are `≥ 0`, so
  `‖A(x' − x)‖² = 0`, `A x' = A x`, and injectivity of `v ↦ A v` gives `x' = x`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp only`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : R → Prop`, or `P : (ι → R) → Prop` for a vector). The step changes
  only the part inside `P (…)`, wherever it sits in a larger goal. `G : Prop` is an arbitrary goal that
  the example finishes with `hG`; it exists only so the new hypothesis can be shown.
- Placeholders are written as Lean binders. `{ι κ : Type} [Fintype ι]` is any finite index type (the
  exercise uses `Fin n = {0, …, n-1}` and `Fin m`). `[CommRing R]` is any commutative ring (`ℤ`, `ℚ`, `ℝ`,
  `ℂ`); the lemmas need less, but every commutative ring qualifies. `[AddCommGroup V]` is any type with
  `+`, `-`, `0` obeying the usual laws; vectors `ι → ℝ` and `ℝ` itself qualify.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin n → ℝ` | a vector in ℝⁿ: a function from the index set `Fin n = {0, …, n-1}` to `ℝ` |
| `Matrix (Fin m) (Fin n) ℝ` | a real `m × n` matrix: a function `Fin m → Fin n → ℝ`; `A i j` is row `i`, column `j` |
| `A *ᵥ v` | `Matrix.mulVec A v`: matrix times column vector, `(A v)ᵢ = Σⱼ A i j * v j` |
| `A.mulVec` | the same as a function: `v ↦ A *ᵥ v` |
| `v ᵥ* A` | `Matrix.vecMul v A`: row vector times matrix, `(vᵀA)ⱼ = Σᵢ v i * A i j` |
| `v ⬝ᵥ w` | `dotProduct v w = Σᵢ v i * w i`; `v ⬝ᵥ v` is `‖v‖²` |
| `Aᵀ` | `Matrix.transpose A`, the `n × m` matrix with `Aᵀ j i = A i j` |
| `c • v` | scalar multiple of a vector, `(c • v) i = c * v i`; for two scalars `a • b = a * b` (R23) |
| `star v` | entrywise conjugation (`star` is complex conjugation on `ℂ`); on `ℝ` it does nothing (R5) |
| `A *ᵥ d ⬝ᵥ r` | `(A *ᵥ d) ⬝ᵥ r`: `*ᵥ`, `ᵥ*`, `•` bind tighter than `⬝ᵥ` |
| `2 * u ⬝ᵥ w` | `2 * (u ⬝ᵥ w)`: `⬝ᵥ` binds tighter than `*` (see Traps) |
| `-t • g` | `(-t) • g` |
| `0` (a vector) | the zero vector `fun _ => 0` |
| `hg : ¬g = 0` | what `by_contra hg` (R16) gives for the goal `g = 0`: "`g` is not the zero vector" |
| `Function.Injective f` | `∀ ⦃a b⦄, f a = f b → a = b`; for `f = A.mulVec`: the columns of `A` are linearly independent |
| `g : Fin n → ℝ := e` | a local definition made by `set` (R15): `g` is a name for `e` |
| `a ≠ b` | `a = b → False` |
| `inst✝ : Fintype ι` | an anonymous type-class hypothesis: "`ι` is finite" |
| `case mp`, `case mpr` | the `→` and `←` goals of an `↔` after `constructor` |

---

## Part 1 · `cross_term` (milestone)

Statement: `(A *ᵥ d) ⬝ᵥ r = (Aᵀ *ᵥ r) ⬝ᵥ d`, i.e. `⟨A d, r⟩ = ⟨Aᵀ r, d⟩`. Three rewrites turn both
sides into `r ᵥ* A ⬝ᵥ d`.

**R1 · `rw [dotProduct_comm]`** changes the **goal**. The lemma is `dotProduct_comm : v ⬝ᵥ w = w ⬝ᵥ v`.
Bare, it swaps the first dot product `rw` finds (and every identical copy); `rw [dotProduct_comm v w]`
swaps only `v ⬝ᵥ w`. Placeholders: `{ι R : Type} [Fintype ι] [CommRing R] (v w : ι → R)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ w)` | `⊢ P (w ⬝ᵥ v)` |

**R2 · `rw [Matrix.dotProduct_mulVec]`** changes the **goal**. The lemma is
`v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w`: a matrix moves from acting on the right vector to acting on the left one.
Placeholders: `{ι κ R : Type} [Fintype ι] [Fintype κ] [CommRing R] (v : κ → R) (A : Matrix κ ι R) (w : ι → R)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ A *ᵥ w)` | `⊢ P (v ᵥ* A ⬝ᵥ w)` |

**R3 · `rw [Matrix.mulVec_transpose]`** changes the **goal**. The lemma is `Aᵀ *ᵥ x = x ᵥ* A`.
Placeholders: `(A : Matrix κ ι R) (x : κ → R)`.

| Before | After |
|---|---|
| `⊢ P (Aᵀ *ᵥ x)` | `⊢ P (x ᵥ* A)` |

---

## Part 2 · `self_nonneg` (milestone)

Statement: `0 ≤ v ⬝ᵥ v` for `v : Fin k → ℝ`. Mathlib states it with a conjugate; on `ℝ` the conjugate
disappears.

**R4 · `dotProduct_self_star_nonneg`** changes the **context** (with `have`). The lemma is
`0 ≤ v ⬝ᵥ star v` over an ordered ring with conjugation (`ℝ`, `ℂ`). Placeholders: `(v : ι → ℝ)`.

| Before | After `have h := dotProduct_self_star_nonneg v` |
|---|---|
| `⊢ G` | `h : 0 ≤ v ⬝ᵥ star v ⊢ G` |

**R5 · `star_trivial`** changes the **context** (with `at h`): `star r = r` on a type whose `star` is the
identity, such as `ℝ` and vectors over `ℝ`. `simp` uses it by itself, so `simpa using e` (simplify `e` and
the goal, then `exact e`) turns the R4 fact into `0 ≤ v ⬝ᵥ v`. Placeholders: `(v : ι → ℝ)`.

| Before | After `simp only [star_trivial] at h` |
|---|---|
| `h : P (star v) ⊢ G` | `h : P v ⊢ G` |

---

## Part 3 · `expand` (milestone)

Statement: with `r = A *ᵥ x - b`,
`(A *ᵥ (x + d) - b) ⬝ᵥ (A *ᵥ (x + d) - b) = r ⬝ᵥ r + 2 * ((Aᵀ *ᵥ r) ⬝ᵥ d) + (A *ᵥ d) ⬝ᵥ (A *ᵥ d)`.

**R6 · `rw [Matrix.mulVec_add]`** changes the **goal**. The lemma is `A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y`.
Placeholders: `{ι κ R : Type} [Fintype ι] [CommRing R] (A : Matrix κ ι R) (x y : ι → R)`.

| Before | After |
|---|---|
| `⊢ P (A *ᵥ (x + y))` | `⊢ P (A *ᵥ x + A *ᵥ y)` |

**R7 · `rw [show a + c - b = a - b + c by abel]`** changes the **goal**: it regroups a sum. `abel` closes
identities that use only `+`, `-`, `0` in an additive commutative group (vectors included); `ring` would
also work on `ℝ` but not on vectors. `show T by tac` is an inline proof of `T`, so `rw` can use it once.
`a - b + c` is how Lean prints `(a - b) + c`. Placeholders: `{V : Type} [AddCommGroup V] (a b c : V)`.

| Before | After |
|---|---|
| `⊢ P (a + c - b)` | `⊢ P (a - b + c)` |

**R8 · `add_dotProduct`** changes the **goal**: `(u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w`.
Placeholders: `{ι R : Type} [Fintype ι] [CommRing R] (u v w : ι → R)`.

| Before | After |
|---|---|
| `⊢ P ((u + v) ⬝ᵥ w)` | `⊢ P (u ⬝ᵥ w + v ⬝ᵥ w)` |

**R9 · `dotProduct_add`** changes the **goal**: `u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w`. Same placeholders.
`simp only [add_dotProduct, dotProduct_add]` applies R8 and R9 until neither fits.

| Before | After |
|---|---|
| `⊢ P (u ⬝ᵥ (v + w))` | `⊢ P (u ⬝ᵥ v + u ⬝ᵥ w)` |

**R10 · `ring`** **closes** an identity of commutative rings. Every dot product is one unknown, and
`u ⬝ᵥ w`, `w ⬝ᵥ u` are *different* unknowns: line them up with R1 (with arguments) first.

**W1: ‖u + w‖² for plain vectors** (R8, R9, R1 with arguments, R10):

```lean-goal
⊢ (u + w) ⬝ᵥ (u + w) = u ⬝ᵥ u + 2 * u ⬝ᵥ w + w ⬝ᵥ w
⊢ u ⬝ᵥ u + w ⬝ᵥ u + (u ⬝ᵥ w + w ⬝ᵥ w) = u ⬝ᵥ u + 2 * u ⬝ᵥ w + w ⬝ᵥ w
⊢ u ⬝ᵥ u + u ⬝ᵥ w + (u ⬝ᵥ w + w ⬝ᵥ w) = u ⬝ᵥ u + 2 * u ⬝ᵥ w + w ⬝ᵥ w
```

After `rw [dotProduct_comm w u]` the two cross terms are the same atom and `ring` closes it. In `expand`
the second cross term is then rewritten by `cross_term` instead.

---

## Part 4 · `normal_equations_iff`

Statement: `Aᵀ *ᵥ (A *ᵥ x - b) = 0 ↔ ∀ y, f(x) ≤ f(y)` with `f(y) = (A *ᵥ y - b) ⬝ᵥ (A *ᵥ y - b)`.

### Splitting and the easy direction

**R11 · `constructor`** on `↔` changes the **goal list**: one goal per direction.
Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R12 · `add_sub_cancel`** changes the **context** (with `rw … at h`). The lemma is `a + (b - a) = b`; it
turns `expand … x (y - x)` into a statement about `y`. Placeholders: `{V : Type} [AddCommGroup V] (a b : V)`.

| Before | After `rw [add_sub_cancel] at h` |
|---|---|
| `h : P (a + (b - a)) ⊢ G` | `h : P b ⊢ G` |

**R13 · `zero_dotProduct`** changes the **context** here (with `at h`): `0 ⬝ᵥ v = 0`. After `rw [hx] at h`
the cross term is `0 ⬝ᵥ (y - x)`. Placeholders: `{ι R : Type} [Fintype ι] [CommRing R] (v : ι → R)`.

| Before | After `rw [zero_dotProduct] at h` |
|---|---|
| `h : P (0 ⬝ᵥ v) ⊢ G` | `h : P 0 ⊢ G` |

**R14 · `linarith [e]`** **closes** a linear equality or inequality that follows from the hypotheses
plus the extra fact `e`. Products and dot products count as single unknowns; numeral arithmetic such as
`2 * 0` is done. Placeholders: `(a c : ℝ) (f : ℝ → ℝ) (hf : ∀ y, 0 ≤ f y)`.

| Before | After `linarith [hf 1]` |
|---|---|
| `h : c = a + 2 * 0 + f 1 ⊢ a ≤ c` | no goals |

### The hard direction: a step against the gradient

**R15 · `set y := e`** changes the **context and the goal**: it adds the local definition `y : T := e` and
replaces every `e` in the goal and the context by `y`. A hypothesis made *later* (such as `hmin _` after
`rw [expand]`) still shows `e`, not `y` (R24). Placeholders: `(f : ℝ → ℝ) (x : ℝ)`.

| Before | After |
|---|---|
| `h : P (f x) ⊢ P (f x)` | `y : ℝ := f x, h : P y ⊢ P y` |

**R16 · `by_contra hc`** changes the **goal and the context**: the goal becomes `False`, and `hc : ¬Q` is
added. Placeholders: `(Q : Prop)`.

| Before | After |
|---|---|
| `⊢ Q` | `hc : ¬Q ⊢ False` |

**R17 · `dotProduct_self_eq_zero`** changes the **context** (with `.mp`). The lemma is
`v ⬝ᵥ v = 0 ↔ v = 0` over `ℝ` (an ordered field); `.mp` is its `→` direction. Placeholders: `(v : ι → ℝ)`.

| Before | After `have hv := dotProduct_self_eq_zero.mp h` |
|---|---|
| `h : v ⬝ᵥ v = 0 ⊢ G` | `hv : v = 0 ⊢ G` |

**R18 · `lt_of_le_of_ne`** changes the **goal list**. The lemma is `a ≤ b → a ≠ b → a < b`. For
`0 < G` the first argument is `self_nonneg g`; the second, `0 ≠ G`, is `fun h => …` with `h : 0 = G`
(use `h.symm : G = 0` with R17 and `hg`). Placeholders: `(a b : ℝ)`.

| Before | After `refine lt_of_le_of_ne ?_ ?_` |
|---|---|
| `⊢ a < b` | `⊢ a ≤ b`, `⊢ a ≠ b` |

**R19 · `positivity`** **closes** goals `0 < e`, `0 ≤ e`, `e ≠ 0` where `e` is built from `+`, `*`, `/`,
`^`, numerals, and atoms whose sign is a hypothesis (`ha : 0 < a`, `hb : 0 ≤ b`). It sees through a
`set` name such as `t := G / (Q + 1)`. Example: `0 < a / (b + 1)` from `0 < a`, `0 ≤ b`.

**R20 · `Matrix.mulVec_smul`** changes the **goal**: `A *ᵥ (c • v) = c • (A *ᵥ v)`.
Placeholders: `(A : Matrix κ ι R) (c : R) (v : ι → R)`.

| Before | After |
|---|---|
| `⊢ P (A *ᵥ c • v)` | `⊢ P (c • A *ᵥ v)` |

**R21 · `smul_dotProduct`** changes the **goal**: `(c • v) ⬝ᵥ w = c • (v ⬝ᵥ w)`.
Placeholders: `(c : R) (v w : ι → R)`.

| Before | After |
|---|---|
| `⊢ P (c • v ⬝ᵥ w)` | `⊢ P (c • (v ⬝ᵥ w))` |

**R22 · `dotProduct_smul`** changes the **goal**: `v ⬝ᵥ (c • w) = c • (v ⬝ᵥ w)`. Same placeholders.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ c • w)` | `⊢ P (c • (v ⬝ᵥ w))` |

**R23 · `smul_eq_mul`** changes the **goal**: for two scalars, `a • b = a * b`. Placeholders: `(a b : R)`.
`simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h` applies R20–R23 together
(W2 shows the result on `(c • v) ⬝ᵥ (c • v)`).

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**R24 · `change T at h`** changes the **context**: `h` is restated as `T`, which must be definitionally
equal (equal after unfolding definitions, `set` names included). `_` in `T` is copied from `h`. Use it to
fold `Aᵀ *ᵥ (A *ᵥ x - b) ⬝ᵥ g` back into `G`, so that `nlinarith` sees `G` and `Q` as the atoms.
Placeholders: `(f : ℝ → ℝ) (x : ℝ)` and `y := f x` made by R15.

| Before | After `change 0 ≤ y ^ 2 at h` |
|---|---|
| `h : 0 ≤ f x ^ 2 ⊢ G` | `h : 0 ≤ y ^ 2 ⊢ G` |

**R25 · `nlinarith`** **closes** a goal that needs *products* of hypotheses: it multiplies pairs of
hypotheses (and the negated goal) and then runs `linarith`. Example: `a ≤ b` from `0 < t` and
`t * a ≤ t * b`. In the exercise: `2 * G ≤ t * Q` from `0 < t` and `0 ≤ 2 * (-t * G) + (-t * (-t * Q))`.

**R26 · `div_mul_eq_mul_div`** changes the **goal**: `a / b * c = a * c / b`, so `t * Q` with
`t := G / (Q + 1)` becomes a single fraction. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a / b * c)` | `⊢ P (a * c / b)` |

**R27 · `rw [div_lt_iff₀ hc]`** changes the **goal**. The lemma is `0 < c → (b / c < a ↔ b < a * c)`:
it clears a positive denominator. Write `div_lt_iff₀ (by linarith)` to prove `0 < Q + 1` on the spot.
Placeholders: `(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ b / c < a` | `⊢ b < a * c` |

---

## Part 5 · `least_squares_unique`

Statement: if `A.mulVec` is injective and both `x`, `x'` solve the normal equations, then `x = x'`.
R12, R13, R14 and R17 are used as in Part 4.

**R28 · `Matrix.mulVec_sub`** changes the **context** here (with `at h`): `A *ᵥ (x - y) = A *ᵥ x - A *ᵥ y`.
Placeholders: `(A : Matrix κ ι R) (x y : ι → R)`.

| Before | After `rw [mulVec_sub] at h` |
|---|---|
| `h : P (A *ᵥ (x - y)) ⊢ G` | `h : P (A *ᵥ x - A *ᵥ y) ⊢ G` |

**R29 · `sub_eq_zero`** changes the **context** (with `rw … at h`; `rw` also rewrites with an `↔`):
`a - b = 0 ↔ a = b`. Placeholders: `{V : Type} [AddCommGroup V] (a b : V)`.

| Before | After |
|---|---|
| `h : a - b = 0 ⊢ G` | `h : a = b ⊢ G` |

**R30 · `hf h`** (applying `hf : Function.Injective f`) changes the **context**: from `h : f a = f b` it
gives `a = b`. The arguments `a b` are implicit, so `hf h` is the whole term. `A *ᵥ v` is `A.mulVec v`, so
`hA` applies directly to `h1 : A *ᵥ x' = A *ᵥ x`. Placeholders: `{α β : Type} (f : α → β) (a b : α)`.

| Before | After `have e := hf h` |
|---|---|
| `h : f a = f b ⊢ G` | `e : a = b ⊢ G` |

**W3: injective `B`, `B *ᵥ (u - w) = 0` gives `u = w`.** `rw [mulVec_sub, sub_eq_zero] at h` (R28, R29)
leaves `h : B *ᵥ u = B *ᵥ w`, and `exact hB h` (R30) closes `u = w`.

---

## Traps

- **Precedence.** `⬝ᵥ` binds tighter than `*`: `2 * u ⬝ᵥ w` is `2 * (u ⬝ᵥ w)`, and after `rw [expand] at h`
  Lean prints `2 * Aᵀ *ᵥ (A *ᵥ x - b) ⬝ᵥ -t • g`, which is `2 * ((Aᵀ *ᵥ (A *ᵥ x - b)) ⬝ᵥ ((-t) • g))`.
  After the R20–R23 `simp only … at h` it prints
  `2 * (-t * Aᵀ *ᵥ (A *ᵥ x - b) ⬝ᵥ g) + -t * (-t * A *ᵥ g ⬝ᵥ A *ᵥ g)`, i.e.
  `2 * (-t * (g ⬝ᵥ g)) + -t * (-t * ((A *ᵥ g) ⬝ᵥ (A *ᵥ g)))` with `g` unfolded.
  Write the parentheses yourself in `have` and `show` statements.
- `have h := hmin _` fails ("don't know how to synthesize placeholder"): `rw [expand] at h` cannot
  choose the point for you. Write it: `have h := hmin (x + (-t) • g)`.
- `Function.Injective A.mulVec` is the hypothesis "the columns of `A` are linearly independent"
  (`A v = 0 → v = 0`). Apply it as a function, `hA h1`, to an equation `A *ᵥ x' = A *ᵥ x` (R30); it gives
  `x' = x`, so the goal `x = x'` needs `.symm`.
- Bare `rw [dotProduct_comm]` swaps the first dot product it meets, which may not be the one you want;
  in `expand` give both arguments (R1).
- `set` folds only what exists when it runs. After `have h := hmin (x + (-t) • g)` and `rw [expand] at h`,
  `h` mentions `Aᵀ *ᵥ (A *ᵥ x - b) ⬝ᵥ g`, not `G`; fold it with `change … at h` (R24) before `nlinarith`,
  or `nlinarith` sees unrelated atoms.
- `ring` and `linarith` treat `u ⬝ᵥ w` and `w ⬝ᵥ u` as different unknowns (R10).
- `abel` for vector identities (`+`, `-` of vectors); `ring` only for scalars (R7).
- `dotProduct_self_eq_zero` needs an ordered ring such as `ℝ`; on `ℂ` it is false (`(1, i) ⬝ᵥ (1, i) = 0`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| swap a dot product | `rw [dotProduct_comm u v]` | R1 |
| `v ⬝ᵥ (A *ᵥ w) → (v ᵥ* A) ⬝ᵥ w` | `rw [dotProduct_mulVec]` | R2 |
| `Aᵀ *ᵥ x → x ᵥ* A` | `rw [mulVec_transpose]` | R3 |
| `0 ≤ v ⬝ᵥ v` on ℝ | `simpa using dotProduct_self_star_nonneg v` | R4, R5 |
| distribute `A` over `+` / `-` | `rw [mulVec_add]` / `rw [mulVec_sub]` | R6, R28 |
| regroup vectors | `rw [show a + c - b = a - b + c by abel]` | R7 |
| distribute `⬝ᵥ` over `+` | `simp only [add_dotProduct, dotProduct_add]` | R8, R9 |
| scalar identity in dot-product atoms | `ring` | R10 |
| split `↔` | `constructor` | R11 |
| `a + (b - a) → b` | `rw [add_sub_cancel] at h` | R12 |
| `0 ⬝ᵥ v → 0` | `rw [zero_dotProduct] at h` | R13 |
| linear finish with an extra fact | `linarith [e]` | R14 |
| name a subexpression | `set g := e` | R15 |
| proof by contradiction | `by_contra hg` | R16 |
| `v ⬝ᵥ v = 0 → v = 0` | `dotProduct_self_eq_zero.mp h` | R17 |
| `≤` and `≠` give `<` | `lt_of_le_of_ne h₁ h₂` | R18 |
| `0 < G / (Q + 1)` | `positivity` | R19 |
| scalars out of `*ᵥ`, `⬝ᵥ` | `simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h` | R20–R23 |
| fold back into `set` names | `change _ ≤ _ + … at h` | R24 |
| nonlinear arithmetic | `nlinarith` | R25 |
| clear a positive denominator | `rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]` | R26, R27 |
| `a - b = 0 → a = b` | `rw [sub_eq_zero] at h` | R29 |
| use injectivity | `hA h` | R30 |
