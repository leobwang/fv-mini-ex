# H101 · Two-site Hubbard model ground state: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `apply`, `rw`, `simp`, `have`,
`constructor`, `ring`, `norm_num`, anonymous functions `fun x => …`. **New here:** Mathlib's real
square root `√` and absolute value `|·|`, vectors `Fin 4 → ℝ` with matrix–vector product `*ᵥ` and dot
product `⬝ᵥ`, and the arithmetic closers `positivity`, `linarith`, `nlinarith`, `linear_combination`.

**The physics, in symbols.** Two lattice sites, two electrons, total spin projection `S_z = 0`. The four
basis states are `|↑↓,0⟩` (both on site 1), `|0,↑↓⟩` (both on site 2), `|↑,↓⟩`, `|↓,↑⟩` (one per site), in
this order, so a state is a vector `x = (x₀, x₁, x₂, x₃)`. `t` is the hopping amplitude (moves one
electron to the other site, matrix entry `-t`), `U` the on-site repulsion (energy of a doubly occupied
site, the diagonal `U, U, 0, 0`). Hopping connects only `s = x₀ + x₁` with `d = x₂ + x₃`; with
`a = x₀ - x₁`, `b = x₂ - x₃`:

$\langle x, Hx\rangle = U(x_0^2 + x_1^2) - 2t\,s\,d$, $\ \|x\|^2 = (s^2 + a^2 + d^2 + b^2)/2$, so

$\langle x, Hx\rangle - E_0\|x\|^2 = \tfrac12\big[(U - E_0)s^2 - 4t\,s\,d - E_0 d^2\big] + \tfrac12(U - E_0)a^2 - \tfrac12 E_0 b^2.$

On the `(s, d)` block the energy is the 2×2 matrix `[[U, -2t], [-2t, 0]]`, whose eigenvalues solve
$E^2 - UE - 4t^2 = 0$: $E_0 = (U - \sqrt{U^2 + 16t^2})/2$ is the lower root. For `t ≠ 0`,
$|U| < \sqrt{U^2 + 16t^2}$, so $E_0 < 0$ and $E_0 < U$. Then the last two terms are `≥ 0`, and the bracket
is `≥ 0` because $(U - E_0)\cdot[\ldots] = ((U - E_0)s - 2td)^2$ (complete the square, use the quadratic).

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves alone.
- Many lemmas here are used in **term mode**: `have h := lemma args` adds the instance `h` to the
  context, and you pass `h` on (to `linarith`, `nlinarith`, `exact`). `X.mpr h` uses the `←` direction
  of an `↔` lemma `X` (`.mp` the `→` direction).
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin 4 → ℝ` | a real vector with entries indexed by `Fin 4 = {0, 1, 2, 3}`; `x 2` is entry 2 |
| `![a, b, c, d]` | the vector with those four entries |
| `Matrix (Fin 4) (Fin 4) ℝ`, `!![a, b; c, d]` | 4×4 real matrices; a literal lists rows separated by `;` |
| `M *ᵥ v` | matrix times vector: `(M *ᵥ v) i = ∑ j, M i j * v j` (`Matrix.mulVec`) |
| `v ⬝ᵥ w` | dot product `∑ i, v i * w i` (`dotProduct`); `x ⬝ᵥ x = ‖x‖²` |
| `E0 t U * x ⬝ᵥ x` | `E0 t U * (x ⬝ᵥ x)`: `⬝ᵥ` binds tighter than `*` |
| `x ⬝ᵥ H t U *ᵥ x` | `x ⬝ᵥ (H t U *ᵥ x) = ⟨x, H x⟩`: `*ᵥ` binds tighter than `⬝ᵥ` |
| `c • v` | scalar times vector, entrywise: `(c • v) i = c * v i` |
| `(fun j => M i j) ⬝ᵥ v` | row `i` of `M` dotted with `v` (what `mulVec` unfolds to) |
| `∑ i, f i` | sum over all `i : Fin 4` |
| `0 2` | entry 2 of the zero vector `(0 : Fin 4 → ℝ)`, which `simp` turns into `0` |
| `√x` | `Real.sqrt x`, the nonnegative root (and `0` for `x < 0`) |
| `\|x\|` | absolute value |
| `a ≠ b` | `a = b → False` |
| `h✝` | a hypothesis with no usable name (made by `cases`); tactics such as `linarith` still see it |
| `(fun i => i) ⟨2, ⋯⟩` | the index `2 : Fin 4`, printed this way after `fin_cases i` (`⋯` hides the proof `2 < 4`); `simp` turns it back into `2` |
| `case refine_2.«0»` | goal from the second `?_` of `refine`, entry `0` after `fin_cases` |
| `case left.inr` | goal from the left half of `constructor`, second (`inr`) side of `cases abs_cases U` |
| `-(t * x 2)` | what `simp` makes of the matrix entry `-t` times `x 2` |

---

## Part 1 · `E0_quad` (milestone)

Statement: `E0 t U ^ 2 - U * E0 t U - 4 * t ^ 2 = 0`, i.e. `E0` is a root of `E² - U E - 4t² = 0`. The only
non-ring fact needed is `√(U² + 16t²)² = U² + 16t²`.

**R1 · `Real.sq_sqrt`** changes the **context** (used as `have h := Real.sq_sqrt hx`). The lemma is
`Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x`. Placeholders: `(x : ℝ) (hx : 0 ≤ x)`. Write the hypothesis inline as
`(show 0 ≤ e by positivity)`.

| Before | After |
|---|---|
| `hx : 0 ≤ x ⊢ G` | `h : √x ^ 2 = x ⊢ G` |

**R2 · `positivity`** **closes** a goal `0 ≤ e` or `0 < e` when `e` is built from squares, even powers,
sums, products and positive numerals (it does not need hypotheses for those).

| Before | After |
|---|---|
| `⊢ 0 ≤ a ^ 2 + 16 * b ^ 2` | closed |

**R3 · `unfold D`** changes the **goal**: every occurrence of the defined name `D` is replaced by its body.
Placeholders: `F` defined by `noncomputable def F (a b : ℝ) : ℝ := (a - b) / 3` (`noncomputable`
because real arithmetic cannot be run).

| Before | After |
|---|---|
| `⊢ P (F a b)` | `⊢ P ((a - b) / 3)` |

**R4 · `linear_combination e`** **closes** an equation `L = R`. Here `e` is a combination
`c₁ * h₁ + c₂ * h₂ + …` of equations `hᵢ : lᵢ = rᵢ` with ring coefficients `cᵢ` (numbers or polynomials, such
as `1 / 4` or `d ^ 2`). It succeeds when `L - R - Σ cᵢ (lᵢ - rᵢ) = 0` is a ring identity (`ring` checks it).
To find `cᵢ`: expand `L - R` and match the non-ring part (here `√… ^ 2`) against `lᵢ - rᵢ`.
Placeholders: `(x y : ℝ) (h : x ^ 2 = y)`.

| Before | After |
|---|---|
| `h : x ^ 2 = y ⊢ (x / 2) ^ 2 = y / 4` | closed by `linear_combination h / 4` |

---

## Part 2 · `E0_lt` (milestone)

Statement: `t ≠ 0 → E0 t U < 0 ∧ E0 t U < U`. Prove `|U| < √(U ^ 2 + 16 * t ^ 2)` first; after unfolding
`E0`, both halves are linear in `U`, `|U|` and that root, once you know the sign of `U`.

**R5 · `rw [← Real.sqrt_sq_eq_abs]`** changes the **goal**. The lemma is
`Real.sqrt_sq_eq_abs : √(x ^ 2) = |x|`; right to left it writes `|x|` as a root, so both sides of `<` are
roots. Placeholders: `(x : ℝ)`. Before, then after (a block, because `|` cannot sit in a table cell):

```lean-goal
⊢ P |x|
⊢ P √(x ^ 2)
```

**R6 · `Real.sqrt_lt_sqrt`** changes the **goal list** (with `apply`). The lemma is
`Real.sqrt_lt_sqrt : 0 ≤ x → x < y → √x < √y`. Placeholders: `(x y : ℝ)`. As a term:
`Real.sqrt_lt_sqrt hx hxy`, with `(by …)` for each argument.

| Before | After |
|---|---|
| `⊢ √x < √y` | `⊢ 0 ≤ x`, `⊢ x < y` |

**R7 · `sq_nonneg`** changes the **context**: `sq_nonneg a : 0 ≤ a ^ 2`. Placeholders: `(a : ℝ)` (any
ordered ring). `sq_nonneg _` lets Lean infer `a`.

| Before | After |
|---|---|
| `⊢ G` | `h : 0 ≤ a ^ 2 ⊢ G` |

**R8 · `abs_pos`** changes the **context**. The lemma is `abs_pos : 0 < |a| ↔ a ≠ 0`, so
`abs_pos.mpr ha : 0 < |a|`. Placeholders: `(a : ℝ) (ha : a ≠ 0)`.

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ G` | `h : 0 < \|a\|` `⊢ G` |

**R9 · `pow_pos`** changes the **context**. The lemma is `pow_pos : 0 < a → ∀ n, 0 < a ^ n`.
Placeholders: `(a : ℝ) (ha : 0 < a)`.

| Before | After |
|---|---|
| `ha : 0 < a ⊢ G` | `h : 0 < a ^ 2 ⊢ G` |

**R10 · `simp at h`** changes the **context**: `h` is simplified in place. Here `simp` uses `sq_abs :
|a| ^ 2 = a ^ 2`, so R8 then R9 then R10 turn `t ≠ 0` into `0 < t ^ 2`, which `linarith` can use.
Placeholders: `(a : ℝ) (h : 0 < |a| ^ 2)`.

| Before | After |
|---|---|
| `h : 0 < \|a\| ^ 2` `⊢ G` | `h : 0 < a ^ 2 ⊢ G` |

**R11 · `linarith`** **closes** a goal `<`, `≤`, `=`, or `False` that follows from hypotheses by adding
them with nonnegative coefficients. It treats every nonlinear piece (`t ^ 2`, `√e`, `|U|`, `E0 t U`) as an
opaque atom, so hand it the facts about those atoms first. Placeholders: `(x y : ℝ) (hy : 0 < y)`.

| Before | After |
|---|---|
| `hy : 0 < y ⊢ x < x + 16 * y` | closed |

**R12 · `cases abs_cases a`** changes the **goal list and the context**. The lemma is
`abs_cases a : (|a| = a ∧ 0 ≤ a) ∨ (|a| = -a ∧ a < 0)`; `cases` makes one goal per side, each with the
side as an unnamed hypothesis. `linarith` reads both halves of the `∧`. Placeholders: `(a b : ℝ)`.
Write `constructor <;> cases abs_cases U <;> linarith` to handle both conjuncts and both signs.

| Before | After |
|---|---|
| `⊢ a < b ∧ -a < b` | `h✝ : \|a\| = a ∧ 0 ≤ a` `⊢ a < b ∧ -a < b`, then `h✝ : \|a\| = -a ∧ a < 0` `⊢ a < b ∧ -a < b` |

---

## Part 3 · `block_nonneg` (milestone)

Statement: `t ≠ 0 → 0 ≤ (U - E0 t U) * s ^ 2 - 4 * t * s * d - E0 t U * d ^ 2`, for all reals `s d`. The
quadratic form in `(s, d)` is not a visible square; multiplied by `U - E0 t U > 0` it becomes one.

**R13 · `rw [← mul_nonneg_iff_of_pos_left hc]`** changes the **goal**. The lemma is
`mul_nonneg_iff_of_pos_left : 0 < c → (0 ≤ c * b ↔ 0 ≤ b)`; right to left it multiplies the goal by `c`.
Placeholders: `(b c : ℝ) (hc : 0 < c)`. Follow it with `rw [key]` where
`key : c * b = (…) ^ 2` (proved by R4 with `E0_quad`), then R2.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ 0 ≤ b` | `hc : 0 < c ⊢ 0 ≤ c * b` |

---

## Part 4 · `ground_state_energy`

Statement: for `t ≠ 0`, (a) some `v ≠ 0` has `H t U *ᵥ v = E0 t U • v`, and (b) every `x` has
`E0 t U * (x ⬝ᵥ x) ≤ x ⬝ᵥ (H t U *ᵥ x)`. Use the three milestones.

### Splitting the statement

**R14 · `obtain ⟨h₁, h₂⟩ := e`** changes the **context**: a fact `e : A ∧ B` becomes two facts.
Placeholders: `(A B : Prop) (e : A ∧ B)`. Use it on `E0_lt t U ht`.

| Before | After |
|---|---|
| `e : A ∧ B ⊢ G` | `h₁ : A, h₂ : B ⊢ G` |

**R15 · `refine ⟨⟨v, ?_, ?_⟩, fun x => ?_⟩`** changes the **goal list**: the witness `v` fills the `∃`, and
each `?_` becomes a goal. `fun x => ?_` proves the `∀` and puts `x` into that goal's context.
Placeholders: `{α β : Type} (A B : α → Prop) (C : β → Prop) (v : α)`.

| Before | After |
|---|---|
| `⊢ (∃ w, A w ∧ B w) ∧ ∀ (x : β), C x` | `⊢ A v`, `⊢ B v`, `x : β ⊢ C x` |

### (a1) The vector is nonzero

**R16 · `intro h`** on `≠` changes the **goal and the context**: `a ≠ b` is `a = b → False`.
Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ a ≠ b` | `h : a = b ⊢ False` |

**R17 · `congrFun h i`** changes the **context** (via `have`). `congrFun : f = g → ∀ i, f i = g i` reads one
component of an equation of functions (vectors are functions `Fin 4 → α`). Placeholders:
`{α : Type} (v w : Fin 4 → α) (h : v = w)`.

| Before | After |
|---|---|
| `h : v = w ⊢ G` | `h₂ : v 2 = w 2 ⊢ G` |

**R18 · `simp at h`** on a vector literal changes the **context**: `simp` evaluates entry 2 of `![…]`
(lemmas `Matrix.cons_val_…`), `0 2` to `0` (`Pi.zero_apply`), and `2 * c = 0` to `c = 0`
(`mul_eq_zero`, `2 ≠ 0`). Placeholders: `(a b c d : ℝ)`.

| Before | After |
|---|---|
| `h : ![a, b, 2 * c, d] 2 = 0 2` `⊢ G` | `h : c = 0 ⊢ G` |

**R19 · `exact hne heq`** **closes** `False`: `hne : a ≠ b` is a function from `a = b` to `False`.

| Before | After |
|---|---|
| `hne : a ≠ b, heq : a = b ⊢ False` | closed |

### (a2) The eigenvalue equation, entry by entry

**R20 · `ext i`** on vectors changes the **goal and the context** (lemma `funext`): two vectors are equal
when every entry is. Then `fin_cases i` gives four goals, `i = 0, 1, 2, 3` (TACTIC_STATES).
Placeholders: `{α : Type} (v w : Fin 4 → α)`.

| Before | After |
|---|---|
| `⊢ v = w` | `i : Fin 4 ⊢ v i = w i` |

`simp [H, mulVec, dotProduct, Fin.sum_univ_four]` applies R21–R24 and evaluates the literal entries by
itself. R21–R23 must be named; R24 is a `simp` lemma.

**R21 · `Matrix.mulVec`** (unfold with `simp only [mulVec]`) changes the **goal**: an entry of `M *ᵥ v` is
row `i` dotted with `v`. Placeholders: `{α : Type} [NonUnitalNonAssocSemiring α]` (α has `+`, `*`, `0`
with distributivity; `ℝ` qualifies), `(M : Matrix (Fin 4) (Fin 4) α) (v : Fin 4 → α) (i : Fin 4)`.

| Before | After |
|---|---|
| `⊢ P ((M *ᵥ v) i)` | `⊢ P ((fun j => M i j) ⬝ᵥ v)` |

**R22 · `dotProduct`** (unfold with `simp only [dotProduct]`) changes the **goal**: `v ⬝ᵥ w = ∑ i, v i * w i`.
Placeholders: `{α : Type} [Mul α] [AddCommMonoid α]` (`ℝ` qualifies), `(v w : Fin 4 → α)`.

| Before | After |
|---|---|
| `⊢ P (v ⬝ᵥ w)` | `⊢ P (∑ i, v i * w i)` |

**R23 · `Fin.sum_univ_four`** changes the **goal**: a sum over `Fin 4` becomes four terms. Placeholders:
`{β : Type} [AddCommMonoid β] (f : Fin 4 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1 + f 2 + f 3)` |

**R24 · `Pi.smul_apply`, then `smul_eq_mul`** change the **goal**: the entry of a scaled vector becomes a
product of reals. Placeholders: `(c : ℝ) (v : Fin 4 → ℝ) (i : Fin 4)`.

| Before | After `rw [Pi.smul_apply]` | After `rw [smul_eq_mul]` |
|---|---|---|
| `⊢ P ((c • v) i)` | `⊢ P (c • v i)` | `⊢ P (c * v i)` |

**R25 · `first | ring1 | linear_combination h`** **closes** each goal it runs on with the first tactic that
succeeds. After the `simp` above, two of the four entries are ring identities and two need the quadratic
`hq` (R4 with coefficient 1). `ring1` is the variant of `ring` that fails when the goal is not an identity;
plain `ring` falls back to `ring_nf` and may "succeed" without closing the goal, so `first` would stop
there. Run it on all goals with `<;>` or `all_goals`.

| Before | After `constructor` |
|---|---|
| `h : a ^ 2 = b ⊢ a + a = 2 * a ∧ a * a = b` | `⊢ a + a = 2 * a`, `⊢ a * a = b` |

`all_goals first | ring1 | linear_combination h` then closes both: `ring1` the first, `linear_combination h`
the second.

### (b) The variational bound

After `simp [H, mulVec, dotProduct, Fin.sum_univ_four]` the goal is one polynomial inequality in
`x 0, …, x 3`, `t`, `U`, `E0 t U`, with `x i * x i` (not `x i ^ 2`). It is not linear, so `linarith` fails.

**R26 · `nlinarith [p₁, p₂]`** **closes** a polynomial inequality. It adds the terms `pᵢ` (proofs) to the
hypotheses, multiplies pairs of them, and runs `linarith` (R11). It does not find good squares itself: pass
exactly the nonnegative products from the decomposition in the physics paragraph. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ 2 * a * b ≤ a ^ 2 + b ^ 2` | closed by `nlinarith [sq_nonneg (a - b)]` |

The products are built in term mode from R27–R30 and R7:

**R27 · `mul_nonneg`** changes the **context**: `mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b`.
Placeholders: `(a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)`.

| Before | After |
|---|---|
| `ha : 0 ≤ a, hb : 0 ≤ b ⊢ G` | `h : 0 ≤ a * b ⊢ G` |

**R28 · `sub_nonneg`** changes the **context**. The lemma is `sub_nonneg : 0 ≤ a - b ↔ b ≤ a`, so
`sub_nonneg.mpr hba : 0 ≤ a - b`. Placeholders: `(a b : ℝ) (hba : b ≤ a)`.

| Before | After |
|---|---|
| `hba : b ≤ a ⊢ G` | `h : 0 ≤ a - b ⊢ G` |

**R29 · `neg_nonneg`** changes the **context**. The lemma is `neg_nonneg : 0 ≤ -a ↔ a ≤ 0`, so
`neg_nonneg.mpr ha : 0 ≤ -a`. Placeholders: `(a : ℝ) (ha : a ≤ 0)`.

| Before | After |
|---|---|
| `ha : a ≤ 0 ⊢ G` | `h : 0 ≤ -a ⊢ G` |

**R30 · `hlt.le`** changes the **context**: from `hlt : a < b`, `hlt.le : a ≤ b` (lemma `LT.lt.le`; the dot
picks it from the type of `hlt`). Placeholders: `(a b : ℝ) (hlt : a < b)`.

| Before | After |
|---|---|
| `hlt : a < b ⊢ G` | `h : a ≤ b ⊢ G` |

---

## Worked combinations (W1–W5 in `guide.lean`, on objects that are not the exercise's)

**W1: a root with `√` satisfies its quadratic (R1, R2, R3, R4).** `r = (1 - √5) / 2`, goal `r² - r - 1 = 0`.
After R1 and R3:

```lean-goal
⊢ ((1 - √5) / 2) ^ 2 - (1 - √5) / 2 - 1 = 0
```

`L - R = (√5 ^ 2 - 5) / 4`, so `linear_combination h / 4` closes it.

**W2: a strict bound through `|a|` (R5, R6, R7, R11, R12).** `a - √(a ^ 2 + 1) < 0`: prove
`hlt : |a| < √(a ^ 2 + 1)` by R5, then R6 with `sq_nonneg _` and `by linarith`; then
`cases abs_cases a <;> linarith`.

**W3: nonnegativity by scaling to a square (R13, `rw [key]`, R2).** For
`0 ≤ 2 * s ^ 2 + 2 * s * d + d ^ 2 / 2`, `key : 2 * (…) = (2 * s + d) ^ 2` by `ring`, then
`rw [← mul_nonneg_iff_of_pos_left (show (0 : ℝ) < 2 by norm_num), key]` leaves

```lean-goal
⊢ 0 ≤ (2 * s + d) ^ 2
```

which `positivity` closes.

**W4: an eigenvector of `!![2, 1; 1, 2]` (R20, `fin_cases`, R21–R24).** After `ext i` and
`fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]` (`Fin.sum_univ_two` is R23 for `Fin 2`):

```lean-goal
⊢ 2 + 1 = 3
⊢ 1 + 2 = 3
```

**W5: a variational bound for the same matrix (R26).** Its lowest eigenvalue is `1`. After
`simp [mulVec, dotProduct, Fin.sum_univ_two]`:

```lean-goal
⊢ x 0 * x 0 + x 1 * x 1 ≤ x 0 * (2 * x 0 + x 1) + x 1 * (x 0 + 2 * x 1)
```

The difference is `(x 0 + x 1) ^ 2`, so `nlinarith [sq_nonneg (x 0 + x 1)]` closes it.

---

## Traps

- `E0_lt` needs `t ≠ 0`: for `t = 0`, `E0 t U = (U - |U|)/2` can be `0` or `U`, and both strict
  inequalities can fail. The strictness comes from `0 < t ^ 2` (R8 → R9 → R10).
- `linarith` and `nlinarith` treat `E0 t U` as an atom: they do not unfold it. Keep `E0` folded in Parts 3–4
  and feed the milestones in as hypotheses.
- `x ⬝ᵥ x` prints as `x ⬝ᵥ x`, and `E0 t U * x ⬝ᵥ x` already means `E0 t U * (x ⬝ᵥ x)` (Reading the goals).
- `(c • v) i` is `c * v i`; after `ext i`, `simp` produces the `*` form (R24).
- `simp [H, …]` leaves `x i * x i`, never `x i ^ 2`; `nlinarith` does not mind, `rw` would.
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases`, use `<;>` or `all_goals`.
- In `first | ring | …`, `ring` never fails (it falls back to `ring_nf`); use `ring1` (R25).
- `nlinarith` given only `hb` usually times out: it needs the two products for the `(x 0 - x 1)²` and
  `(x 2 - x 3)²` terms as well (R26–R30).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `√e ^ 2 = e` as a fact | `have h := Real.sq_sqrt (show 0 ≤ e by positivity)` | R1, R2 |
| `0 ≤` sums of squares | `positivity` | R2 |
| expand a definition | `unfold E0` | R3 |
| equation from hypotheses + ring | `linear_combination c * h` | R4 |
| compare `\|x\|` with a root | `rw [← Real.sqrt_sq_eq_abs]`, `Real.sqrt_lt_sqrt h₁ h₂` | R5, R6 |
| `0 ≤ a ^ 2` | `sq_nonneg a` | R7 |
| `t ≠ 0 → 0 < t ^ 2` | `have h := pow_pos (abs_pos.mpr ht) 2; simp at h` | R8, R9, R10 |
| linear arithmetic | `linarith` | R11 |
| split on the sign of `U` | `cases abs_cases U <;> linarith` | R12 |
| `0 ≤ b` from `0 ≤ c * b`, `0 < c` | `rw [← mul_nonneg_iff_of_pos_left hc]` | R13 |
| split a fact `A ∧ B` | `obtain ⟨h₁, h₂⟩ := e` | R14 |
| witness + three goals | `refine ⟨⟨v, ?_, ?_⟩, fun x => ?_⟩` | R15 |
| prove `v ≠ 0` | `intro h; have h₂ := congrFun h 2; simp at h₂` | R16, R17, R18 |
| `False` from `ht : t ≠ 0`, `h : t = 0` | `exact ht h` | R19 |
| vector equation → 4 entries | `ext i; fin_cases i` | R20 |
| evaluate `*ᵥ`, `⬝ᵥ`, `•` | `simp [H, mulVec, dotProduct, Fin.sum_univ_four]` | R21–R24 |
| close ring-or-quadratic entries | `first \| ring1 \| linear_combination hq` | R25 |
| polynomial inequality | `nlinarith [p₁, p₂, p₃]` | R26 |
| `0 ≤ a * b`, `0 ≤ a - b`, `0 ≤ -a`, `a ≤ b` | `mul_nonneg`, `sub_nonneg.mpr`, `neg_nonneg.mpr`, `h.le` | R27–R30 |
| see the state | infoview | |
