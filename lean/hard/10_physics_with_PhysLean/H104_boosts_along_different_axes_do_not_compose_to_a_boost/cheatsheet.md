# H104 · Boosts along different axes do not compose to a boost: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ` with `|·|` and `√`,
matrices indexed by a sum type, finite sums `∑`, the transpose `ᵀ`, and `nlinarith`; physlib's Lorentz group
`LorentzGroup d`, the boost `boost i β hβ`, its Lorentz factor `γ`, and the lemmas naming its entries.

**The physics (units with c = 1).** Spacetime has one time and `d` space coordinates; a Lorentz
transformation is a real `(1 + d) × (1 + d)` matrix. Index `0` is time, index `k` is space axis `k`. The
boost along axis `i` with speed `β` (`|β| < 1`) is, with $\gamma(\beta) = 1/\sqrt{1 - \beta^2}$,

$$B_i(\beta)_{00} = B_i(\beta)_{ii} = \gamma, \qquad B_i(\beta)_{0i} = B_i(\beta)_{i0} = -\gamma\beta, \qquad
B_i(\beta)_{jk} = \delta_{jk} \ \text{for every other pair } (j, k),$$

where $\delta_{jk}$ is 1 if $j = k$ and 0 otherwise. So a boost is a **symmetric** matrix, $B^\mathsf{T} = B$.
For $i \ne j$ let $C = B_i(\beta_1)\,B_j(\beta_2)$ and $\gamma_k = \gamma(\beta_k)$. Then, with
$C_{rc} = \sum_l B_i(\beta_1)_{rl}\,B_j(\beta_2)_{lc}$:

$$C_{ij} = \underbrace{(-\gamma_1\beta_1)(-\gamma_2\beta_2)}_{l = 0} + \underbrace{\gamma_1 \cdot 0}_{l = i} = \gamma_1\beta_1\gamma_2\beta_2 \ne 0,
\qquad C_{ji} = \sum_l \delta_{jl}\,B_j(\beta_2)_{li} = B_j(\beta_2)_{ji} = 0,$$

the second because row $j$ of $B_i(\beta_1)$ is a row of the identity. $C_{ij} \ne C_{ji}$, so $C$ is not
symmetric and cannot be any boost $B_k(\beta)$. (The rotation missing from $C$ is the Thomas–Wigner rotation.)

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`apply`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid M]` is a
  requirement on a type (a *type class*). Each entry says which familiar types meet it.
- `|` cannot appear literally inside a table, so `|a|` is written `\|a\|` there.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `\|β\|` | absolute value of `β : ℝ` |
| `√x` | `Real.sqrt x`; it is `0` for `x < 0` |
| `γ β` | physlib's `LorentzGroup.γ β = 1 / √(1 - β ^ 2)`, the Lorentz factor (R3) |
| `Fin 1 ⊕ Fin d` | the index type "time or one of `d` space axes"; `⊕` is the sum (disjoint union) type |
| `Sum.inl 0`, `Sum.inr k` | the time index, and space axis `k : Fin d` |
| `LorentzGroup d`, printed `↑(𝓛 d)` | the Lorentz group: the set of real matrices on `Fin 1 ⊕ Fin d` preserving the Minkowski metric, used as a type (a subtype) |
| `↑Λ`, written `Λ.1` | the matrix underlying `Λ : LorentzGroup d` (the coercion out of the subtype) |
| `↑Λ r c` | entry in row `r`, column `c` of that matrix |
| `boost i β hβ` | the boost along axis `i : Fin d` with speed `β`; `hβ : \|β\| < 1` |
| `A * B` | product in the group (and of matrices): first `B`, then `A` |
| `Mᵀ` | `Matrix.transpose M`: `Mᵀ r c = M c r` (R26) |
| `∑ l, f l` | the sum of `f l` over every `l` of a finite type; it is `∑ l ∈ Finset.univ, f l` |
| `∑ x ∈ s, f x` | the sum over a finite set `s : Finset ι` (a `Finset` is a finite set of elements of `ι`) |
| `Finset.univ` | the `Finset` of all elements of a finite type (here all of `Fin d`) |
| `∀ x ∈ s, Q x` | `∀ x, x ∈ s → Q x`: two binders, so two names in `intro` (R13) |
| `-γ β * β` | `(-(γ β)) * β`, i.e. $-\gamma\beta$; function application binds tightest, then `-`, then `*` |
| `j_1`, `a₁`, `a₂` | names Lean picks for the bound summation index |
| `if j = k then 1 else 0` | Lean's `ite`; with `j = k` decidable it is `δⱼₖ` |
| `a✝` | an unnamed hypothesis (from `intro l _`); you cannot type its name |
| `a ≠ b` | `a = b → False` (R22) |
| `case pos`, `case neg` | the two goals of `by_cases`: the condition holds / fails |

---

## Part 1 · `gamma_ne_zero` (milestone)

Statement: `|β| < 1 → γ β ≠ 0`. Prove it first: Part 4 needs it twice to show `γ β₁ * β₁ * (γ β₂ * β₂) ≠ 0`.
First the fact `0 < 1 - β ^ 2` (R1, R2), then open `γ` and peel off `1 / ·` and `√` (R3, R4, R5).
`simp [γ, Real.sqrt_ne_zero', this]` performs R3–R5 at once.

**R1 · `rw [abs_lt] at h`** changes the **context**. The lemma is `abs_lt : |a| < b ↔ -b < a ∧ a < b`; `rw` with
an `↔` replaces one side by the other, `at h` only in `h`. Placeholders: `(a b : ℝ)` (any ordered additive group).
Inside `have … := by rw [abs_lt] at hβ; …` the change stays inside that proof.

| Before | After |
|---|---|
| `h : \|a\| < b`, `⊢ P` | `h : -b < a ∧ a < b ⊢ P` |

**R2 · `nlinarith`** **closes** a polynomial inequality over `ℝ`. It splits `∧` hypotheses, multiplies pairs of
hypotheses (here `(2 + a) * (2 - a) > 0`), then finds a linear combination. Placeholders: `(a : ℝ)`
`(h : -2 < a ∧ a < 2)`, goal `0 < 4 - a ^ 2`.

**R3 · `unfold γ`** changes the **goal**: `γ β` becomes its definition. Placeholders: `(β : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (γ β)` | `⊢ P (1 / √(1 - β ^ 2))` |

**R4 · `apply one_div_ne_zero`** changes the **goal**. The lemma is `one_div_ne_zero : a ≠ 0 → 1 / a ≠ 0`;
`apply` leaves its premise. Placeholders: `(a : ℝ)` (any `GroupWithZero`: `ℝ`, `ℚ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ 1 / a ≠ 0` | `⊢ a ≠ 0` |

**R5 · `rw [Real.sqrt_ne_zero']`** changes the **goal**. The lemma is `Real.sqrt_ne_zero' : √x ≠ 0 ↔ 0 < x`.
Placeholders: `(x : ℝ)`. (`Real.sqrt_ne_zero` without `'` needs `0 ≤ x` and is not the one you want.)

| Before | After |
|---|---|
| `⊢ √x ≠ 0` | `⊢ 0 < x` |

---

## Part 2 · `entry_ij` (milestone)

Statement: for `i ≠ j`, entry `(Sum.inr i, Sum.inr j)` of `boost i β₁ h₁ * boost j β₂ h₂` is
`γ β₁ * β₁ * (γ β₂ * β₂)`. Expand the entry into a time term plus a spatial sum (R6, R7, R8), let `simp` evaluate
the time term (R9, R10, R11), then show every term of the spatial sum is 0 (R12–R18).

### Expanding one entry of a product

**R6 · `simp only [lorentzGroupIsGroup_mul_coe]`** changes the **goal**. The lemma is
`lorentzGroupIsGroup_mul_coe (A B : LorentzGroup d) : ↑(A * B) = ↑A * ↑B`: the matrix of a group product is the
product of the matrices. Placeholders: `{d : ℕ} (A B : LorentzGroup d) (r c : Fin 1 ⊕ Fin d)`.

| Before | After |
|---|---|
| `⊢ P (↑(A * B) r c)` | `⊢ P ((↑A * ↑B) r c)` |

**R7 · `simp only [Matrix.mul_apply]`** changes the **goal**: an entry of a matrix product becomes a sum over the
middle index, $(MN)_{rc} = \sum_l M_{rl} N_{lc}$. Placeholders:
`{d : ℕ} (M N : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (r c : Fin 1 ⊕ Fin d)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) r c)` | `⊢ P (∑ j, M r j * N j c)` |

**R8 · `simp only [Fintype.sum_sum_type]`** changes the **goal**. The lemma is
`∑ x : α ⊕ β, f x = ∑ a, f (Sum.inl a) + ∑ b, f (Sum.inr b)`: split the sum into its time part (over `Fin 1`)
and its space part (over `Fin d`). Placeholders: `{d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ)` (any `AddCommMonoid` target).

| Before | After |
|---|---|
| `⊢ P (∑ x, f x)` | `⊢ P (∑ a₁, f (Sum.inl a₁) + ∑ a₂, f (Sum.inr a₂))` |

### What plain `simp` does next

**R9 · `Fin.sum_univ_one`** changes the **goal**: a sum over `Fin 1` is its only term,
`∑ a : Fin 1, f a = f 0`. Plain `simp` does this by itself (via `Finset.univ_unique`, `Finset.sum_singleton`).
Placeholders: `(f : Fin 1 → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ a, f a)` | `⊢ P (f 0)` |

**R10 · the `@[simp]` entries of a boost** change the **goal**. physlib tags four lemmas `@[simp]`, so plain
`simp` evaluates these entries without being told:
`boost_inl_0_inl_0 : ↑(boost i β hβ) (Sum.inl 0) (Sum.inl 0) = γ β`,
`boost_inr_self_inr_self : … (Sum.inr i) (Sum.inr i) = γ β`,
`boost_inl_0_inr_self : … (Sum.inl 0) (Sum.inr i) = -γ β * β`,
`boost_inr_self_inl_0 : … (Sum.inr i) (Sum.inl 0) = -γ β * β`.
All other entries need a lemma with a hypothesis `j ≠ i` (R16, R18, R20). Placeholders:
`{d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1)`, and a 4-argument `P : ℝ → ℝ → ℝ → ℝ → Prop`.

| Before | After |
|---|---|
| `⊢ P (↑(boost i β hβ) (Sum.inl 0) (Sum.inl 0)) (↑(boost i β hβ) (Sum.inr i) (Sum.inr i)) (↑(boost i β hβ) (Sum.inl 0) (Sum.inr i)) (↑(boost i β hβ) (Sum.inr i) (Sum.inl 0))` | `⊢ P (γ β) (γ β) (-γ β * β) (-γ β * β)` |

**R11 · `add_eq_left`** changes the **goal**. The lemma is `add_eq_left : a + b = a ↔ b = 0`. After R9 and R10
the time term `(-(γ β₁ * β₁)) * (-(γ β₂ * β₂))` equals the right side, and `simp` uses this lemma to drop it:
what is left is "the spatial sum is 0". Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ a + b = a` | `⊢ b = 0` |

### Every term of the spatial sum is zero

**R12 · `apply Finset.sum_eq_zero`** changes the **goal**. The lemma is
`Finset.sum_eq_zero : (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0`. Placeholders: `{d : ℕ} (f : Fin d → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ l, f l = 0` | `⊢ ∀ x ∈ Finset.univ, f x = 0` |

**R13 · `intro l _`** changes the **goal and the context**: `∀ x ∈ s, Q x` is `∀ x, x ∈ s → Q x`, so two
`intro`s; `_` leaves the membership proof unnamed (`a✝`). Placeholders: `{d : ℕ} (Q : Fin d → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ l ∈ Finset.univ, Q l` | `l : Fin d, a✝ : l ∈ Finset.univ ⊢ Q l` |

**R14 · `by_cases hl : l = i`** changes the **goal list and the context**: two goals, `case pos` with
`hl : l = i` and `case neg` with `hl : ¬l = i`. Placeholders: `{d : ℕ} (l i : Fin d)`.

| Before | After |
|---|---|
| `⊢ P` | `hl : l = i ⊢ P`, `hl : ¬l = i ⊢ P` |

**R15 · `subst hl`** with `hl : l = i` changes the **context**: `i` (the variable on the right) disappears,
every `i` becomes `l`, and hypotheses about `i` are restated about `l`. Placeholders: `{d : ℕ} (l i j : Fin d)`,
`(hij : i ≠ j)`.

| Before | After |
|---|---|
| `hij : i ≠ j, hl : l = i ⊢ P l i` | `hij : l ≠ j ⊢ P l l` |

**R16 · `rw [boost_inr_other_inr hβ hj]`** changes the **goal**. The lemma is
`boost_inr_other_inr (hβ : |β| < 1) (hj : j ≠ i) : ↑(boost i β hβ) (Sum.inr j) (Sum.inr k) = if j = k then 1 else 0`:
a space row `j` other than the boosted axis `i` is a row of the identity matrix. Note the order: the row
index `j` comes first in the hypothesis `j ≠ i`. Placeholders: `{d : ℕ} (i j k : Fin d) (β : ℝ) (hβ : |β| < 1)`.

| Before | After |
|---|---|
| `⊢ P (↑(boost i β hβ) (Sum.inr j) (Sum.inr k))` | `⊢ P (if j = k then 1 else 0)` |

**R17 · `simp [hne]`** with `hne : a ≠ b` changes the **goal**: it rewrites `a = b` to `False` and takes the `else`
branch. In the exercise `simp` then also turns `x * 0` into `0` and closes the goal. Placeholders:
`{d : ℕ} (a b : Fin d) (x y : ℝ)`.

| Before | After |
|---|---|
| `hne : a ≠ b ⊢ P (if a = b then x else y)` | `⊢ P y` |

**R18 · `rw [boost_inr_self_inr_other hβ hj]`** changes the **goal**. The lemma is
`boost_inr_self_inr_other (hβ : |β| < 1) (hj : j ≠ i) : ↑(boost i β hβ) (Sum.inr i) (Sum.inr j) = 0`: in row `i`
of the boost along `i`, every other space column is 0. Placeholders: as in R16.

| Before | After |
|---|---|
| `⊢ P (↑(boost i β hβ) (Sum.inr i) (Sum.inr j))` | `⊢ P 0` |

In the exercise: in `case pos` (`l = i`), after R15 the second factor is entry `(Sum.inr l, Sum.inr j)` of
`boost j`, a row `l ≠ j`: R16 with `hij`, then R17 with `hij`. In `case neg` the first factor is R18 with `hl`.
Both are a single `simp [lemma …, …]` call.

---

## Part 3 · `entry_ji` (milestone)

Statement: for `i ≠ j`, entry `(Sum.inr j, Sum.inr i)` of the same product is `0`. Expand as in Part 2 (R6, R7,
R8), then one `simp` with three named entries: row `j` of `boost i` is a row of the identity (R20 for the time
column, R16 for the space columns, both need `j ≠ i`, i.e. `Ne.symm hij` by R19), the identity row picks one
term of the sum (R21), and that term is entry `(Sum.inr j, Sum.inr i)` of `boost j`, which is 0 (R18 with `hij`).

**R19 · `Ne.symm`** changes the **context** (inside a `have`, or used directly as an argument). From
`h : a ≠ b` it gives `b ≠ a`. Placeholders: `{d : ℕ} (a b : Fin d)`.

| Before | After `have h' : b ≠ a := Ne.symm h` |
|---|---|
| `h : a ≠ b ⊢ P` | `h' : b ≠ a ⊢ P` |

**R20 · `rw [boost_inr_other_inl_0 hβ hj]`** changes the **goal**. The lemma is
`boost_inr_other_inl_0 (hβ : |β| < 1) (hj : j ≠ i) : ↑(boost i β hβ) (Sum.inr j) (Sum.inl 0) = 0`. Placeholders:
as in R16.

| Before | After |
|---|---|
| `⊢ P (↑(boost i β hβ) (Sum.inr j) (Sum.inl 0))` | `⊢ P 0` |

**R21 · `Finset.sum_ite_eq`** (applied by plain `simp`, after `ite_mul : (if c then x else y) * z = if c then x * z else y * z`)
changes the **goal**. The lemma is
`Finset.sum_ite_eq s a b : (∑ x ∈ s, if a = x then b x else 0) = if a ∈ s then b a else 0`, and `a ∈ Finset.univ`
is true: a sum against a row of the identity picks out one term. Placeholders: `{d : ℕ} (j : Fin d) (f : Fin d → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ a, (if j = a then 1 else 0) * f a)` | `⊢ P (f j)` |

### Worked combination (W2, not the exercise's object)

**W2: an entry of a boost squared.** `(boost i β hβ * boost i β hβ).1 (Sum.inr j) (Sum.inr j) = 1` for `j ≠ i`:
R6, R7, R8 in one `simp only` give

```lean-goal
⊢ ∑ a₁, ↑(boost i β hβ) (Sum.inr j) (Sum.inl a₁) * ↑(boost i β hβ) (Sum.inl a₁) (Sum.inr j) + ∑ a₂, ↑(boost i β hβ) (Sum.inr j) (Sum.inr a₂) * ↑(boost i β hβ) (Sum.inr a₂) (Sum.inr j) = 1
```

and `simp [boost_inr_other_inl_0 hβ hj, boost_inr_other_inr hβ hj]` closes it (R20, R16, R21, then R16 again on
the picked term `if j = j then 1 else 0`). This is the shape of Part 3.

---

## Part 4 · `boost_mul_boost_ne_boost`

Statement: for `i ≠ j`, `β₁ ≠ 0`, `β₂ ≠ 0`: `∀ k β hβ, boost i β₁ h₁ * boost j β₂ h₂ ≠ boost k β hβ`. Assume the
equation `h` (R22). Take the symmetry of `boost k β hβ` (R23) at entry `(Sum.inr i, Sum.inr j)` (R24), replace
`boost k β hβ` by the product (R25), remove the transpose (R26), and evaluate both sides with the milestones
`entry_ij`, `entry_ji` (`rw [...] at e`). Then `e : 0 = γ β₁ * β₁ * (γ β₂ * β₂)`, against a nonzero product built
from `gamma_ne_zero` (R27), and R28 closes `False`.

**R22 · `intro h`** on `a ≠ b` changes the **goal and the context**: `a ≠ b` is notation for `a = b → False`, so
`intro` assumes the equation and the goal becomes `False`. In the exercise write `intro k β hβ h`: three `∀`
variables, then the equation. Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ a ≠ b` | `h : a = b ⊢ False` |

**R23 · `boost_transpose_matrix_eq_self i hβ`** changes the **context** (with `have`). The lemma is
`boost_transpose_matrix_eq_self (i : Fin d) (hβ : |β| < 1) : (↑(boost i β hβ))ᵀ = ↑(boost i β hβ)`: the
boost's matrix is symmetric. `β` is implicit, read off `hβ`. Placeholders: `{d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1)`.

| Before | After `have hs := boost_transpose_matrix_eq_self i hβ` |
|---|---|
| `⊢ P` | `hs : (↑(boost i β hβ))ᵀ = ↑(boost i β hβ) ⊢ P` |

**R24 · `congrFun (congrFun hM r) c`** changes the **context** (with `have`). `congrFun : f = g → ∀ a, f a = g a`;
a matrix is a function of the row returning a function of the column, so two applications give one entry.
Placeholders: `{d : ℕ} (M N : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (hM : M = N) (r c : Fin 1 ⊕ Fin d)`.

| Before | After `have e := congrFun (congrFun hM r) c` |
|---|---|
| `hM : M = N ⊢ P` | `e : M r c = N r c ⊢ P` |

**R25 · `rw [← h] at e`** with `h : a = b` changes the **context**: every `b` in `e` becomes `a`. In the exercise
`b` is `boost k β hβ`, which sits inside `↑(…)` on both sides of `e`. Placeholders: `{α : Type} (a b : α)`,
`(Q : α → Prop)`.

| Before | After |
|---|---|
| `e : Q b ⊢ Q a` | `e : Q a ⊢ Q a` |

**R26 · `simp only [transpose_apply] at e`** changes the **context**. The lemma is
`Matrix.transpose_apply : Mᵀ r c = M c r`. Placeholders: as in R24.

| Before | After |
|---|---|
| `e : Mᵀ r c = N r c ⊢ M c r = N r c` | `e : M c r = N r c ⊢ M c r = N r c` |

After R26, `e` reads `↑(A * B) (Sum.inr j) (Sum.inr i) = ↑(A * B) (Sum.inr i) (Sum.inr j)` for the product
`A * B`; `rw [entry_ij hij, entry_ji hij] at e` turns it into `0 = γ β₁ * β₁ * (γ β₂ * β₂)`. Both sides
are entries of the same product; each milestone's left side matches exactly one of them.

**R27 · `mul_ne_zero`** changes the **context** (with `have`). The lemma is
`mul_ne_zero : a ≠ 0 → b ≠ 0 → a * b ≠ 0`. Nest it for a product of four factors:
`mul_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero h3 h4)` for `a * b * (c * d)` (`*` groups to the left). Placeholders:
`(a b : ℝ)` (any type with no zero divisors).

| Before | After `have hab : a * b ≠ 0 := mul_ne_zero ha hb` |
|---|---|
| `⊢ P` | `hab : a * b ≠ 0 ⊢ P` |

**R28 · `exact hne e.symm`** **closes** `False`. `e.symm` is `Eq.symm e`, the equation flipped; `hne : a ≠ 0` is a
function from `a = 0` to `False`, so applying it gives `False`. Placeholders: `(a : ℝ) (hne : a ≠ 0) (e : 0 = a)`.

### Worked combinations (W1, W3, on objects that are not the exercise's)

**W1: one boost is symmetric entrywise.** `have e := congrFun (congrFun (boost_transpose_matrix_eq_self i hβ) (Sum.inl 0)) (Sum.inr j)`
(R23, R24) and `simp only [transpose_apply] at e` (R26) give exactly the goal:

```lean-goal
⊢ ↑(boost i β hβ) (Sum.inr j) (Sum.inl 0) = ↑(boost i β hβ) (Sum.inl 0) (Sum.inr j)
```

**W3: a nonzero product is not 0.** From `ha : a ≠ 0`, `hb : b ≠ 0`, `e : 0 = a * b`:
`have hne := mul_ne_zero ha hb` (R27), then `exact hne e.symm` (R28).

---

## Traps

- Unfolding the boost with `simp [boost, …]` leaves nested `if`s on `Sum` indices whose shape depends on
  whether you supplied `hij` or `Ne.symm hij`. Use the named entry lemmas (R10, R16, R18, R20) instead.
- The entry lemmas take `j ≠ i` with the *other* index first and the boost's axis second. For `boost i` with
  `hij : i ≠ j` you need `Ne.symm hij`; for `boost j` you pass `hij` itself.
- `subst hl` with `hl : l = i` removes `i`, not `l`: afterwards `hij` reads `l ≠ j`.
- `rw [abs_lt] at hβ` inside a `have … := by` changes `hβ` only inside that proof.
- `rw [← h] at e` with `h : product = boost k β hβ`, not `rw [h] at e`: `e` mentions the boost, not the product.
- `Real.sqrt_ne_zero'` (with `'`) is the `↔ 0 < x` form; `Real.sqrt_ne_zero` asks for `0 ≤ x` first.
- `t1 ; t2` runs `t2` on the first goal only. Handle the two `by_cases` goals with `·`.
- The main theorem's hole is a term, `:= sorry` on the line after `-- END SPEC`. Replace `sorry` with `by`
  followed by indented tactics (the milestones already start with `:= by`).
- `simp [γ, Real.sqrt_ne_zero', this]` reaches the same end as R3 → R4 → R5 by another route (`one_div`,
  `inv_eq_zero`), so its intermediate goals differ from the R3–R5 tables; both routes work.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `\|β\| < 1` → two inequalities | `rw [abs_lt] at hβ` | R1 |
| `0 < 1 - β ^ 2` | `nlinarith` | R2 |
| open `γ` | `unfold γ` / `simp [γ]` | R3 |
| `1 / a ≠ 0`, `√x ≠ 0` | `one_div_ne_zero`, `Real.sqrt_ne_zero'` | R4, R5 |
| entry of a group product | `simp only [lorentzGroupIsGroup_mul_coe, Matrix.mul_apply, Fintype.sum_sum_type]` | R6, R7, R8 |
| time term, `@[simp]` boost entries | `simp` | R9, R10, R11 |
| sum of zeros | `apply Finset.sum_eq_zero; intro l _` | R12, R13 |
| `l = i` or not | `by_cases hl : l = i` | R14 |
| substitute a variable | `subst hl` | R15 |
| other row of a boost | `boost_inr_other_inr hβ hj`, `boost_inr_other_inl_0 hβ hj` | R16, R20 |
| `if` with false condition | `simp [hne]` | R17 |
| boost row `i`, other space column | `boost_inr_self_inr_other hβ hj` | R18 |
| flip `≠` | `Ne.symm h` | R19 |
| sum against an identity row | `simp` (`Finset.sum_ite_eq`) | R21 |
| prove `a ≠ b` | `intro h` (goal `False`) | R22 |
| a boost is symmetric | `boost_transpose_matrix_eq_self k hβ` | R23 |
| matrix equation → one entry | `congrFun (congrFun hM r) c` | R24 |
| rewrite inside a hypothesis | `rw [← h] at e` | R25 |
| remove `ᵀ` | `simp only [transpose_apply] at e` | R26 |
| product nonzero | `mul_ne_zero h1 h2` | R27 |
| `≠` against `=` | `exact hne e.symm` | R28 |
| see the state | infoview | |
