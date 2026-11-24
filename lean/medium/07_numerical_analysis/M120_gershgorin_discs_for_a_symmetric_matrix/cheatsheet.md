# M120 · Gershgorin discs for a symmetric matrix: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`constructor`, `<;>`, `all_goals`, `rw … at h`, `simp … at h`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's matrices over `ℝ`, eigenvalues of
a matrix, metric balls, finite sums `∑`, absolute value, the Gershgorin circle theorem, and `linarith`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`obtain`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" and `Q` "the rest of a hypothesis": the step changes only the part inside
  `P (…)` / `Q (…)`. `G : Prop` is a goal the step leaves alone.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[NormedField K]` is
  a requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- In this problem most steps act on a hypothesis (`rw [...] at hk`, `simp [...] at hk`). Several entries
  are shown on the goal instead; the same tactic with `at hk` does the same thing to `hk`.

## Reading the goals

| You see | It means |
|---|---|
| `Matrix (Fin 3) (Fin 3) ℝ` | 3×3 real matrices. Rows and columns are indexed by `Fin 3 = {0, 1, 2}` |
| `!![a, b, c; d, e, f; g, h, i]` | the matrix with rows `a b c`, `d e f`, `g h i` (rows split by `;`) |
| `M i j` | the entry in row `i`, column `j`, counted from 0 |
| `![a, b, c]` | the vector `Fin 3 → α` with entries `a, b, c`; `![a, b, c] j` is its entry `j`. `M 0 j` with `j` unknown evaluates to `![…] j` (row 0) |
| `Matrix.toLin' M` | `M` as a linear map `x ↦ M *ᵥ x` on `Fin n → K`; `M *ᵥ x` is the matrix `M` times the column vector `x` |
| `Module.End.HasEigenvalue f μ` | `μ` is an eigenvalue of the linear map `f`: some `v ≠ 0` has `f v = μ • v` (`•` = scalar times vector). `Module.End` = linear maps from a space to itself |
| `Metric.closedBall c r` | the closed ball `{x ∣ dist x c ≤ r}`; on `ℝ` the interval `[c - r, c + r]` |
| `dist x y` | the distance; on `ℝ` it is `\|x - y\|` (R3) |
| `‖x‖` | the norm; on `ℝ` it is `\|x\|` (R6) |
| `\|x\|` | absolute value |
| `∑ x, f x` | the sum of `f x` over all `x` of a finite type (here all of `Fin 3`) |
| `∑ j ∈ s, f j` | the sum over the finite set `s` only |
| `Finset.univ.erase k` | all indices except `k` (`Finset.univ` = every element of the type) |
| `i.succ`, `Fin.succ i` | `i + 1`, as an index into `Fin (n + 1)` when `i : Fin n` |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases`; `⟨0, ⋯⟩` is the pair (value `0`, hidden proof `⋯` that `0 < 3`) |
| `case «0»`, `case «1»`, `case «2»` | the goals for rows 0, 1, 2 after `fin_cases` |
| `case left`, `case right` | the two halves of `A ∧ B` after `constructor`; after `fin_cases` they print as `case «0».left` etc. |
| `NormedField K` | `K` is a field with an absolute value `‖·‖` (`ℝ`, `ℂ`) |
| `Fintype n`, `DecidableEq n` | `n` is a finite type whose elements can be compared (`Fin 3` is both) |

---

## Part 1 · `eigenvalue_bounds`

Statement: if `μ : ℝ` is an eigenvalue of the matrix `A` (as the linear map `Matrix.toLin' A`), then
`2 ≤ μ ∧ μ ≤ 6`.

**Why it is true.** For an `n×n` matrix `M` with entries `M k j` in a field `K` that has an absolute
value (`ℝ` or `ℂ`), the **Gershgorin disc** of row `k` has center `M k k` (the diagonal entry) and radius
$r_k = \sum_{j \ne k} |M_{kj}|$ (the off-diagonal entries of that row). The **Gershgorin circle theorem**:
every eigenvalue `μ` of `M` lies in at least one disc, i.e. some row `k` has $|\mu - M_{kk}| \le r_k$.
Over `ℝ` a disc is the interval $[M_{kk} - r_k,\ M_{kk} + r_k]$. Proof idea: take an eigenvector `v`
and the index `k` where `|v k|` is largest; row `k` of `M v = μ v` gives the bound.

Plan: Gershgorin gives one row's disc (R1); turn the disc into `|μ - A k k| ≤ radius`
(R2, R3); split on the row (R4); evaluate the center and radius to numbers (R5–R8); then turn each
`|μ - c| ≤ r` into the two bounds (R9, R10).

### From the eigenvalue to one inequality

**R1 · `obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ`** changes the **context**: it adds the row `k` and the
fact `hk` that `μ` is in that row's disc. The lemma (root namespace, file
`Mathlib/LinearAlgebra/Matrix/Gershgorin.lean`) is

`eigenvalue_mem_ball : Module.End.HasEigenvalue (Matrix.toLin' M) μ → ∃ k, μ ∈ Metric.closedBall (M k k) (∑ j ∈ Finset.univ.erase k, ‖M k j‖)`

and `obtain ⟨k, hk⟩ := e` unpacks the `∃` of `e`. Placeholders:
`{K : Type} [NormedField K] {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n K) (μ : K)`; `K = ℝ`,
`n = Fin 3` here.

| Before | After |
|---|---|
| `hμ : Module.End.HasEigenvalue (Matrix.toLin' M) μ ⊢ G` | `k : n ⊢ G` |

and the context also gains `hk : μ ∈ Metric.closedBall (M k k) (∑ j ∈ Finset.univ.erase k, ‖M k j‖)`.

**R2 · `rw [Metric.mem_closedBall] at hx`** changes the **context**. The lemma is
`Metric.mem_closedBall : y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε`. Placeholders:
`{α : Type} [PseudoMetricSpace α] (x c : α) (r : ℝ)` (α has a distance; `ℝ` and `ℂ` qualify).

| Before | After |
|---|---|
| `hx : x ∈ Metric.closedBall c r ⊢ G` | `hx : dist x c ≤ r ⊢ G` |

**R3 · `rw [Real.dist_eq] at hx`** changes the **context**. The lemma is `Real.dist_eq : dist x y = |x - y|`
for `x y : ℝ`. Placeholders: `(x y r : ℝ)`.

| Before | After |
|---|---|
| `hx : dist x y ≤ r ⊢ G` | hx : \|x - y\| ≤ r ⊢ G |

R2 and R3 can go in one call: `rw [Metric.mem_closedBall, Real.dist_eq] at hk`. Do this before R4, once
instead of three times.

### One case per row

**R4 · `fin_cases k`** changes the **goal list and the context**: `k` leaves the context and there is one goal
per value `0, 1, 2`. Every hypothesis mentioning `k` (here `hk`) is rewritten with that value. Placeholders:
`(P Q : Fin 3 → Prop) (k : Fin 3)` with `hk : Q k`.

| Before | After |
|---|---|
| `k : Fin 3 ⊢ P k` | `⊢ P ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩)`, `⊢ P ((fun i => i) ⟨2, ⋯⟩)` |

In each goal `hk : Q k` has become `hk : Q ((fun i => i) ⟨0, ⋯⟩)` (resp. `1`, `2`). Follow it with `<;>` so
the next tactic runs on all three goals.

### Evaluating the disc of one row

`simp [A, Fin.sum_univ_succ] at hk` does R5–R8 in one call: R6 and R7 are `simp` lemmas, R5 needs the name of
your matrix, and R8 must be named.

**R5 · `simp [D]`** changes the **goal** (with `at hk`: the **context**). It unfolds the definition `D` and
evaluates entries of `!![…]`: a fixed entry becomes a number, an entry `D 0 j` with unknown column `j`
becomes the row vector applied to `j`. Placeholders: `D` defined by
`def D : Matrix (Fin 3) (Fin 3) ℝ := !![2, 0, 1; 0, 3, 0; 1, 0, 7]`, `(P : ℝ → ℝ → Prop) (j : Fin 3)`.

| Before | After |
|---|---|
| `⊢ P (D 2 2) (D 0 j)` | `⊢ P 7 (![2, 0, 1] j)` |

**R6 · `rw [Real.norm_eq_abs] at hk`** changes the **context**. The lemma is `Real.norm_eq_abs : ‖r‖ = |r|`
for `r : ℝ`: the radius `∑ … ‖M k j‖` is a sum of absolute values. `simp` applies it by itself.
Placeholders: `(r : ℝ) (Q : ℝ → Prop)`.

| Before | After |
|---|---|
| `hk : Q ‖r‖ ⊢ G` | hk : Q \|r\| ⊢ G |

**R7 · `rw [Finset.sum_erase_eq_sub (Finset.mem_univ a)]`** changes the **goal**. The lemma is
`Finset.sum_erase_eq_sub : a ∈ s → ∑ x ∈ s.erase a, f x = ∑ x ∈ s, f x - f a`; its argument proves `a ∈ s`,
here `Finset.mem_univ a : a ∈ Finset.univ`. `simp` applies it by itself (and proves `a ∈ Finset.univ`).
Placeholders: `{β : Type} [AddCommGroup β] (f : Fin 3 → β) (a : Fin 3)` (β has `+`, `-`, `0`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (∑ x ∈ Finset.univ.erase a, f x)` | `⊢ P (∑ x, f x - f a)` |

**R8 · `Fin.sum_univ_succ`** changes the **goal**. The lemma is
`Fin.sum_univ_succ : ∑ i : Fin (n + 1), f i = f 0 + ∑ i : Fin n, f i.succ`. `rw` peels one term;
`simp [Fin.sum_univ_succ]` peels them all and cleans up `Fin.succ 0` to `1`. `simp` does **not** use it
unless you name it. Placeholders: `{β : Type} [AddCommMonoid β] (f : Fin 3 → β)`.

| Before | After `rw [Fin.sum_univ_succ]` | After `simp [Fin.sum_univ_succ]` |
|---|---|---|
| `⊢ P (∑ x, f x)` | `⊢ P (f 0 + ∑ i, f i.succ)` | `⊢ P (f 0 + (f 1 + f 2))` |

### From `|μ - c| ≤ r` to the two bounds

Split the goal `2 ≤ μ ∧ μ ≤ 6` with `constructor` (TACTIC_STATES): `linarith` proves one inequality, not a
conjunction.

**R9 · `abs_le`** gives a new fact in the **context**. The lemma is `abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b`;
`abs_le.mp hab` (`.mp` = left to right) turns `hab : |a| ≤ b` into the two linear facts. Placeholders:
`{α : Type} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b : α)` (an ordered additive group;
`ℝ` qualifies).

| Before | After `have h' := abs_le.mp hab` |
|---|---|
| hab : \|a\| ≤ b ⊢ G | `h' : -b ≤ a ∧ a ≤ b ⊢ G` |

**R10 · `linarith [e]`** **closes** a goal `s ≤ t`, `s < t`, `s = t` (or `False`) that follows by adding
and scaling the hypotheses and the extra facts `e` linearly. A conjunction `e` contributes both halves.
Anything non-linear, such as `|a - b|`, is an unknown to it, so it needs R9 to see inside `|·|`.
Unnormalised numbers like `1 + (4 + 1) - 4` are fine. Placeholders: `(a b c : ℝ)` and `hab : |a - b| ≤ c`.

| Before | After |
|---|---|
| `⊢ b - c ≤ a` (with `hab` in the context) | closed by `linarith [abs_le.mp hab]` |

### Worked combinations (W1–W2, on the matrix `D` of R5, not the exercise's)

**W1: one row's disc as an explicit inequality.** Row 0 of `D`: center `2`, radius `|0| + |1| = 1`. Shown on
the goal; at a hypothesis use the same calls with `at hk`. R2 and R3 in one `rw`, then R5–R8 in one `simp`:

```lean-goal
⊢ μ ∈ Metric.closedBall (D 0 0) (∑ j ∈ Finset.univ.erase 0, ‖D 0 j‖)
⊢ |μ - D 0 0| ≤ ∑ j ∈ Finset.univ.erase 0, ‖D 0 j‖
⊢ |μ - 2| ≤ 1
```

**W2: disc to interval.** With `h : |μ - 2| ≤ 1`: `constructor`, then `all_goals linarith [abs_le.mp h]` (R9 → R10):

| Before | After `constructor` |
|---|---|
| `⊢ 1 ≤ μ ∧ μ ≤ 3` | `⊢ 1 ≤ μ`, `⊢ μ ≤ 3` |

---

## Traps

- `simp [A] at hk` without `Fin.sum_univ_succ` stops at `∑ x, |![…] x| - c`; `linarith` cannot see inside
  the sum. Name R8.
- `linarith` closes one inequality; a goal `X ∧ Y` must be split first (`constructor`).
- `linarith` treats `|μ - c|` as an unknown: pass `abs_le.mp hk`, not `hk`.
- `abs_le` is an `↔`; as a proof term use `abs_le.mp hk`, or rewrite with `rw [abs_le] at hk`.
- After `fin_cases k` there are three goals: `t1 ; t2` runs `t2` on the first only. Use `<;>` or `all_goals`.
- `simp` may leave a radius unnormalised (`1 + (4 + 1) - 4`); that is fine for `linarith`, no `norm_num` needed.
- The eigenvalue is real because `μ : ℝ` in the statement (and `A` is symmetric, so all its eigenvalues are
  real). Gershgorin itself works over any normed field.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| eigenvalue → some row's disc | `obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ` | R1 |
| ball → inequality | `rw [Metric.mem_closedBall, Real.dist_eq] at hk` | R2, R3 |
| one goal per row | `fin_cases k <;> …` | R4 |
| evaluate center and radius | `simp [A, Fin.sum_univ_succ] at hk` | R5–R8 |
| `‖r‖ → \|r\|` on `ℝ` | `Real.norm_eq_abs` (simp does it) | R6 |
| sum without one term | `Finset.sum_erase_eq_sub` (simp does it) | R7 |
| expand a sum over `Fin (n+1)` | `simp [Fin.sum_univ_succ]` | R8 |
| split `X ∧ Y` | `constructor` | TACTIC_STATES |
| `\|a\| ≤ b → -b ≤ a ∧ a ≤ b` | `abs_le.mp h` | R9 |
| linear inequality | `linarith [abs_le.mp h]` | R10 |
| see the state | infoview | |
