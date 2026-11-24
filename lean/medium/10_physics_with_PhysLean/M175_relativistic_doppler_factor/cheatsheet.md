# M175 · Relativistic Doppler factor: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's Lorentz vectors
`Lorentz.Vector d`, the boost `LorentzGroup.boost` acting by `•`, the Lorentz factor `γ`, its lemmas
`γ_sq` and `γ_det_not_zero`; Mathlib's `calc` chains and the denominator-clearing tactic `field_simp`.

The physics (units with `c = 1`). A 4-vector `p` has time coordinate `t = p⁰` and space coordinates
`xⱼ` (`j = 0, …, d-1`). The boost with speed `β` (`|β| < 1`) along axis `i` sends
`t ↦ γ (t − β xᵢ)` and `xᵢ ↦ γ (xᵢ − β t)`, where `γ = γ β = 1 / √(1 − β²)` is the Lorentz factor; the
other axes are untouched. The *light-cone coordinates* are `t + xᵢ` and `t − xᵢ`.

Math. Adding the two boosted coordinates:
`γ (t − β xᵢ) + γ (xᵢ − β t) = γ (1 − β) (t + xᵢ)`, so `t + xᵢ` is just multiplied by the Doppler factor
`D₋ = γ (1 − β)` (and `t − xᵢ` by `D₊ = γ (1 + β)`, W1). Their product is
`D₋ D₊ = γ² (1 − β²) = (1 / (1 − β²)) (1 − β²) = 1`, which needs `1 − β² ≠ 0`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is a goal the entry does not touch.
- Placeholders are written as Lean binders. `{d : ℕ}` is implicit (Lean infers it from the other
  arguments). No type-class brackets occur here: everything is over `ℝ`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Lorentz.Vector d` | a 4-vector in `d` space dimensions: by definition a function `Fin 1 ⊕ Fin d → ℝ` |
| `Fin 1 ⊕ Fin d` | the index type (disjoint union `⊕`): `Sum.inl 0` is the time index, `Sum.inr i` (`i : Fin d`) the `i`-th space index |
| `p (Sum.inl 0)`, `p (Sum.inr i)` | the coordinates `t = p⁰` and `xᵢ` (a vector is applied to an index like a function) |
| `boost i β hβ` | the boost with speed `β` along space axis `i`; `hβ : \|β\| < 1` is a required argument |
| `↑(𝓛 d)` | how `#check` prints the type of `boost i β hβ`: an element of `LorentzGroup d` (`𝓛 d` is physlib notation for it) |
| `Λ • p` | the Lorentz transformation `Λ` applied to the vector `p` (`•` is a group action) |
| `(boost i β hβ • p) (Sum.inl 0)` | the time coordinate of the boosted vector (R2) |
| `γ β` | `LorentzGroup.γ β`, defined as `1 / √(1 - β ^ 2)`; it is an ordinary real number, an atom for `ring` |
| `\|β\|` | absolute value of `β` |
| `x ≠ 0` | `¬(x = 0)`; the side condition `field_simp` needs to cancel `x` (R8) |
| `case left`, `case right` | the names of the two goals after `constructor` (R1) |
| `case calc_1`, `case calc_2` | the names of the goals a `calc` with `?_` steps leaves (R6); inside the second conjunct they print as `case right.calc_1`, `case right.calc_2` |

---

## Part 1 · `doppler`, first conjunct

Statement: the boosted `t + xᵢ` equals `γ β * (1 - β) * (t + xᵢ)`. Split the `∧` first (R1); this part is
two rewrites and `ring`.

**R1 · `constructor`** changes the **goal list**: `A ∧ B` becomes the two goals `A` and `B`. Placeholders:
`(A B : Prop)`. Prove them in order, each under its own `·`.

| Before | After |
|---|---|
| `⊢ A ∧ B` | `⊢ A`, `⊢ B` |

**R2 · `rw [Lorentz.Vector.boost_time_eq]`** changes the **goal**: the time coordinate of the boosted vector
becomes its formula. The lemma is
`boost_time_eq : (boost i β hβ • p) (Sum.inl 0) = γ β * (p (Sum.inl 0) - β * p (Sum.inr i))`
(`t' = γ (t − β xᵢ)`). With `open Lorentz Vector` the short name `boost_time_eq` works. Placeholders:
`{d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1) (p : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `⊢ P ((boost i β hβ • p) (Sum.inl 0))` | `⊢ P (γ β * (p (Sum.inl 0) - β * p (Sum.inr i)))` |

**R3 · `rw [Lorentz.Vector.boost_inr_self_eq]`** changes the **goal**: the space coordinate *along the boost
axis* `i` becomes its formula. The lemma is
`boost_inr_self_eq : (boost i β hβ • p) (Sum.inr i) = γ β * (p (Sum.inr i) - β * p (Sum.inl 0))`
(`xᵢ' = γ (xᵢ − β t)`). "self" means the index is the boost axis itself; another axis `j ≠ i` is unchanged
(a different lemma). Placeholders: as in R2.

| Before | After |
|---|---|
| `⊢ P ((boost i β hβ • p) (Sum.inr i))` | `⊢ P (γ β * (p (Sum.inr i) - β * p (Sum.inl 0)))` |

**R4 · `ring`** **closes** an identity that holds in every commutative ring. It treats `γ β`, `p (Sum.inl 0)`
and `p (Sum.inr i)` as unknowns, so it needs no fact about `γ`. Placeholders: `(β a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ γ β * a + γ β * b - (a + b) * γ β = 0` | no goals |

**W1: the other light-cone coordinate** (R2, R3, R4). For `t − xᵢ` the same two rewrites give

```lean-goal
⊢ (boost i β hβ • p) (Sum.inl 0) - (boost i β hβ • p) (Sum.inr i) = γ β * (1 + β) * (p (Sum.inl 0) - p (Sum.inr i))
⊢ γ β * (p (Sum.inl 0) - β * p (Sum.inr i)) - (boost i β hβ • p) (Sum.inr i) = γ β * (1 + β) * (p (Sum.inl 0) - p (Sum.inr i))
⊢ γ β * (p (Sum.inl 0) - β * p (Sum.inr i)) - γ β * (p (Sum.inr i) - β * p (Sum.inl 0)) = γ β * (1 + β) * (p (Sum.inl 0) - p (Sum.inr i))
```

and `ring` closes the last line.

---

## Part 2 · `doppler`, second conjunct

Statement: `γ β * (1 - β) * (γ β * (1 + β)) = 1`. `ring` alone fails: it does not know what `γ β` is. Get
the fact `1 - β ^ 2 ≠ 0` (R5), regroup the product into `γ β ^ 2 * (1 - β ^ 2)` with a `calc` step proved by
`ring` (R6, R4), substitute `γ β ^ 2` (R7), and clear the denominator (R8).

**R5 · `have hd := LorentzGroup.γ_det_not_zero β hβ`** changes the **context**: it adds
`hd : 1 - β ^ 2 ≠ 0`. The lemma is `γ_det_not_zero : ∀ β, |β| < 1 → 1 - β ^ 2 ≠ 0` (`β` explicit).
Placeholders: `(β : ℝ) (hβ : |β| < 1)`.

| Before | After |
|---|---|
| `⊢ G` | `hd : 1 - β ^ 2 ≠ 0 ⊢ G` |

**R6 · `calc`** changes the **goal list**: a goal `a = c` is proved as a chain `a = b`, `b = c`, one proof per
step. Write it as
```
calc a = b := by tac₁
  _ = c := by tac₂
```
(`_` stands for the previous right side; the continuation line is indented). With `?_` in place of the
proofs the steps become goals. Placeholders: `(a b c : ℝ)`; you choose the middle term `b`.

| Before | After |
|---|---|
| `⊢ a = c` | `⊢ a = b`, `⊢ b = c` |

**R7 · `rw [LorentzGroup.γ_sq β hβ]`** changes the **goal**: `γ β ^ 2` becomes `1 / (1 - β ^ 2)`. The lemma is
`γ_sq : ∀ β, |β| < 1 → γ β ^ 2 = 1 / (1 - β ^ 2)`. `rw` needs `γ β ^ 2` literally in the goal (Traps).
Placeholders: `(β : ℝ) (hβ : |β| < 1)`.

| Before | After |
|---|---|
| `⊢ P (γ β ^ 2)` | `⊢ P (1 / (1 - β ^ 2))` |

**R8 · `field_simp`** changes the **goal**: it multiplies out denominators that a hypothesis in the context
(`hx : x ≠ 0`) proves nonzero, then simplifies. It **closes** `a / x * x = a`; on `a / x = b` it leaves
`a = x * b`. Placeholders: `(a b x : ℝ) (hx : x ≠ 0)`.

| Before | After |
|---|---|
| `hx : x ≠ 0 ⊢ a / x * x = a` | no goals |
| `hx : x ≠ 0 ⊢ a / x = b` | `hx : x ≠ 0 ⊢ a = x * b` |
| `⊢ a / x * x = a` (no `hx`) | `⊢ a * x / x = a` (stuck: it cannot cancel `x`) |

**W2: regroup, substitute, clear** (R6, R4, R7-style `rw`, R8), on a Euclidean identity for a plain real
`c` with `hc : c ^ 2 = 1 / (1 + u ^ 2)` and `hu : 1 + u ^ 2 ≠ 0` (with `c = cos θ`, `u = tan θ` it is
`sin² θ + cos² θ = 1`). The `calc` with `?_` steps leaves two goals; `ring` closes the first, and in the
second `rw [hc]` gives a state that `field_simp` (using `hu`) closes:

```lean-goal
⊢ (c * u) ^ 2 + c ^ 2 = 1
⊢ (c * u) ^ 2 + c ^ 2 = c ^ 2 * (1 + u ^ 2)
⊢ c ^ 2 * (1 + u ^ 2) = 1
⊢ 1 / (1 + u ^ 2) * (1 + u ^ 2) = 1
```

---

## Traps

- `rw [γ_sq β hβ]` fails on the original product `γ β * (1 - β) * (γ β * (1 + β))`: there is no `γ β ^ 2`
  in it. Regroup first (R6 with R4), or `ring_nf` and check what it produced.
- `field_simp` cancels a denominator `x` only when it can prove `x ≠ 0`; otherwise it gets stuck at
  `a * x / x = a` (R8, last row). Put `hd : 1 - β ^ 2 ≠ 0` in the context (R5) so the cancellation is
  guaranteed. (Here `field_simp` also happens to succeed from `hβ : |β| < 1` alone; with neither `hd` nor
  `hβ` it stops at `(1 - β ^ 2) / (1 - β ^ 2) = 1`.)
- `boost_inr_self_eq` is for the index `Sum.inr i` with the **same** `i` as the boost axis.
- The `have` for `hd` belongs inside the second branch (or before `constructor`); a `have` in the first
  `·` block is not visible in the second.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `A ∧ B` | `constructor` | R1 |
| boosted time coordinate | `rw [boost_time_eq]` | R2 |
| boosted coordinate on the boost axis | `rw [boost_inr_self_eq]` | R3 |
| finish algebra with `γ β` as an unknown | `ring` | R4 |
| `1 - β ^ 2 ≠ 0` | `have hd := γ_det_not_zero β hβ` | R5 |
| regroup an expression first | `calc a = b := by ring` / `_ = c := by …` | R6 |
| `γ β ^ 2 → 1 / (1 - β ^ 2)` | `rw [γ_sq β hβ]` | R7 |
| `1 / x * x = 1` with `hx : x ≠ 0` | `field_simp` | R8 |
| see the state | infoview | |
