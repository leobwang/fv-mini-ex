# M180 · ⟪u, v⟫ₘ = 1 forces equal 4-velocities: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's Lorentz vectors
`Lorentz.Vector d`, the Minkowski product `⟪p, q⟫ₘ`, the time/space split `p⁰`, `p⃗`, the set
`Velocity d` of 4-velocities used as a type, Mathlib's `EuclideanSpace` with `inner` and `‖·‖`
(Cauchy–Schwarz), and the arithmetic closers `linarith`, `nlinarith`, `positivity`.

The physics: in `d` space dimensions, a 4-vector `p` has a time component `p⁰` and a spatial part
`p⃗ ∈ ℝᵈ`. The Minkowski product is `⟪p, q⟫ₘ = p⁰ q⁰ − p⃗ · q⃗` (signature `(+, −, …, −)`). A 4-velocity is
a `u` with `⟪u, u⟫ₘ = 1` and `u⁰ > 0`; `⟪u, v⟫ₘ` is the Lorentz factor `γ` of `v` seen from `u`, and `γ = 1`
means no relative motion.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal or hypothesis. `G : Prop` is a goal the entry does not touch.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddGroup α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- In a table, `\|` is a literal `|` (absolute value); Lean writes `|a|`.

## Reading the goals

| You see | It means |
|---|---|
| `Lorentz.Vector d` | a 4-vector: by definition a function `Fin 1 ⊕ Fin d → ℝ` (one time + `d` space components) |
| `Fin 1 ⊕ Fin d` | the index type: `Sum.inl 0` is the time index, `Sum.inr i` (`i : Fin d`) the `i`-th space index |
| `⟪p, q⟫ₘ` | Minkowski product `p⁰ q⁰ − p⃗ · q⃗`. Scoped notation: it needs `open Lorentz Vector` |
| `(minkowskiProduct p) q` | how the infoview prints `⟪p, q⟫ₘ`. `minkowskiProduct` is a bilinear map `Vector d →L[ℝ] Vector d →L[ℝ] ℝ` (`→L[ℝ]`: continuous ℝ-linear map), so `minkowskiProduct p` is a linear map, then applied to `q` |
| `p.timeComponent` | `p⁰`, defined as `p (Sum.inl 0)` (an `abbrev`, so `exact` sees through it) |
| `p.spatialPart` | `p⃗ : EuclideanSpace ℝ (Fin d)`, the vector `i ↦ p (Sum.inr i)` |
| `(fun i => w (Sum.inr i))` | `w⃗` after `simp` unfolded `w.spatialPart` (R12); `= 0` then means every space component is `0` |
| `EuclideanSpace ℝ (Fin d)` | `ℝᵈ` with the Euclidean norm; a wrapper `WithLp 2 (Fin d → ℝ)` around plain functions |
| `x.ofLp i`, `WithLp.ofLp x i` | coordinate `i` of `x : EuclideanSpace ℝ (Fin d)` (`ofLp` removes the wrapper) |
| `inner ℝ x y` | dot product `∑ᵢ xᵢ yᵢ` (Mathlib also writes `⟪x, y⟫_ℝ`) |
| `‖x‖` | Euclidean norm `√(inner ℝ x x)`; for a real number `a`, `‖a‖ = \|a\|` (R3) |
| `\|a\|` | absolute value of `a : ℝ` |
| `Velocity d` | the **set** `{v : Vector d \| ⟪v, v⟫ₘ = 1 ∧ 0 < v⁰}` |
| `u : ↑(Velocity d)` | `u` is an element of that set used as a type (a subtype): a pair of a vector and a proof it is in the set |
| `↑u` | `u.1`, the underlying `Lorentz.Vector d` of `u : Velocity d` (`u.2` is the membership proof) |
| `0 μ` | the zero 4-vector applied to the index `μ`; `simp` turns it into the real `0` |
| `¬a = 0` | `a ≠ 0` |
| `case refine_1` | the name of the first goal after `refine` |

---

## Part 1 · `eq_zero_of_orth` (milestone)

Statement: for `u w : Lorentz.Vector d`, if `0 < ⟪u, u⟫ₘ` (`u` timelike), `⟪w, w⟫ₘ = 0` (`w` null) and
`⟪u, w⟫ₘ = 0` (orthogonal), then `w = 0`. It is optional (you may change or delete it), but it is the
intended route to Part 2.

Math. In components: `hu : u⁰² − ‖u⃗‖² > 0`, `hw : w⁰² − ‖w⃗‖² = 0`, `huw : u⁰ w⁰ − u⃗ · w⃗ = 0`. Cauchy–Schwarz
gives `(u⁰ w⁰)² = (u⃗ · w⃗)² ≤ ‖u⃗‖² ‖w⃗‖² = ‖u⃗‖² w⁰²`. If `w⁰ ≠ 0`, then `w⁰² > 0` and `‖u⃗‖² w⁰² < u⁰² w⁰²`, a
contradiction. So `w⁰ = 0`, then `‖w⃗‖² = 0`, so `w⃗ = 0`, and `w = 0` component by component.

### Components (the stub already does these three steps)

**R1 · `rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at h`** changes the **context**. The lemma is
`⟪p, p⟫ₘ = ‖p⁰‖ ^ 2 - ‖p⃗‖ ^ 2`. Note `‖p⁰‖`: the norm of a real number (R3 removes it). Placeholders:
`{d : ℕ} (p : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `h : P ((minkowskiProduct p) p) ⊢ G` | `h : P (‖p.timeComponent‖ ^ 2 - ‖p.spatialPart‖ ^ 2) ⊢ G` |

**R2 · `rw [minkowskiProduct_eq_timeComponent_spatialPart] at h`** changes the **context**. The lemma is
`⟪p, q⟫ₘ = p⁰ * q⁰ - inner ℝ p⃗ q⃗`. Placeholders: `{d : ℕ} (p q : Lorentz.Vector d)`. Use R1 first on the
`⟪p, p⟫ₘ` hypotheses: R2 also matches them, and gives the less useful `inner ℝ p⃗ p⃗`.

| Before | After |
|---|---|
| `h : P ((minkowskiProduct p) q) ⊢ G` | `h : P (p.timeComponent * q.timeComponent - inner ℝ p.spatialPart q.spatialPart) ⊢ G` |

**R3 · `Real.norm_eq_abs`, then `sq_abs`** change the **context**. `Real.norm_eq_abs : ‖r‖ = |r|` for `r : ℝ`;
`sq_abs : |a| ^ 2 = a ^ 2`. The stub writes both as `simp only [Real.norm_eq_abs, sq_abs] at hu hw`.
Placeholders: `(a : ℝ)`.

| Before | After `rw [Real.norm_eq_abs] at h` | After `rw [sq_abs] at h` |
|---|---|---|
| `h : P (‖a‖ ^ 2) ⊢ G` | `h : P (\|a\| ^ 2)`, `⊢ G` | `h : P (a ^ 2) ⊢ G` |

### `w⁰ = 0` by contradiction

**R4 · `have hcs := abs_real_inner_le_norm x y`** changes the **context**: it adds Cauchy–Schwarz,
`|inner ℝ x y| ≤ ‖x‖ * ‖y‖`. Placeholders: `{d : ℕ} (x y : EuclideanSpace ℝ (Fin d))`; in the milestone
`x y` are `u.spatialPart`, `w.spatialPart`.

| Before | After |
|---|---|
| `⊢ G` | `hcs : \|inner ℝ x y\| ≤ ‖x‖ * ‖y‖`, `⊢ G` |

**R5 · `by_contra h0`** changes the **goal and the context**: to prove `G`, assume `¬G` and prove `False`.
Placeholders: `(a : ℝ)`. Use it inside `have hw0 : w.timeComponent = 0 := by …`.

| Before | After |
|---|---|
| `⊢ a = 0` | `h0 : ¬a = 0 ⊢ False` |

**R6 · `positivity`** **closes** a goal `0 < e` or `0 ≤ e` by the syntactic shape of `e` (squares, sums of
nonnegatives, products …). For a square `a ^ 2` it needs `a ≠ 0` (here `h0 : ¬a = 0`) in the context.
Placeholders: `(a : ℝ)`.

| Closes |
|---|
| `h0 : ¬a = 0 ⊢ 0 < a ^ 2` |

**R7 · `linarith`** **closes** a goal `t = s`, `t < s`, `t ≤ s` (or `False`) that follows from the hypotheses by
adding multiples of them. Every non-linear subterm (`a * b`, `inner ℝ x y`, `‖x‖ ^ 2`) is treated as an
unknown. Placeholders: `(a b c : ℝ)`.

| Closes |
|---|
| `h1 : a - b = c, h2 : c = 0 ⊢ a = b` |

**R8 · `rw [show a = b by tac]`** changes the **goal**: `show a = b by tac` is a proof term for `a = b`, built
on the spot. In the milestone, rewrite `u⁰ * w⁰` into `inner ℝ u⃗ w⃗` with `huw` and R7, so the squared
Cauchy–Schwarz (R9, R10) applies. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P a` | `⊢ P b` |

**R9 · `abs_le`** changes the **context** with `have h2 := abs_le.mp h`. The lemma is
`|a| ≤ b ↔ -b ≤ a ∧ a ≤ b`; `.mp` is its left-to-right direction, `.1`/`.2` of the result are the two
halves. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : \|a\| ≤ b`, `⊢ G` | `h2 : -b ≤ a ∧ a ≤ b ⊢ G` |

**R10 · `sq_le_sq'`** changes the **goal list** with `apply`. The lemma is `-b ≤ a → a ≤ b → a ^ 2 ≤ b ^ 2`;
`exact sq_le_sq' h₁ h₂` closes the goal in one go. Placeholders: `(a b : ℝ)`.

| Before | After `apply sq_le_sq'` |
|---|---|
| `⊢ a ^ 2 ≤ b ^ 2` | `⊢ -b ≤ a`, `⊢ a ≤ b` |

**R11 · `nlinarith`** **closes** what `linarith` closes after also adding the pairwise products of the
hypotheses (and of the negated goal). It needs the right facts in the context: here the squared
Cauchy–Schwarz `(u⁰ * w⁰) ^ 2 ≤ (‖u⃗‖ * ‖w⃗‖) ^ 2` and `0 < w⁰ ^ 2` (R6), next to `hu`, `hw`.
Placeholders: `(a b c : ℝ)`.

| Closes |
|---|
| `hc : 0 < c, hab : a < b ⊢ a * c < b * c` |

### `w⃗ = 0`, then `w = 0`

**R12 · `simp at h`** on a squared norm changes the **context**: `‖x‖ ^ 2 = 0` becomes `x = 0` (simp uses
`pow_eq_zero_iff` and `norm_eq_zero : ‖x‖ = 0 ↔ x = 0`). `simpa using h` does the same and closes the goal.
Get `‖w⃗‖ ^ 2 = 0` first: `rw [hw0] at hw`, then R7. Placeholders: `{d : ℕ} (x : EuclideanSpace ℝ (Fin d))`.

| Before | After |
|---|---|
| `h : ‖x‖ ^ 2 = 0 ⊢ x = 0` | `h : x = 0 ⊢ x = 0` |

In the milestone `x` is `w.spatialPart`, and there `simp` also unfolds `spatialPart` (second example of
R12): `h` becomes `(fun i => w (Sum.inr i)) = 0`, which does **not** match the goal `w.spatialPart = 0`
for `exact`. Run `simp` on the goal as well, or write `simpa using h`, which simplifies both the same way.
Placeholders: `{d : ℕ} (w : Lorentz.Vector d)`.

| Before | After `simp at h` | After `simp` |
|---|---|---|
| `h : ‖w.spatialPart‖ ^ 2 = 0 ⊢ w.spatialPart = 0` | `h : (fun i => w (Sum.inr i)) = 0 ⊢ w.spatialPart = 0` | `⊢ (fun i => w (Sum.inr i)) = 0` |

**R13 · `funext μ`** changes the **goal and the context**: a `Lorentz.Vector d` is a function, so two are
equal when all components are. Placeholders: `{d : ℕ} (w : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `⊢ w = 0` | `μ : Fin 1 ⊕ Fin d ⊢ w μ = 0 μ` |

**R14 · `match μ with | Sum.inl 0 => … | Sum.inr i => …`** changes the **goal list**: one goal per shape of
the index, time (`Fin 1` has only `0`) and space. In the tactic `match`, each `=>` is followed by the tactics
for that goal. The time goal is `w (Sum.inl 0) = 0 (Sum.inl 0)`, which `hw0 : w.timeComponent = 0` closes by
`exact` (`timeComponent` unfolds to `w (Sum.inl 0)`). Placeholders: `(P : Fin 1 ⊕ Fin d → Prop)`.

| Before | After |
|---|---|
| `μ : Fin 1 ⊕ Fin d ⊢ P μ` | `⊢ P (Sum.inl 0)`, `i : Fin d ⊢ P (Sum.inr i)` |

**R15 · `have h := congrArg (fun v => v i) hs`** changes the **context**: from `hs : x = y` it gets
`x i = y i`. `congrArg f : a = b → f a = f b`. Placeholders: `{d : ℕ} (w : Lorentz.Vector d) (i : Fin d)`,
`hs : w.spatialPart = 0`.

| Before | After |
|---|---|
| `⊢ G` | `h : w.spatialPart.ofLp i = WithLp.ofLp 0 i ⊢ G` |

**R16 · `simp at h`, `simp`** change the **context** and the **goal**: coordinates of `w⃗` become components
of `w`, and `0 (Sum.inr i)` becomes `0`. `simpa using congrArg (fun v => v i) hs` does R15 and R16 in one
line. Placeholders as in R15.

| Before | After `simp at h` | After `simp` |
|---|---|---|
| `h : w.spatialPart.ofLp i = WithLp.ofLp 0 i ⊢ w (Sum.inr i) = 0 (Sum.inr i)` | `h : w (Sum.inr i) = 0 ⊢ w (Sum.inr i) = 0 (Sum.inr i)` | `⊢ w (Sum.inr i) = 0` |

### Worked combinations (W2, W3, on objects that are not the exercise's)

**W2: squared Cauchy–Schwarz in ℝ³.** R4, then R9, then `sq_le_sq'` used as a term (R10), then
`rw [mul_pow] at h3` (`mul_pow : (a * b) ^ n = a ^ n * b ^ n`):

```lean-goal
⊢ inner ℝ x y ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2
```

with `h3 : inner ℝ x y ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2` before the `rw` and `h3 : inner ℝ x y ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2`
after it.

**W3: two 4-vectors with the same parts are equal.** `funext μ` (R13), then the tactic `match` (R14) with
`exact ht` for time and `simpa using congrArg (fun x => x i) hs` (R15, R16) for space:

| Before | After `funext μ` |
|---|---|
| `⊢ w = v` | `μ : Fin 1 ⊕ Fin d ⊢ w μ = v μ` |

---

## Part 2 · `eq_of_minkowskiProduct_eq_one`

Statement: for `u v : Velocity d` with `⟪u.1, v.1⟫ₘ = 1`, `u = v`.

Math. Put `w = u − v`. Bilinearity and `⟪u, u⟫ₘ = ⟪v, v⟫ₘ = ⟪u, v⟫ₘ = 1` give
`⟪w, w⟫ₘ = 1 − 1 − (1 − 1) = 0` and `⟪u, w⟫ₘ = 1 − 1 = 0`, and `⟪u, u⟫ₘ = 1 > 0`. The milestone gives
`w = 0`, so `u.1 = v.1`, so `u = v`.

**R17 · `have hq := L a (by tac)`** changes the **context**: it applies a lemma `L` (here the milestone) to
explicit arguments, and each `(by tac)` proves one of its hypotheses on the spot. The new fact is `L`'s
conclusion. Placeholders: `(Q : ℝ → Prop) (L : ∀ x : ℝ, 0 < x → Q x)`.

| Before | After |
|---|---|
| `⊢ Q 1` | `hq : Q 1 ⊢ Q 1` |

**R18 · `Velocity.minkowskiProduct_self_eq_one`** changes the **goal**: `⟪u.1, u.1⟫ₘ = 1` for `u : Velocity d`.
It is a `simp` lemma, so plain `simp` uses it (and then closes `0 < 1`). Placeholders: `{d : ℕ} (u : Velocity d)`.

| Before | After `simp only [Velocity.minkowskiProduct_self_eq_one]` |
|---|---|
| `⊢ P ((minkowskiProduct ↑u) ↑u)` | `⊢ P 1` |

**R19 · `map_sub`, `sub_apply`** change the **goal**: bilinearity. `map_sub : f (a - b) = f a - f b` for any
linear map `f`. In the left slot `f = minkowskiProduct` gives a difference of linear maps, and
`sub_apply : (f - g) r = f r - g r` applies it to `r`. In the right slot `f = minkowskiProduct r`, so
`map_sub` alone does it. `simp [map_sub]` does all of this (and `map_add` for `+`). Placeholders:
`{d : ℕ} (p q r : Lorentz.Vector d)`.

| Before | After `rw [map_sub]` | After `rw [sub_apply]` |
|---|---|---|
| `⊢ P ((minkowskiProduct (p - q)) r)` | `⊢ P ((minkowskiProduct p - minkowskiProduct q) r)` | `⊢ P ((minkowskiProduct p) r - (minkowskiProduct q) r)` |
| `⊢ P ((minkowskiProduct r) (p - q))` | `⊢ P ((minkowskiProduct r) p - (minkowskiProduct r) q)` | |

**R20 · `minkowskiProduct_symm`** changes the **goal**. The lemma is `⟪p, q⟫ₘ = ⟪q, p⟫ₘ`. Give it the
arguments, `minkowskiProduct_symm q p`, when you pass it to `simp`: then it rewrites only `⟪q, p⟫ₘ`
(unrestricted, it would rewrite back and forth). Placeholders: `{d : ℕ} (p q : Lorentz.Vector d)`.

| Before | After `rw [minkowskiProduct_symm]` |
|---|---|
| `⊢ P ((minkowskiProduct p) q)` | `⊢ P ((minkowskiProduct q) p)` |

**R21 · `ext1`** changes the **goal**: it applies the one extensionality lemma `Velocity.ext : u.1 = v.1 → u = v`
(two velocities are equal when their vectors are). `ext` (without `1`) may keep going into components.
Placeholders: `{d : ℕ} (u v : Velocity d)`.

| Before | After |
|---|---|
| `⊢ u = v` | `⊢ ↑u = ↑v` |

**R22 · `sub_eq_zero`** changes the **goal** with `rw [← sub_eq_zero]`. The lemma is `a - b = 0 ↔ a = b`;
`sub_eq_zero.mp h` turns `h : a - b = 0` into `a = b` directly. Placeholders:
`{α : Type} [AddGroup α] (a b : α)` (α has `+`, `-`, `0`; `ℝ` and `Lorentz.Vector d` qualify).

| Before | After |
|---|---|
| `⊢ a = b` | `⊢ a - b = 0` |

### Worked combination W1: `⟪u + v, u + v⟫ₘ = 2 + 2⟪u, v⟫ₘ`

`simp only [map_add, add_apply]` (R19 for `+`), `rw [minkowskiProduct_symm v.1 u.1]` (R20), `simp` (R18), `ring`:

```lean-goal
⊢ (minkowskiProduct (↑u + ↑v)) (↑u + ↑v) = 2 + 2 * (minkowskiProduct ↑u) ↑v
⊢ (minkowskiProduct ↑u) ↑u + (minkowskiProduct ↑v) ↑u + ((minkowskiProduct ↑u) ↑v + (minkowskiProduct ↑v) ↑v) = 2 + 2 * (minkowskiProduct ↑u) ↑v
⊢ (minkowskiProduct ↑u) ↑u + (minkowskiProduct ↑u) ↑v + ((minkowskiProduct ↑u) ↑v + (minkowskiProduct ↑v) ↑v) = 2 + 2 * (minkowskiProduct ↑u) ↑v
⊢ 1 + (minkowskiProduct ↑u) ↑v + ((minkowskiProduct ↑u) ↑v + 1) = 2 + 2 * (minkowskiProduct ↑u) ↑v
```

The side goals of Part 2 have the same shape with `-`, and `h` closes the remaining `⟪u.1, v.1⟫ₘ`.

---

## Traps

- `⟪p, q⟫ₘ` is scoped notation: it parses only after `open Lorentz Vector`, and the infoview never prints
  it back; it shows `(minkowskiProduct p) q`.
- `simp` does not know `⟪v, u⟫ₘ = ⟪u, v⟫ₘ`. After `simp [map_sub]` the expansion of `⟪u - v, u - v⟫ₘ` contains
  both; add `minkowskiProduct_symm v.1 u.1` (with arguments, R20) so `h` applies to both.
- `linarith`/`nlinarith` treat `inner ℝ u⃗ w⃗` and `u⁰ * w⁰` as unrelated unknowns unless a hypothesis links
  them (`huw`); `nlinarith` also knows nothing about Cauchy–Schwarz: put the squared form in the context first.
- `nlinarith` multiplies pairs of hypotheses only. Give it `0 < w⁰ ^ 2` (R6) explicitly; `¬w⁰ = 0` alone is
  not something it can multiply.
- Writing a component goal by hand needs the type: `(0 : Lorentz.Vector d) μ`; a bare `0 μ` does not
  elaborate.
- `have h : T` with no `:= …` makes `T` your next goal instead of adding `h` (TACTIC_STATES, "Adding facts").
- `t1 ; t2` runs `t2` on the first goal only (TACTIC_STATES). After `apply sq_le_sq'`, close both goals.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `⟪p, p⟫ₘ` → `‖p⁰‖² − ‖p⃗‖²` in `h` | `rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at h` | R1 |
| `⟪p, q⟫ₘ` → `p⁰q⁰ − inner ℝ p⃗ q⃗` in `h` | `rw [minkowskiProduct_eq_timeComponent_spatialPart] at h` | R2 |
| `‖a‖ ^ 2 → a ^ 2` for real `a` | `simp only [Real.norm_eq_abs, sq_abs] at h` | R3 |
| Cauchy–Schwarz | `have hcs := abs_real_inner_le_norm x y` | R4 |
| prove `a = 0` by contradiction | `by_contra h0` | R5 |
| `0 < a ^ 2` from `a ≠ 0` | `positivity` | R6 |
| linear arithmetic | `linarith` | R7 |
| rewrite with a fact proved inline | `rw [show a = b by linarith]` | R8 |
| `\|a\| ≤ b` → two inequalities | `abs_le.mp h` (then `.1`, `.2`) | R9 |
| square both sides | `sq_le_sq' h₁ h₂` | R10 |
| products of hypotheses | `nlinarith` | R11 |
| `‖x‖ ^ 2 = 0` → `x = 0` | `simpa using h` | R12 |
| 4-vector equation → components | `funext μ` | R13 |
| split time / space index | `match μ with \| Sum.inl 0 => … \| Sum.inr i => …` | R14 |
| `i`-th coordinate of `x = y` | `congrArg (fun v => v i) hs` | R15 |
| coordinates of `w⃗` → components of `w` | `simpa using …` | R16 |
| use the milestone | `have hw := eq_zero_of_orth _ _ (by …) (by …) (by …)` | R17 |
| `⟪u.1, u.1⟫ₘ = 1` | `simp` (`Velocity.minkowskiProduct_self_eq_one`) | R18 |
| expand `⟪p - q, r⟫ₘ`, `⟪r, p - q⟫ₘ` | `simp [map_sub]` | R19 |
| `⟪v, u⟫ₘ = ⟪u, v⟫ₘ` | `minkowskiProduct_symm v.1 u.1` | R20 |
| velocities equal ← vectors equal | `ext1` | R21 |
| `a - b = 0` → `a = b` | `sub_eq_zero.mp h` | R22 |
| see the state | infoview | |
