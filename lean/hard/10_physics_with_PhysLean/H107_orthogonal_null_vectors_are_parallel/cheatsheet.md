# H107 · Orthogonal null vectors are parallel: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `apply`, `rw`, `simp`, `have`,
`refine`, `funext` (E022), anonymous constructors `⟨_, _⟩`. **New here:** Mathlib's norms `‖·‖`, the real
inner product `inner ℝ`, `EuclideanSpace` and its `ofLp`, scalar multiplication `•`, the tactics
`funext` on 4-vectors, tactic `match`, `change`, `linarith`, `nlinarith`, `field_simp` (and `norm_num`
in W1–W2, see TACTIC_STATES.md); physlib's Lorentz vectors
`Lorentz.Vector d`, their `timeComponent` and `spatialPart`, and the Minkowski product `⟪·, ·⟫ₘ`.

**The math, in symbols.** A 4-vector (for general `d`: a $(1+d)$-vector) is
$p = (p^0, \vec p) \in \mathbb R^{1+d}$: time component $p^0 \in \mathbb R$, spatial part
$\vec p \in \mathbb R^d$. The Minkowski product (signature $+-\cdots-$) is
$\langle p, q\rangle_m = p^0 q^0 - \vec p\cdot\vec q$, where $\vec p\cdot\vec q$ is the Euclidean dot
product. $p$ is *null* (lightlike) when $\langle p, p\rangle_m = 0$, i.e. $(p^0)^2 = \|\vec p\|^2$.
Write $a = p^0$, $b = q^0$. The three hypotheses say
$$a^2 = \|\vec p\|^2,\qquad b^2 = \|\vec q\|^2,\qquad ab = \vec p\cdot\vec q .$$
Then the spatial vector $w = b\,\vec p - a\,\vec q$ has
$$\|w\|^2 = b^2\|\vec p\|^2 - 2ab\,(\vec p\cdot\vec q) + a^2\|\vec q\|^2 = a^2b^2 - 2a^2b^2 + a^2b^2 = 0,$$
so $b\,\vec p = a\,\vec q$. Also $b \ne 0$: if $b = 0$ then $\|\vec q\|^2 = b^2 = 0$, so $\vec q = 0$ and
$q = 0$. Hence $r = a / b$ works: $p^0 = (a/b)\,b$ and $\vec p = b^{-1}(b\,\vec p) = b^{-1}(a\,\vec q) = (a/b)\,\vec q$.
Geometrically: the light cone contains no two independent orthogonal directions (two orthogonal light
rays point the same way). The three milestones are exactly these steps: $b \ne 0$ (Part 1),
$\|w\|^2 = 0$ (Part 2), "a vector is its time component plus its spatial part" (Part 3); Part 4
assembles them.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`, or `P : EuclideanSpace ℝ (Fin d) → Prop`). The step
  changes only the part inside `P (…)`, wherever it sits in a larger goal. `G : Prop` is an arbitrary
  goal; a hypothesis `g : … → G` is only there to close the example after a hypothesis changed.
- Placeholders are written as Lean binders. `{d : ℕ}` is the number of space dimensions (`d = 3` for
  physical spacetime). `{α : Type}` is any type. `x y : EuclideanSpace ℝ (Fin d)` are vectors of
  $\mathbb R^d$ with the Euclidean norm and dot product.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Lorentz.Vector d` | functions `Fin 1 ⊕ Fin d → ℝ`, i.e. vectors of $\mathbb R^{1+d}$ |
| `Fin 1 ⊕ Fin d`, `Sum.inl 0`, `Sum.inr i` | the index type (a disjoint union `⊕`): the time index `Sum.inl 0`, and the space index `Sum.inr i` for `i : Fin d` |
| `p.timeComponent`, `p (Sum.inl 0)` | the time component $p^0$; the same term by definition (R7) |
| `p.spatialPart` | the spatial part $\vec p$, a vector of `EuclideanSpace ℝ (Fin d)`; by definition `WithLp.toLp 2 (fun i => p (Sum.inr i))` |
| `EuclideanSpace ℝ (Fin d)` | $\mathbb R^d$ with the Euclidean norm; a wrapper (`WithLp 2`) around `Fin d → ℝ` |
| `x.ofLp i` | the `i`-th coordinate of `x : EuclideanSpace ℝ (Fin d)`; you type `x i` (R8) |
| `p.spatialPart.ofLp i` | $\vec p_i$, which is `p (Sum.inr i)` by definition (R8) |
| `0 μ`, `0 (Sum.inl 0)` | component `μ` of the zero vector `0 : Lorentz.Vector d`; it is `0 : ℝ` by definition, so `exact h0` accepts it (R7) |
| `(fun i => p (Sum.inr i)) = 0` | "the spatial part of `p` is zero", as plain functions `Fin d → ℝ` (what `simp` leaves, R3) |
| `(minkowskiProduct p) q` | $\langle p, q\rangle_m$. You type `⟪p, q⟫ₘ` (scoped notation, needs `open Lorentz Vector`); the infoview prints the long form |
| `‖x‖` | the norm; for a real `x` it is the absolute value (R10) |
| `\|x\|` | the absolute value `abs x` of a real `x` |
| `inner ℝ x y` | the Euclidean dot product $\vec x\cdot\vec y$ |
| `r • x` | scalar `r : ℝ` times vector `x`; `a • b • x` is `a • (b • x)` |
| `b⁻¹` | the inverse $1/b$; in `ℝ`, `0⁻¹ = 0`, so its lemmas need `b ≠ 0` |
| `a ≠ b` | `a = b → False` (R1, R4) |
| `case refine_1`, `case refine_2` | the goals left by `refine` with two `?_`, in order |

---

## Part 1 · `time_ne_zero_of_null` (milestone 1)

Statement: from `hq : ⟪q, q⟫ₘ = 0` and `hq0 : q ≠ 0`, prove `q.timeComponent ≠ 0`. Proof idea: assume
$q^0 = 0$; then $\|\vec q\|^2 = 0$, so every component of $q$ is $0$, contradicting `hq0`.

**R1 · `intro h0`** on a goal `a ≠ b` changes the **goal and the context**. `a ≠ b` is notation for
`a = b → False`, so `intro` assumes `a = b` and leaves `False`. Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ a ≠ b` | `h0 : a = b ⊢ False` |

**R2 · `rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at h`** changes the **context**. The
lemma is `⟪p, p⟫ₘ = ‖p.timeComponent‖ ^ 2 - ‖p.spatialPart‖ ^ 2`, i.e.
$\langle p,p\rangle_m = (p^0)^2 - \|\vec p\|^2$ with a norm around the real $p^0$ (removed by R10).
`at h` rewrites `h` instead of the goal; `at hp hq` rewrites both. Placeholders: `{d : ℕ} (p : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `h : (minkowskiProduct p) p = 0 ⊢ G` | `h : ‖p.timeComponent‖ ^ 2 - ‖p.spatialPart‖ ^ 2 = 0 ⊢ G` |

After R2, `rw [h0] at hq` (with `h0 : q.timeComponent = 0`) replaces `q.timeComponent` by `0`.

**R3 · `simp at h`** changes the **context**: from `‖0‖ ^ 2 - ‖p⃗‖ ^ 2 = 0` it derives that the spatial
part is zero. `simp` chains `norm_zero` (`‖0‖ = 0`), `zero_pow` (`0 ^ 2 = 0`), `zero_sub`, `neg_eq_zero`,
`pow_eq_zero_iff` (`a ^ 2 = 0 ↔ a = 0`), `norm_eq_zero` (R19) and `WithLp.toLp_eq_zero` (`toLp 2 f = 0 ↔ f = 0`).
`p.spatialPart` is by definition `WithLp.toLp 2 (fun i => p (Sum.inr i))`, so the result is a statement about
the plain function `fun i => p (Sum.inr i)`. Run `simp? at h` to see the list yourself.
Placeholders: `{d : ℕ} (p : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `h : ‖0‖ ^ 2 - ‖p.spatialPart‖ ^ 2 = 0 ⊢ G` | `h : (fun i => p (Sum.inr i)) = 0 ⊢ G` |

**R4 · `apply hne`** with `hne : a ≠ b` changes the **goal**: `hne` has type `a = b → False`, so on the
goal `False` it leaves its premise `a = b`. In Part 1: `apply hq0` turns `False` into `q = 0`.
Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `hne : a ≠ b ⊢ False` | `hne : a ≠ b ⊢ a = b` |

**R5 · `funext μ`** changes the **goal and the context**. `Lorentz.Vector d` is a function type, so two
vectors are equal when they agree at every index `μ`. Placeholders: `{d : ℕ} (p q : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `⊢ p = q` | `μ : Fin 1 ⊕ Fin d ⊢ p μ = q μ` |

**R6 · `match μ with | Sum.inl 0 => tac₁ | Sum.inr i => tac₂`** changes the **goal list**: one goal for the
time index and one for the space indices (the arm `Sum.inr i` also adds `i : Fin d`). `Fin 1` has the
single element `0`, so the two patterns cover everything. Each arm is a tactic block that must close its
goal. Placeholders: `{d : ℕ} (P : Fin 1 ⊕ Fin d → Prop) (μ : Fin 1 ⊕ Fin d)`. The guide also writes the
same split as `refine match μ with | Sum.inl 0 => ?_ | Sum.inr i => ?_` so both goals show up at once:

| Before | After |
|---|---|
| `μ : Fin 1 ⊕ Fin d ⊢ P μ` | `⊢ P (Sum.inl 0)`, `i : Fin d ⊢ P (Sum.inr i)` |

**R7 · `exact h0` across a definition** **closes** the goal. `timeComponent` is defined as
`p.timeComponent = p (Sum.inl 0)` (a reducible definition), so `exact` accepts a proof about
`p.timeComponent` for a goal about `p (Sum.inl 0)`. The same holds for `0 (Sum.inl 0)`, which is `0`.
Placeholders: `{d : ℕ} (p : Lorentz.Vector d) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `h0 : P p.timeComponent ⊢ P (p (Sum.inl 0))` | closed by `exact h0` |

**R8 · `congrArg (· i) hs`** changes the **context** (via `have h' := …`, or directly in `exact`).
`congrArg f : a = b → f a = f b`, and `(· i)` is the function `fun x => x i`, so from an equation of
vectors you get the equation of their `i`-th coordinates. A coordinate of `x : EuclideanSpace ℝ (Fin d)`
prints as `x.ofLp i`. Placeholders: `{d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) (i : Fin d)`.

| Before | After `have h' := congrArg (· i) hs` |
|---|---|
| `hs : x = y ⊢ G` | `h' : x.ofLp i = y.ofLp i ⊢ G` |

`p.spatialPart.ofLp i` is `p (Sum.inr i)` by definition, so `exact` closes the space-index goal with it:

| Before | After |
|---|---|
| `h : P (p.spatialPart.ofLp i) ⊢ P (p (Sum.inr i))` | closed by `exact h` |

In Part 1 the hypothesis is `hq : (fun i => q (Sum.inr i)) = 0` (R3); `congrArg (· i) hq` is then
`(fun i => q (Sum.inr i)) i = 0 i`, which is the goal `q (Sum.inr i) = 0 (Sum.inr i)` by definition.

---

## Part 2 · `key` (milestone 2)

Statement: from the three hypotheses, `‖q.timeComponent • p.spatialPart - p.timeComponent • q.spatialPart‖ ^ 2 = 0`,
i.e. $\|b\,\vec p - a\,\vec q\|^2 = 0$. First put the hypotheses in components (R2, R9, R10), then expand
the goal (R11–R15), substitute $\vec p\cdot\vec q = ab$ (R16), and finish with R17.

**R9 · `rw [minkowskiProduct_eq_timeComponent_spatialPart] at h`** changes the **context**. The lemma is
`⟪p, q⟫ₘ = p.timeComponent * q.timeComponent - inner ℝ p.spatialPart q.spatialPart`. Placeholders:
`{d : ℕ} (p q : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `h : (minkowskiProduct p) q = 0 ⊢ G` | `h : p.timeComponent * q.timeComponent - inner ℝ p.spatialPart q.spatialPart = 0 ⊢ G` |

**R10 · `Real.norm_eq_abs`, then `sq_abs`** change the **goal** (or, with `at h`, the context):
`‖x‖ = |x|` for a real `x`, and `|a| ^ 2 = a ^ 2`. Together they remove the norm around a real number,
e.g. `‖p.timeComponent‖ ^ 2` becomes `p.timeComponent ^ 2`. Use them as
`simp only [Real.norm_eq_abs, sq_abs] at hp hq`. Placeholders: `(x : ℝ)`.

```lean-goal
⊢ P (‖x‖ ^ 2)
⊢ P (|x| ^ 2)
⊢ P (x ^ 2)
```

**R11 · `rw [norm_sub_sq_real]`** changes the **goal**. The lemma is
`‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2` in any real inner product space. Placeholders:
`{d : ℕ} (x y : EuclideanSpace ℝ (Fin d))`.

| Before | After |
|---|---|
| `⊢ P (‖x - y‖ ^ 2)` | `⊢ P (‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2)` |

**R12 · `rw [norm_smul]`** changes the **goal**: `‖r • x‖ = ‖r‖ * ‖x‖` (here `‖r‖ = |r|` for `r : ℝ`).
One `rw` rewrites one pattern; with two different scaled vectors, write it twice.
Placeholders: `{d : ℕ} (r : ℝ) (x : EuclideanSpace ℝ (Fin d))`.

| Before | After |
|---|---|
| `⊢ P ‖r • x‖` | `⊢ P (‖r‖ * ‖x‖)` |

**R13 · `rw [real_inner_smul_left]`** changes the **goal**: `inner ℝ (r • x) y = r * inner ℝ x y`.
Placeholders: `{d : ℕ} (r : ℝ) (x y : EuclideanSpace ℝ (Fin d))`.

| Before | After |
|---|---|
| `⊢ P (inner ℝ (r • x) y)` | `⊢ P (r * inner ℝ x y)` |

**R14 · `rw [real_inner_smul_right]`** changes the **goal**: `inner ℝ x (r • y) = r * inner ℝ x y`.
Placeholders: as R13.

| Before | After |
|---|---|
| `⊢ P (inner ℝ x (r • y))` | `⊢ P (r * inner ℝ x y)` |

**R15 · `mul_pow`** changes the **goal**: `(a * b) ^ n = a ^ n * b ^ n`. After R12 the goal has
`(‖r‖ * ‖x‖) ^ 2`; `simp only [Real.norm_eq_abs, mul_pow, sq_abs]` (R10, R15) turns it into
`r ^ 2 * ‖x‖ ^ 2`. Placeholders: `(a b : ℝ) (n : ℕ)` (any commutative monoid).

| Before | After |
|---|---|
| `⊢ P ((a * b) ^ n)` | `⊢ P (a ^ n * b ^ n)` |

**R16 · `linarith`** **closes** a goal `=`, `≤`, `<` that follows *linearly* from the hypotheses.
Products of unknowns such as `y * z` count as one atom. Use it to solve the third hypothesis for the dot
product: `have hpq' : inner ℝ p.spatialPart q.spatialPart = p.timeComponent * q.timeComponent := by linarith`,
then `rw [hpq']`. Placeholders: `(x y z : ℝ)`.

| Before | After |
|---|---|
| `h : x - y * z = 0 ⊢ y * z = x` | closed by `linarith` |

**R17 · `nlinarith`** **closes** a polynomial (in)equality. Like `linarith`, but it first multiplies
hypotheses (and hint terms `nlinarith [t]`) in pairs, so it can use `hp`, `hq` multiplied by squares.
Substitute the inner product first (R16): `nlinarith` treats `inner ℝ x y` as an unknown.
Placeholders: `(a b u v : ℝ)`.

| Before | After |
|---|---|
| `hu : u = a ^ 2, hv : v = b ^ 2 ⊢ a ^ 2 * v + b ^ 2 * u - 2 * u * v = 0` | closed by `nlinarith` |

### Worked combination W1 (not the exercise's objects)

**W1: a length from three numbers.** For `x y : EuclideanSpace ℝ (Fin 3)` with `‖x‖ ^ 2 = 1`,
`‖y‖ ^ 2 = 1`, `inner ℝ x y = 1`: R11, then `rw [hx, hy, hxy]`, then `norm_num`:

```lean-goal
⊢ ‖x - y‖ ^ 2 = 0
⊢ ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 = 0
⊢ 1 - 2 * 1 + 1 = 0
```

---

## Part 3 · `ext_time_space` (milestone 3)

Statement: `p.timeComponent = q.timeComponent` and `p.spatialPart = q.spatialPart` give `p = q`. This is
R5 (`funext μ`), R6 (`match μ`), then R7 in the time arm and R8 in the space arm: `exact congrArg (· i) hs`
closes `p (Sum.inr i) = q (Sum.inr i)` because `p.spatialPart.ofLp i` is `p (Sum.inr i)` by definition.

---

## Part 4 · `parallel_of_null_orth`

Statement: `∃ r : ℝ, p = r • q`. Prove milestones 1–3 first. Then: `have hb := time_ne_zero_of_null q hq hq0`,
`have h := key p q hp hq hpq`, turn `h` into `q⁰ • p⃗ = p⁰ • q⃗` (R18–R20), choose `r = p⁰ / q⁰` and
reduce to time and space with milestone 3 (R21), and prove each with R22 and R23–R27.

**R18 · `rw [sq_eq_zero_iff] at h`** changes the **context**: `a ^ 2 = 0 ↔ a = 0`. Placeholders: `(a : ℝ)`
(any type with `*`, `0` and no nilpotents).

| Before | After |
|---|---|
| `h : a ^ 2 = 0 ⊢ G` | `h : a = 0 ⊢ G` |

**R19 · `rw [norm_eq_zero] at h`** changes the **context**: `‖x‖ = 0 ↔ x = 0`. Placeholders:
`{d : ℕ} (x : EuclideanSpace ℝ (Fin d))`.

| Before | After |
|---|---|
| `h : ‖x‖ = 0 ⊢ G` | `h : x = 0 ⊢ G` |

**R20 · `rw [sub_eq_zero] at h`** changes the **context**: `a - b = 0 ↔ a = b`. Placeholders:
`{d : ℕ} (x y : EuclideanSpace ℝ (Fin d))`. R18, R19, R20 go in one `rw [...] at h`.

| Before | After |
|---|---|
| `h : x - y = 0 ⊢ G` | `h : x = y ⊢ G` |

**R21 · `refine ⟨r, f _ _ ?_ ?_⟩`** changes the **goal list**: the witness `r` of `∃` is given now, and the
remaining goal is proved by a lemma `f` whose two explicit arguments `_` Lean finds by unification and whose
two premises `?_` become new goals. In Part 4, `f` is `ext_time_space` and `r` is
`p.timeComponent / q.timeComponent`. Placeholders: `{α : Type} (A B : α → α → Prop)
(f : ∀ u v, A u v → B u v → u = v) (p : α) (s : ℝ → α) (r : ℝ)`.

| Before | After |
|---|---|
| `⊢ ∃ t, p = s t` | `⊢ A p (s r)`, `⊢ B p (s r)` |

**R22 · `change G'`** changes the **goal** to `G'`, which must be the same up to unfolding definitions.
`(r • q).timeComponent` is `r * q.timeComponent` and `(r • q).spatialPart` is `r • q.spatialPart` by
definition, but `rw` and `field_simp` only see the written form. Placeholders:
`{d : ℕ} (p q : Lorentz.Vector d) (r : ℝ)`.

| Before | After |
|---|---|
| `⊢ p.timeComponent = (r • q).timeComponent` | `⊢ p.timeComponent = r * q.timeComponent` |
| `⊢ P (r • q).spatialPart` | `⊢ P (r • q.spatialPart)` |

**R23 · `field_simp`** **closes** (or simplifies) a goal with fractions by multiplying out the denominators.
It needs each denominator's `≠ 0` fact in the context (here `hb : q.timeComponent ≠ 0`, from milestone 1).
Placeholders: `(a b : ℝ) (hb : b ≠ 0)`.

| Before | After |
|---|---|
| `hb : b ≠ 0 ⊢ a = a / b * b` | closed by `field_simp` |

**R24 · `rw [div_eq_inv_mul]`** changes the **goal**: `a / b = b⁻¹ * a`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a / b)` | `⊢ P (b⁻¹ * a)` |

**R25 · `smul_smul`** changes the **goal**: `a • b • x = (a * b) • x`. Right to left, `rw [← smul_smul]`
splits a product of scalars into two actions; left to right it merges them. Placeholders:
`{d : ℕ} (a b : ℝ) (x : EuclideanSpace ℝ (Fin d))`.

| Before | After `rw [← smul_smul]` |
|---|---|
| `⊢ P ((a * b) • x)` | `⊢ P (a • b • x)` |

| Before | After `rw [smul_smul]` |
|---|---|
| `⊢ P (a • b • x)` | `⊢ P ((a * b) • x)` |

**R26 · `rw [inv_mul_cancel₀ hb]`** changes the **goal**: `b ≠ 0 → b⁻¹ * b = 1`. Placeholders:
`(b : ℝ) (hb : b ≠ 0)`.

| Before | After |
|---|---|
| `⊢ P (b⁻¹ * b)` | `⊢ P 1` |

**R27 · `rw [one_smul]`** changes the **goal**: `1 • x = x`. If the goal becomes `x = x`, `rw` closes it.
Placeholders: `{d : ℕ} (x : EuclideanSpace ℝ (Fin d))`.

| Before | After |
|---|---|
| `⊢ P (1 • x)` | `⊢ P x` |

### Worked combination W2 (not the exercise's objects)

**W2: dividing an equation of vectors by a scalar.** From `h : 2 • x = 6 • y` prove `x = 3 • y`. Write
`3` as `2⁻¹ * 6` (a `show … by norm_num`), split it (R25 ←), replace `6 • y` by `2 • x` (`rw [← h]`),
merge (R25), cancel (R26 with `(by norm_num)`), and R27 closes `x = x`:

```lean-goal
⊢ x = 3 • y
⊢ x = (2⁻¹ * 6) • y
⊢ x = 2⁻¹ • 6 • y
⊢ x = 2⁻¹ • 2 • x
⊢ x = (2⁻¹ * 2) • x
⊢ x = 1 • x
```

The space goal of Part 4 is the same chain with R24 in place of the `show`: `p⁰ / q⁰` becomes
`(q⁰)⁻¹ * p⁰`, and `h : q⁰ • p⃗ = p⁰ • q⃗` is used right to left.

---

## Traps

- You type `⟪p, q⟫ₘ`, the infoview prints `(minkowskiProduct p) q`. Both are the same term.
- R2 writes $(p^0)^2$ as `‖p.timeComponent‖ ^ 2`, a norm around a real number. Clear it with
  `simp only [Real.norm_eq_abs, sq_abs] at hp hq` (R10) before `linarith`/`nlinarith`, or they see
  `‖p⁰‖ ^ 2` and `p⁰ ^ 2` as unrelated.
- Bare `mul_smul` is ambiguous after `open Lorentz Vector` (it also names `Vector.mul_smul`). Use
  `smul_smul` (R25), possibly with `←`.
- `simp at hq` in Part 1 leaves `(fun i => q (Sum.inr i)) = 0`, not `q.spatialPart = 0`. That is fine:
  `congrArg (· i) hq` still closes the space arm (R8).
- `rw [← h]` with `h : q⁰ • p⃗ = p⁰ • q⃗` needs `p⁰ • q⃗` literally in the goal. Get it with R24 and
  `rw [← smul_smul]`: `(p⁰ / q⁰) • q⃗` → `((q⁰)⁻¹ * p⁰) • q⃗` → `(q⁰)⁻¹ • p⁰ • q⃗`.
- `rw` does not see through `(r • q).timeComponent`; state the unfolded goal with `change` (R22) first.
- `nlinarith` treats `inner ℝ p⃗ q⃗` as an unknown; substitute it by `p⁰ * q⁰` (R16) before calling it.
- In a tactic `match`, the arms `| Sum.inl 0 => …` start at the column of `match` or further right, and each
  arm must close its goal.
- The milestones are optional, but they must come before `parallel_of_null_orth` in the file to be used.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `a ≠ b` | `intro h0` (goal becomes `False`) | R1 |
| `⟪p, p⟫ₘ` in components | `rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at h` | R2 |
| `⟪p, q⟫ₘ` in components | `rw [minkowskiProduct_eq_timeComponent_spatialPart] at h` | R9 |
| `‖0‖ ^ 2 - ‖x‖ ^ 2 = 0` → spatial part `= 0` | `simp at h` | R3 |
| use `hne : a ≠ b` on `False` | `apply hne` | R4 |
| vector equation → components | `funext μ` then `match μ with \| Sum.inl 0 => … \| Sum.inr i => …` | R5, R6 |
| time arm | `exact h0` (`p.timeComponent` is `p (Sum.inl 0)`) | R7 |
| space arm | `exact congrArg (· i) hs` | R8 |
| `‖x‖ ^ 2 → x ^ 2` for real `x` | `simp only [Real.norm_eq_abs, sq_abs]` | R10 |
| expand `‖x - y‖ ^ 2` | `rw [norm_sub_sq_real]` | R11 |
| pull scalars out of norms and inner products | `rw [norm_smul, real_inner_smul_left, real_inner_smul_right]` | R12–R14 |
| `(a * b) ^ n → a ^ n * b ^ n` | `mul_pow` | R15 |
| linear / polynomial arithmetic | `linarith` / `nlinarith` | R16, R17 |
| `‖x - y‖ ^ 2 = 0 → x = y` | `rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h` | R18–R20 |
| witness plus a lemma with open premises | `refine ⟨r, f _ _ ?_ ?_⟩` | R21 |
| unfold `(r • q).timeComponent`, `(r • q).spatialPart` | `change …` | R22 |
| fractions with `b ≠ 0` in context | `field_simp` | R23 |
| `a / b → b⁻¹ * a` | `rw [div_eq_inv_mul]` | R24 |
| split / merge scalars | `rw [← smul_smul]` / `rw [smul_smul]` | R25 |
| `b⁻¹ * b → 1`, `1 • x → x` | `rw [inv_mul_cancel₀ hb, one_smul]` | R26, R27 |
| see the state | infoview | |
