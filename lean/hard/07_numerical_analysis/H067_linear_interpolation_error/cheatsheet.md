# H067 · Linear interpolation error: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, the derivative
predicate `HasDerivAt` and its arithmetic (sum, product, constant multiple), continuity (`Continuous`,
`ContinuousAt`, `ContinuousOn`), intervals as sets, Rolle's theorem (`exists_hasDerivAt_eq_zero`), absolute
values, and the tactics `set`, `linarith`, `linear_combination`, `gcongr`.

The mathematics. Write `s = (f b - f a) / (b - a)` for the chord's slope and `g t = f t - (f a + s (t - a))` for
the chord error, so `g a = g b = 0`. For an interior `a < x < b` put `K = g x / ((x - a)(x - b))` (the
denominator is nonzero) and `φ t = g t - K (t - a)(t - b)`. Then `φ a = φ x = φ b = 0`. Rolle on `[a, x]` and
`[x, b]` gives `ξ₁ < ξ₂` with `φ' ξ₁ = φ' ξ₂ = 0`; Rolle on `φ'` over `[ξ₁, ξ₂]` gives `η ∈ (a, b)` with
`φ'' η = f'' η - 2K = 0`. Hence `g x = K (x - a)(x - b) = f'' η / 2 · (x - a)(x - b)` (`interp_error_eq`), and
with `|f'' η| ≤ M` and `(x - a)(x - b) = -(x - a)(b - x)`, `|g x| ≤ M/2 · (x - a)(b - x)`. At `x = a` and `x = b`
both sides are `0`.

## How to read an entry

Each entry is one tactic or one lemma used with `have`/`exact`/`rw`/`simp only`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`.
- `G : Prop` is an arbitrary goal. Most lemmas here are *forward* facts: `have h := lemma args` adds `h`
  to the context; in the guide a hypothesis `k : … → G` then consumes it.
- Placeholders are written as Lean binders: reals `(a b c d e x : ℝ)`, functions `(g l : ℝ → ℝ)`, sets
  `(s : Set ℝ)`. The Mathlib lemmas hold for any normed field or ordered field; `ℝ` meets every requirement.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. A
  hypothesis containing `, ` (such as `∃ c ∈ s, Q c`) is written outside the `⊢` cell.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | the real numbers (Mathlib's `Real`), an ordered field. Lean sets `x / 0 = 0`, so cancelling `/ b` needs `b ≠ 0` |
| `f'`, `f''` | ordinary function *variables*. Nothing makes them derivatives except the hypotheses `hf`, `hf'` |
| `HasDerivAt g d x` | `g` is differentiable at `x` with derivative `g'(x) = d`. A *proposition*, not a function |
| `fun x => x` | the identity function `y ↦ y`; Lean may rename the bound variable (`fun y => …` prints as `fun x => …`) |
| `g * l`, `g - l` (functions) | the pointwise product / difference, `fun y => g y * l y`. Definitionally equal to the `fun` spelling, so `exact` accepts either (R5, R6) |
| `(fun x => x - a) * fun x => x - b` | the same pointwise product with both factors written as `fun` (W1) |
| `Continuous g` | `g : ℝ → ℝ` is continuous everywhere |
| `ContinuousAt g x` | `g` is continuous at the point `x` |
| `ContinuousOn g s` | `g` restricted to the set `s` is continuous |
| `Set.Icc a b` | the closed interval `[a, b] = {x \| a ≤ x ∧ x ≤ b}` ("I-closed-closed"); `Icc` after `open Set` |
| `Set.Ioo a b` | the open interval `(a, b) = {x \| a < x ∧ x < b}` ("I-open-open") |
| `x ∈ Set.Ioo a b` | *by definition* `a < x ∧ x < b`: `hx.1`, `hx.2`, `⟨h1, h2⟩`, `obtain ⟨h1, h2⟩ := hx` work on it (R20, R22, R25) |
| `∀ t ∈ s, Q t` | `∀ t, t ∈ s → Q t`; prove it with `fun t ht => …` (or `fun t _ => …` if `ht` is unused) |
| `∃ c ∈ s, Q c` | `∃ c, c ∈ s ∧ Q c`; take it apart with R19, build it with R22 |
| `k : ℝ := e` | a local definition made by `set` (R8): `k` abbreviates `e`, and `simp only [k]` unfolds it (R14) |
| `\|a\|` | absolute value of `a` |
| `a ≠ b` | `¬(a = b)`, that is `a = b → False` |
| `case ha`, `case hb`, `case hab` | goal names after `apply mul_ne_zero`, `apply mul_nonneg`, `gcongr`; ignore them |
| `case inl`, `case inr`, `case inr.inl` | after `rcases h with … \| …`: the left / right side of an `∨` (R27); a second `rcases` inside `inr` gives `inr.inl`, `inr.inr` |
| `u / 2 * c`, `2 * K / 2` | `*` and `/` group to the left: `(u / 2) * c`, `(2 * K) / 2` |

---

## Part 1 · `aux_deriv` (milestone)

Statement: for `hf : ∀ t, HasDerivAt f (f' t) t`, the function
`t ↦ f t - (f a + s * (t - a)) - K * ((t - a) * (t - b))` has derivative `f' t - s - K * (2 * t - a - b)` at `t`.
Build the derivative of each piece forward with R1–R6, then fix its shape with R7.

**R1 · `hasDerivAt_id' x`** changes the **context**: `hasDerivAt_id' x : HasDerivAt (fun x => x) 1 x`, the slope
of `y ↦ y`. Placeholders: `(x : ℝ)`. (`hasDerivAt_id x` is the same fact stated for `id`.)

| Before | After `have hid := hasDerivAt_id' x` |
|---|---|
| `⊢ G` | `hid : HasDerivAt (fun x => x) 1 x ⊢ G` |

**R2 · `HasDerivAt.sub_const`** changes the **context**. The lemma is
`HasDerivAt g d x → HasDerivAt (fun y => g y - c) d x`; the constant is explicit, `hg.sub_const c`.
Placeholders: `(g : ℝ → ℝ) (d c x : ℝ)`. From R1: `hid.sub_const a : HasDerivAt (fun x => x - a) 1 x`.

| Before | After `have h2 := hg.sub_const c` |
|---|---|
| `hg : HasDerivAt g d x ⊢ G` | `h2 : HasDerivAt (fun x => g x - c) d x ⊢ G` |

**R3 · `HasDerivAt.const_mul`** changes the **context**. The lemma is
`HasDerivAt g d x → HasDerivAt (fun y => c * g y) (c * d) x`, written `hg.const_mul c`. Placeholders:
`(g : ℝ → ℝ) (d c x : ℝ)`.

| Before | After `have h3 := hg.const_mul c` |
|---|---|
| `hg : HasDerivAt g d x ⊢ G` | `h3 : HasDerivAt (fun y => c * g y) (c * d) x ⊢ G` |

**R4 · `HasDerivAt.const_add`** changes the **context**. The lemma is
`HasDerivAt g d x → HasDerivAt (fun y => c + g y) d x`, written `hg.const_add c`; the constant goes on the
*left*. Placeholders: `(g : ℝ → ℝ) (d c x : ℝ)`. In the exercise: the chord `f a + s * (t - a)`.

| Before | After `have h4 := hg.const_add c` |
|---|---|
| `hg : HasDerivAt g d x ⊢ G` | `h4 : HasDerivAt (fun x => c + g x) d x ⊢ G` |

**R5 · `HasDerivAt.mul`** changes the **context**: the product rule,
`HasDerivAt g d x → HasDerivAt l e x → HasDerivAt (g * l) (d * l x + g x * e) x`, written `hg.mul hl`. The
function is the pointwise product `g * l`. Placeholders: `(g l : ℝ → ℝ) (d e x : ℝ)`. In the exercise:
`(t - a) * (t - b)` from two R2's, with derivative `1 * (t - b) + (t - a) * 1`.

| Before | After `have h5 := hg.mul hl` |
|---|---|
| `hg : HasDerivAt g d x, hl : HasDerivAt l e x ⊢ G` | `h5 : HasDerivAt (g * l) (d * l x + g x * e) x ⊢ G` |

**R6 · `HasDerivAt.sub`** changes the **context**. The lemma is
`HasDerivAt g d x → HasDerivAt l e x → HasDerivAt (g - l) (d - e) x`, written `hg.sub hl`. Placeholders:
`(g l : ℝ → ℝ) (d e x : ℝ)`. (`HasDerivAt.add` is the same for `+`.)

| Before | After `have h6 := hg.sub hl` |
|---|---|
| `hg : HasDerivAt g d x, hl : HasDerivAt l e x ⊢ G` | `h6 : HasDerivAt (g - l) (d - e) x ⊢ G` |

**R7 · `HasDerivAt.congr_deriv`** changes the **goal**. The lemma is
`HasDerivAt g d x → d = e → HasDerivAt g e x`: keep the function, replace the derivative by an equal one.
R1–R6 always produce a derivative with `* 1`, `1 * …` and nested `-`; `hg.congr_deriv (by ring)` trades it for
the one the statement wants. Placeholders: `(g : ℝ → ℝ) (d e x : ℝ) (hg : HasDerivAt g d x)`.

| Before | After `refine hg.congr_deriv ?_` |
|---|---|
| `hg : HasDerivAt g d x ⊢ HasDerivAt g e x` | `⊢ d = e` |

**W1: a scaled parabola, R1, R2, R5, R3, R7.** `((hid.sub_const 1).mul (hid.sub_const 3)).const_mul 3` has the
function `fun y => 3 * ((fun x => x - 1) * fun x => x - 3) y` and the derivative
`3 * (1 * (t - 3) + (t - 1) * 1)`. Both differ from the goal only in spelling: the function is definitionally
equal (so no rewrite is needed), and the derivative is fixed by `congr_deriv (by ring)`:

```lean-goal
⊢ HasDerivAt (fun y => 3 * ((y - 1) * (y - 3))) (6 * t - 12) t
```

---

## Part 2 · `interp_error_eq` (milestone)

Statement: for `a < x < b`, there is `η ∈ (a, b)` with
`f x - (f a + (f b - f a) / (b - a) * (x - a)) = f'' η / 2 * ((x - a) * (x - b))`. Name `s`, `K`, `φ`, `φ'`
(R8), get their derivatives (`aux_deriv`, R1–R7), their continuity (R11, R12), the three zeros (R13–R15),
apply Rolle three times (R16–R21), then assemble (R22–R24).

**R8 · `set k := e with hk`** changes the **goal and the context**: every `e` is replaced by the new local
definition `k`, and `hk : k = e` is added (omit `with hk` if you do not need it). It also rewrites `e`
inside later `set`s, so name the slope `s` first and `K`'s and `φ`'s bodies will mention `s`.
Placeholders: `(u v : ℝ)`, `e = u / v`.

| Before | After |
|---|---|
| `h : P (u / v) ⊢ P (u / v)` | `k : ℝ := u / v, h : P k, hk : k = u / v ⊢ P k` |

**R9 · `mul_ne_zero`** changes the **goal list**: `a ≠ 0 → b ≠ 0 → a * b ≠ 0`. As a term,
`mul_ne_zero (by linarith) (by linarith)`. Placeholders: `(a b : ℝ)`. In the exercise: `hden`.

| Before | After `apply mul_ne_zero` |
|---|---|
| `⊢ a * b ≠ 0` | `⊢ a ≠ 0`, `⊢ b ≠ 0` |

**R10 · `linarith`** **closes** a goal `t < u`, `t ≤ u`, `t = u` or `t ≠ u` that follows from the hypotheses by
adding them with nonnegative coefficients. Products of variables are atoms. Placeholders: `(a x : ℝ) (h : a < x)`.

| Before | After |
|---|---|
| `h : a < x ⊢ x - a ≠ 0` | closed |

**R11 · `continuous_iff_continuousAt`** changes the **goal**: `Continuous g ↔ ∀ x, ContinuousAt g x`. As a term,
`continuous_iff_continuousAt.mpr fun t => …`. Placeholders: `(g : ℝ → ℝ)`.

| Before | After `rw [continuous_iff_continuousAt]` |
|---|---|
| `⊢ Continuous g` | `⊢ ∀ (x : ℝ), ContinuousAt g x` |

**R12 · `HasDerivAt.continuousAt`** changes the **context**: differentiable at `x` implies continuous at `x`,
`HasDerivAt g d x → ContinuousAt g x`. Placeholders: `(g : ℝ → ℝ) (d x : ℝ)`. With R11:
`continuous_iff_continuousAt.mpr fun t => (hφ t).continuousAt` (W2).

| Before | After `have hc := hg.continuousAt` |
|---|---|
| `hg : HasDerivAt g d x ⊢ G` | `hc : ContinuousAt g x ⊢ G` |

**R13 · `div_mul_cancel₀`** changes the **goal**: `div_mul_cancel₀ a hb : a / b * b = a` for `hb : b ≠ 0`. The
first argument may be `_`. Lean sees through a `set` name, so `div_mul_cancel₀ _ hb` matches `s * (b - a)` with
`s := (f b - f a) / (b - a)` without unfolding `s`, both as a term and in `rw`. Used four times:
`hsb : s * (b - a) = f b - f a := div_mul_cancel₀ _ (by linarith)`, `φ x = 0` (with `hden`), the last step of
`interp_error_eq`, and the endpoint `x = b` of Part 3. Placeholders: `(a b : ℝ) (hb : b ≠ 0)`.

| Before | After `rw [div_mul_cancel₀ a hb]` |
|---|---|
| `⊢ P (a / b * b)` | `⊢ P a` |

**R14 · `simp only [k]`** changes the **goal**: it unfolds the `set` name `k` and performs the application
`(fun t => …) y` (β-reduction). `simp [k]` also simplifies afterwards, which closes `φ a = 0` (`a - a = 0`,
`0 * _ = 0`). `simp only [φ, K]` unfolds two names at once. Placeholders: `(g : ℝ → ℝ) (c y : ℝ)`.

| Before | After `set k := fun t => g t - c * t with hk` | After `simp only [k]` |
|---|---|---|
| `⊢ P ((fun t => g t - c * t) y)` | `k : ℝ → ℝ := fun t => g t - c * t ⊢ P (k y)` | `⊢ P (g y - c * y)` |

**R15 · `linear_combination e`** **closes** an equation `lhs = rhs` when `lhs - rhs - (e₁ - e₂)` is `0` by `ring`,
where `e : e₁ = e₂` is a proof (possibly scaled: `-h`, `2 * h`, `h₁ + h₂`). In the exercise: after
`simp only [φ]`, `φ b = 0` is `linear_combination -hsb`. Placeholders: `(u v w : ℝ) (h : u * v = w)`.

| Before | After `linear_combination -h` |
|---|---|
| `h : u * v = w ⊢ w - u * v + 0 = 0` | closed |

**R16 · `exists_hasDerivAt_eq_zero`** (Rolle) changes the **context**. The lemma is
`a < b → ContinuousOn g (Set.Icc a b) → g a = g b → (∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x) →
∃ c ∈ Set.Ioo a b, g' c = 0`. Our derivative facts hold everywhere, so the last argument is
`fun x _ => hd x` (ignore the membership). Placeholders: `(g g' : ℝ → ℝ) (a b : ℝ)`.

| Before | After `have hr := exists_hasDerivAt_eq_zero hab hc he fun x _ => hd x` |
|---|---|
| `⊢ G` | `hr : ∃ c ∈ Set.Ioo a b, g' c = 0` in the context, `⊢ G` |

**R17 · `Continuous.continuousOn`** changes the **context**: `Continuous g → ContinuousOn g s` for any `s`
(`s` is found from where you use it; in the guide it is given as `(s := s)`). Placeholders:
`(g : ℝ → ℝ) (s : Set ℝ)`. In the exercise: `cφ.continuousOn` as Rolle's second argument.

| Before | After `have hs := hg.continuousOn (s := s)` |
|---|---|
| `hg : Continuous g ⊢ G` | `hs : ContinuousOn g s ⊢ G` |

**R18 · `h₁.trans h₂.symm`** (`Eq.trans`, `Eq.symm`) changes the **context**: from `h₁ : u = 0` and `h₂ : v = 0`,
`h₂.symm : 0 = v` and `h₁.trans h₂.symm : u = v`. This is Rolle's `g a = g b` argument: `φa.trans φx.symm`, and
`h1.trans h2.symm` for the two zeros of `φ'`. Placeholders: `(u v : ℝ)`.

| Before | After `have he := h₁.trans h₂.symm` |
|---|---|
| `h₁ : u = 0, h₂ : v = 0 ⊢ G` | `he : u = v ⊢ G` |

**R19 · `obtain ⟨c, hc, h⟩ := hr`** changes the **context**: `hr : ∃ c ∈ s, Q c` is replaced by the point, its
membership and its property. Combine with R16: `obtain ⟨ξ₁, hξ₁, h1⟩ := exists_hasDerivAt_eq_zero …`.
Placeholders: `(s : Set ℝ) (Q : ℝ → Prop)`.

| Before | After |
|---|---|
| `hr : ∃ c ∈ s, Q c` in the context, `⊢ G` | `c : ℝ, hc : c ∈ s, h : Q c ⊢ G` |

**R20 · `hc.1`, `hc.2`** change the **context**: `hc : c ∈ Set.Ioo a b` *is* `a < c ∧ c < b`, so its
projections are `hc.1 : a < c` and `hc.2 : c < b`. Placeholders: `(a b c : ℝ)`.

| Before | After `have h2 := hc.2` |
|---|---|
| `hc : c ∈ Set.Ioo a b ⊢ G` | `h2 : c < b ⊢ G` |

**R21 · `h₁.trans h₂`** (`LT.lt.trans`) changes the **context**: `a < b → b < c → a < c`. In the exercise:
`hξ₁.2.trans hξ₂.1 : ξ₁ < ξ₂` (both sides of `x`), and `hξ₁.1.trans hη.1 : a < η`. Placeholders: `(a b c : ℝ)`.

| Before | After `have h3 := h₁.trans h₂` |
|---|---|
| `h₁ : a < b, h₂ : b < c ⊢ G` | `h3 : a < c ⊢ G` |

**R22 · `refine ⟨c, ⟨h₁, h₂⟩, ?_⟩`** changes the **goal**: for `∃ x ∈ Set.Ioo a b, Q x`, give the point `c`, its
membership as the pair `⟨h₁, h₂⟩` (`a < c` and `c < b`), and leave `Q c` open. Placeholders:
`(a b c : ℝ) (Q : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ ∃ x ∈ Set.Ioo a b, Q x` | `⊢ Q c` |

**R23 · `rw [show u = w by tac]`** changes the **goal**: it proves the equation `u = w` on the spot and rewrites
with it. In the exercise: `show f'' η = 2 * K by linarith` (from the third Rolle's `f'' η - 2 * K = 0`), and in
Part 3 `show (x - a) * (x - b) = -((x - a) * (b - x)) by ring`. Placeholders: `(u w : ℝ)`.

| Before | After `rw [show u = w by linarith]` |
|---|---|
| `h : u - w = 0 ⊢ P u` | `⊢ P w` |

**R24 · `mul_div_cancel_left₀`** changes the **goal**: `mul_div_cancel_left₀ b ha : a * b / a = b` for
`ha : a ≠ 0`; with `a = 2` the proof is `two_ne_zero : (2 : ℝ) ≠ 0`. In the exercise: `2 * K / 2` → `K`.
Placeholders: `(b : ℝ)`.

| Before | After `rw [mul_div_cancel_left₀ b two_ne_zero]` |
|---|---|
| `⊢ P (2 * b / 2)` | `⊢ P b` |

After R24, `rw [hK]` puts `K`'s definition back, and R13 with `hden` makes both sides equal (`rw` closes it).

**W2: Rolle on `[1, 3]`** for `p y = (y - 1) * (y - 3)`: the derivative fact by R1, R2, R5, R7; continuity by
R11, R12; then R17 and R16, with `norm_num` for `1 < 3` and `p 1 = p 3`:

```lean-goal
⊢ ∃ c ∈ Set.Ioo 1 3, 2 * c - 4 = 0
```

**W3: a constant chosen to kill a value** (R8, R13): `set K := v / p with hK`, then `rw [hK, div_mul_cancel₀ v hp]`:

```lean-goal
⊢ v - v / p * p = 0
⊢ v - K * p = 0
⊢ v - v = 0
```

**W4: two Rolle points in order** (R19, R20, R21): from `c₁ ∈ (0, 1)` and `c₂ ∈ (1, 2)`,
`hc₁.2.trans hc₂.1 : c₁ < c₂`.

```lean-goal
⊢ ∃ c₁ c₂, c₁ < c₂ ∧ Q c₁ ∧ Q c₂
```

---

## Part 3 · `linear_interp_error`

Statement: for `x ∈ [a, b]` and `|f'' t| ≤ M` on `[a, b]`,
`|f x - (f a + (f b - f a) / (b - a) * (x - a))| ≤ M / 2 * ((x - a) * (b - x))`. Split off the endpoints
(R25–R27), use `interp_error_eq` inside, and turn the equation into a bound (R28–R35).

**R25 · `obtain ⟨h₁, h₂⟩ := hx`** changes the **context**: `hx : x ∈ Set.Icc a b` is the pair
`a ≤ x ∧ x ≤ b`. Placeholders: `(a b x : ℝ)`.

| Before | After |
|---|---|
| `hx : x ∈ Set.Icc a b ⊢ G` | `h₁ : a ≤ x, h₂ : x ≤ b ⊢ G` |

**R26 · `h.eq_or_lt`** (`LE.le.eq_or_lt`) changes the **context**: `a ≤ b → a = b ∨ a < b`. Placeholders:
`(a b : ℝ)`. Usually consumed at once by R27: `rcases h1.eq_or_lt with rfl | hax`.

| Before | After `have h' := h.eq_or_lt` |
|---|---|
| `h : a ≤ b ⊢ G` | `h' : a = b ∨ a < b ⊢ G` |

**R27 · `rcases h with rfl | h`** changes the **goal list and the context**: one goal per side of the `∨`. In the
first, the equation is *substituted*: one variable disappears everywhere and the other takes its place
(which one survives is Lean's choice; here `a`). In the second, `h : a < b` is added. Placeholders:
`(a b : ℝ) (P : ℝ → ℝ → Prop)`. In the exercise the substituted goal has `x - x` or `a - a`, and `simp` closes it.

| Before | After |
|---|---|
| `h : a = b ∨ a < b ⊢ P a b` | `⊢ P a a` (`b` gone), `h : a < b ⊢ P a b` |

**R28 · `mul_nonneg`** changes the **goal list**: `0 ≤ a → 0 ≤ b → 0 ≤ a * b`. As a term,
`mul_nonneg (by linarith) (by linarith)`. Placeholders: `(a b : ℝ)`. In the exercise: `hpos`.

| Before | After `apply mul_nonneg` |
|---|---|
| `⊢ 0 ≤ a * b` | `⊢ 0 ≤ a`, `⊢ 0 ≤ b` |

R29–R33 rewrite absolute values. Their states contain `|`, which cannot sit inside a table cell, so each shows
its before and after in a block (first line before, second line after).

**R29 · `rw [abs_mul]`** changes the **goal**: `abs_mul a b : |a * b| = |a| * |b|`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| first line below | second line below |

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R30 · `rw [abs_div]`** changes the **goal**: `abs_div a b : |a / b| = |a| / |b|`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| first line below | second line below |

```lean-goal
⊢ P |a / b|
⊢ P (|a| / |b|)
```

**R31 · `rw [abs_two]`** changes the **goal**: `abs_two : |2| = 2`.

| Before | After |
|---|---|
| first line below | second line below |

```lean-goal
⊢ P |2|
⊢ P 2
```

**R32 · `rw [abs_neg]`** changes the **goal**: `abs_neg a : |-a| = |a|` (Lean prints `|(-a)|`). Placeholders:
`(a : ℝ)`.

| Before | After |
|---|---|
| first line below | second line below |

```lean-goal
⊢ P |(-a)|
⊢ P |a|
```

**R33 · `rw [abs_of_nonneg ha]`** changes the **goal**: `abs_of_nonneg : 0 ≤ a → |a| = a`. Placeholders:
`(a : ℝ) (ha : 0 ≤ a)`. In the exercise: `abs_of_nonneg hpos`.

| Before | After |
|---|---|
| first line below | second line below |

```lean-goal
⊢ P |a|
⊢ P a
```

**R34 · `gcongr`** changes the **goal**: it reduces an inequality between two expressions of the same shape to
inequalities between the parts that differ. For `u / 2 * c ≤ v / 2 * c` that is `u ≤ v`; the side condition
`0 ≤ c` is taken from `hc` in the context (keep `hpos` there). If the remaining goal is itself a hypothesis,
`gcongr` closes it. Placeholders: `(u v c : ℝ) (hc : 0 ≤ c)`.

| Before | After |
|---|---|
| `hc : 0 ≤ c ⊢ u / 2 * c ≤ v / 2 * c` | `⊢ u ≤ v` |

**R35 · `Set.Ioo_subset_Icc_self`** changes the **context**: `Set.Ioo a b ⊆ Set.Icc a b`, applied to
`hx : x ∈ Set.Ioo a b` it gives `x ∈ Set.Icc a b`. In the exercise: `hM η (Ioo_subset_Icc_self hη)`.
Placeholders: `(a b x : ℝ)`.

| Before | After `have hx' := Set.Ioo_subset_Icc_self hx` |
|---|---|
| `hx : x ∈ Set.Ioo a b ⊢ G` | `hx' : x ∈ Set.Icc a b ⊢ G` |

---

## Traps

- Mathlib's Rolle (`exists_hasDerivAt_eq_zero`, R16) is allowed here; H049 proves it from scratch. The point of
  this problem is the auxiliary-function argument.
- `f'` and `f''` are variables, not derivatives: the only link is `hf`, `hf'`. Never write `deriv`.
- `field_simp` rewrites `s` and `K` in unhelpful ways on these goals; cancel with `div_mul_cancel₀` (R13).
- After `set`, the goal and hypotheses show the short name. `rw` does not look inside it: unfold with
  `simp only [φ]` (R14) or rewrite with the `with hK` equation (R8).
- `set` the slope `s` before `K` and `φ`, and write `φ`'s body exactly as in `aux_deriv`, so that
  `fun t => aux_deriv f f' hf a b s K t` has type `∀ t, HasDerivAt φ (φ' t) t` (definitional unfolding).
- `hden : (x - a) * (x - b) ≠ 0` is needed before `K` can be cancelled; Lean's `x / 0 = 0` makes the
  cancellation lemmas require it.
- Rolle wants `∀ x ∈ Ioo a b, …`; pass `fun t _ => hφ t`. It wants `g a = g b`, not two zeros: use R18.
- The third Rolle runs on `[ξ₁, ξ₂]`, so its first argument is `ξ₁ < ξ₂` (R21), and `η ∈ (a, b)` is built
  from the chain `a < ξ₁ < η < ξ₂ < b`.
- After `rcases h with rfl | h` (R27) the surviving variable may be either one; close the endpoint goals with
  `simp`, not by names. At `x = b` cancel the slope's `/ (b - a) * (b - a)` first (R13).
- `(x - a) * (x - b)` is `≤ 0` inside `(a, b)`: rewrite it as `-((x - a) * (b - x))` (R23) before R32, R33.
- `t1 ; t2` runs `t2` on the first goal only; use `·` bullets for the endpoint cases.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| derivative of `y ↦ y` | `hasDerivAt_id' t` | R1 |
| derivative of `g - c`, `c * g`, `c + g` | `hg.sub_const c`, `hg.const_mul c`, `hg.const_add c` | R2–R4 |
| product / difference rule | `hg.mul hl`, `hg.sub hl` | R5, R6 |
| fix the derivative's shape | `h.congr_deriv (by ring)` | R7 |
| name a subterm | `set K := e with hK` | R8 |
| `a * b ≠ 0` | `mul_ne_zero (by linarith) (by linarith)` | R9, R10 |
| linear (in)equality, `≠` | `linarith` | R10 |
| continuity from derivatives | `continuous_iff_continuousAt.mpr fun t => (h t).continuousAt` | R11, R12 |
| `a / b * b = a` | `div_mul_cancel₀ _ hb` | R13 |
| unfold a `set` name | `simp only [φ]` / `simp [φ]` | R14 |
| equation linear in a hypothesis | `linear_combination -h` | R15 |
| Rolle | `obtain ⟨c, hc, h⟩ := exists_hasDerivAt_eq_zero hab hg.continuousOn he fun t _ => hd t` | R16, R17, R19 |
| `u = 0`, `v = 0` → `u = v` | `h₁.trans h₂.symm` | R18 |
| parts of `c ∈ Set.Ioo a b` | `hc.1`, `hc.2` | R20 |
| chain `<` | `h₁.trans h₂` | R21 |
| prove `∃ η ∈ Set.Ioo a b, Q η` | `refine ⟨η, ⟨h₁, h₂⟩, ?_⟩` | R22 |
| rewrite with a fact proved inline | `rw [show u = w by linarith]` | R23 |
| `2 * K / 2 = K` | `mul_div_cancel_left₀ _ two_ne_zero` | R24 |
| split `x ∈ Set.Icc a b` | `obtain ⟨h1, h2⟩ := hx` | R25 |
| endpoint or interior | `rcases h1.eq_or_lt with rfl \| hax` | R26, R27 |
| `0 ≤ a * b` | `mul_nonneg (by linarith) (by linarith)` | R28 |
| split `\|·\|` | `rw [abs_mul, abs_div, abs_two, abs_neg, abs_of_nonneg h]` | R29–R33 |
| compare two sides of the same shape | `gcongr` | R34 |
| `(a, b) ⊆ [a, b]` | `Set.Ioo_subset_Icc_self hη` | R35 |
| see the state | infoview | |
