# M108 · cos on [0,1]: contraction and the Dottie number: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, `Real.cos`,
`Real.sin`, `Real.pi`; closed intervals `Set.Icc`; `Set.MapsTo`; norms `‖·‖` and absolute values `|·|`;
derivatives (`HasDerivAt`, `HasDerivWithinAt`), convex sets and the mean value bound; continuity
(`ContinuousOn`) and the intermediate value theorem; unique existence `∃!`; the tactics `linarith`,
`nlinarith`, `fun_prop`, `simpa`.

The mathematics. On `[0,1] ⊂ [0, π/2]` (as `π > 3`): `0 ≤ cos x ≤ 1`, so `cos` maps `[0,1]` into itself;
`|cos' t| = |sin t| = sin t ≤ sin 1` (sin is increasing there), so by the mean value theorem
`|cos x − cos y| ≤ sin 1 · |x − y|`; and `sin 1 < 1` since `sin x < x` for `x > 0`. The function
`g(x) = cos x − x` is continuous with `g(0) = 1 ≥ 0 ≥ cos 1 − 1 = g(1)`, so it has a zero `p` (the
Dottie number ≈ 0.739). Two fixed points `p, q` give `|q − p| ≤ sin 1 · |q − p|`, forcing `q = p`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after. A state that
contains `|…|` (absolute value) is repeated below its table in a `lean-goal` block, because a table cell
must escape `|` as `\|`.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` with `g : … → G` is an arbitrary goal that the new fact finishes.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as
  `[SeminormedAddGroup E]` is a requirement on `E` (a *type class*); each entry says which familiar types
  meet it.
- A lemma with hypotheses is used three ways: `exact lemma h₁ h₂` closes a goal of its conclusion's form;
  `apply lemma` turns that goal into one goal per hypothesis; `have h := lemma h₁ h₂` adds the
  conclusion to the context.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Real.cos x`, `Real.sin x`, `Real.pi` | cosine, sine, π on `ℝ` (no `open Real`, so the full names print) |
| `Set.Icc a b` | the closed interval `{x | a ≤ x ∧ x ≤ b}`; `x ∈ Set.Icc a b` *is* `a ≤ x ∧ x ≤ b` |
| `(0:ℝ)` | the numeral `0` read as a real number |
| `Set.MapsTo f s t` | `∀ ⦃x⦄, x ∈ s → f x ∈ t`: `f` sends `s` into `t` (`⦃x⦄`: `x` is filled in once `x ∈ s` is given) |
| `‖v‖` | the norm of `v` in a normed space; for `v : ℝ` it equals `|v|` (R11) |
| `\|v\|` | absolute value `max v (-v)` |
| `HasDerivAt f f' x` | `f : ℝ → ℝ` is differentiable at `x` with derivative the number `f'` |
| `HasDerivWithinAt f f' s x` | the same, but the limit uses only points of `s` (one-sided at an endpoint) |
| `Convex ℝ s` | for `x, y ∈ s` the segment between them lies in `s`; intervals are convex |
| `ContinuousOn f s` | `f` restricted to `s` is continuous |
| `f '' s` | the image `{f x | x ∈ s}`; `y ∈ f '' s` *is* `∃ x, x ∈ s ∧ f x = y` |
| `∀ t ∈ s, Q t` | `∀ t, t ∈ s → Q t`: `intro t ht` (or `fun t ht => …`) takes both apart |
| `∃ p ∈ s, Q p` | `∃ p, p ∈ s ∧ Q p` |
| `∃! x, P x` | exactly one `x`: `∃ x, P x ∧ ∀ y, P y → y = x` |
| `(fun x => P x) y` | `P y` not yet beta-reduced; it is the same proposition |
| `x✝ : …` | a hypothesis with no name you can type (the `⟨hq, hqfix⟩` pattern of R21 leaves one); ignore it |
| `this : …` | the fact added by `have := e` when you give no name |
| `𝕜`, `[RCLike 𝕜]` (in `#check` output) | the scalar field, `ℝ` or `ℂ`; here always `ℝ` |
| `case refine_1`, `case h0x` | the name of one goal among several |

---

## Part 1 · `cos_maps_to`

Statement: `Set.MapsTo Real.cos (Set.Icc 0 1) (Set.Icc 0 1)`: for `0 ≤ x ≤ 1`, `0 ≤ cos x ≤ 1`.

**R1 · `intro x ⟨h0, h1⟩`** changes the **context**. `Set.MapsTo` and `∈ Set.Icc` both unfold to what `intro`
expects, so one `intro` names the point and splits its membership. The same pattern works on a goal
`∀ x ∈ Set.Icc a b, Q x`, and in term mode: `fun t ⟨h0, h1⟩ => …`. Placeholders:
`(f : ℝ → ℝ) (a b : ℝ) (t : Set ℝ)`.

| Before | After |
|---|---|
| `⊢ Set.MapsTo f (Set.Icc a b) t` | `x : ℝ, h0 : a ≤ x, h1 : x ≤ b ⊢ f x ∈ t` |

**R2 · `refine ⟨?_, ?_⟩`** on interval membership changes the **goal list**: `y ∈ Set.Icc a b` is a pair, so
it splits into its two inequalities. `exact ⟨e₀, e₁⟩` does both at once. Placeholders: `(a b y : ℝ)`.

| Before | After |
|---|---|
| `⊢ y ∈ Set.Icc a b` | `⊢ a ≤ y`, `⊢ y ≤ b` |

**R3 · `apply Real.cos_nonneg_of_mem_Icc`** changes the **goal**. Lemma: `x ∈ Set.Icc (-(π / 2)) (π / 2) →
0 ≤ Real.cos x`. The new goal is again a pair (R2). Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ Real.cos x` | `⊢ x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)` |

**R4 · `Real.cos_le_one x`** **closes** a goal `Real.cos x ≤ 1`; it is the fact `∀ x : ℝ, cos x ≤ 1`. As an
extra fact for `linarith` it gives the endpoint `cos 1 - 1 ≤ 0` in Part 4. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `x : ℝ ⊢ Real.cos x ≤ 1` | no goals |

**R5 · `linarith [Real.pi_pos, Real.pi_gt_three]`** **closes** a goal that follows linearly from the
hypotheses and the facts in brackets. `Real.pi_pos : 0 < Real.pi`, `Real.pi_gt_three : 3 < Real.pi`.
`linarith` treats `Real.pi`, `Real.cos 1`, `|d|` as unknowns, so it needs these facts to know anything
about them. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `h1 : x ≤ 1 ⊢ x ≤ Real.pi / 2` | no goals |

---

## Part 2 · `cos_contracts`

Statement: for `x, y ∈ [0,1]`, `|cos x − cos y| ≤ sin 1 · |x − y|`. Plan: bound the derivative `−sin t` on
`[0,1]` (R10–R14), then the mean value bound (R6–R9), then convert norms to absolute values (R15).

### The mean value bound

**R6 · `Real.hasDerivAt_cos t`** **closes** `HasDerivAt Real.cos (-Real.sin t) t`: `cos' = −sin`.
Placeholders: `(t : ℝ)`.

| Before | After |
|---|---|
| `t : ℝ ⊢ HasDerivAt Real.cos (-Real.sin t) t` | no goals |

**R7 · `HasDerivAt.hasDerivWithinAt`** **closes** a within-`s` derivative goal from a plain one; written
with dot notation `hd.hasDerivWithinAt`. So `fun t _ => (Real.hasDerivAt_cos t).hasDerivWithinAt` proves
`∀ t ∈ s, HasDerivWithinAt Real.cos (-Real.sin t) s t` for any `s`. Placeholders:
`(f : ℝ → ℝ) (f' t : ℝ) (s : Set ℝ)`.

| Before | After |
|---|---|
| `hd : HasDerivAt f f' t ⊢ HasDerivWithinAt f f' s t` | no goals |

**R8 · `convex_Icc a b`** **closes** `Convex ℝ (Set.Icc a b)`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ Convex ℝ (Set.Icc a b)` | no goals |

**R9 · `have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hC hs hx hy`** changes the
**context**. Lemma (mean value bound): if `f` has derivative `f' t` within `s` at every `t ∈ s` (`hf`),
`‖f' t‖ ≤ C` on `s` (`hC`), `s` is convex (`hs`), and `x, y ∈ s`, then `‖f y − f x‖ ≤ C · ‖y − x‖`. The
conclusion has `y` first: pass the membership proofs in the order that gives the difference you want.
Placeholders: `(f f' : ℝ → ℝ) (s : Set ℝ) (C x y : ℝ)` (the lemma allows any `RCLike` field and normed
space; here `ℝ` throughout).

| Before | After |
|---|---|
| `⊢ G` | `h : ‖f y - f x‖ ≤ C * ‖y - x‖ ⊢ G` |

### Bounding the derivative

**R10 · `rw [norm_neg]`** changes the **goal**. Lemma: `‖-a‖ = ‖a‖`. Placeholders:
`{E : Type} [SeminormedAddGroup E] (a : E)` (E has a norm compatible with `+`, `-`; `ℝ`, `ℂ` qualify).

| Before | After |
|---|---|
| `⊢ P ‖-a‖` | `⊢ P ‖a‖` |

**R11 · `rw [Real.norm_eq_abs]`** changes the **goal**. Lemma: `‖r‖ = |r|` for `r : ℝ`. Placeholders:
`(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ‖r‖` | ⊢ P \|r\| |

```lean-goal
⊢ P |r|
```

**R12 · `rw [abs_of_nonneg]`** changes the **goal list**. Lemma: `0 ≤ a → |a| = a`, so the goal is rewritten
and a side goal `0 ≤ a` is added. Write `rw [abs_of_nonneg (proof of 0 ≤ a)]` to discharge it on the spot
(R13). Placeholders: `(a : ℝ)` (any ordered additive group).

| Before | After |
|---|---|
| ⊢ P \|a\| | `⊢ P a`, `⊢ 0 ≤ a` |

```lean-goal
⊢ P |a|
```

**R13 · `apply Real.sin_nonneg_of_nonneg_of_le_pi`** changes the **goal list**. Lemma:
`0 ≤ x → x ≤ π → 0 ≤ sin x`. The second goal comes from `x ≤ 1` and R5. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ Real.sin x` | `⊢ 0 ≤ x`, `⊢ x ≤ Real.pi` |

**R14 · `apply Real.sin_le_sin_of_le_of_le_pi_div_two`** changes the **goal list**. Lemma:
`-(π / 2) ≤ x → y ≤ π / 2 → x ≤ y → sin x ≤ sin y` (sin increases on `[-π/2, π/2]`). With `x := t`,
`y := 1`: the first two goals are R5, the third is `t ≤ 1`. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ Real.sin x ≤ Real.sin y` | `⊢ -(Real.pi / 2) ≤ x`, `⊢ y ≤ Real.pi / 2`, `⊢ x ≤ y` |

### Norms back to absolute values

**R15 · `simpa [Real.norm_eq_abs] using h`** **closes** the goal: it simplifies both `h` and the goal with
the given lemmas (plus the default `simp` set), then closes the goal with the simplified `h`. Use it when
`h` is the goal written with `‖·‖` instead of `|·|`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| h : ‖a‖ ≤ c * ‖b‖ ⊢ \|a\| ≤ c * \|b\| | no goals |

```lean-goal
⊢ |a| ≤ c * |b|
```

**W2** in `guide.lean` runs Part 2's whole chain for `sin` on `[-1, 2]` (derivative `cos`, bound `1`); its goal:

```lean-goal
⊢ |Real.sin u - Real.sin v| ≤ 1 * |u - v|
```

---

## Part 3 · `sin_one_lt_one`

Statement: `Real.sin 1 < 1`.

**R16 · `Real.sin_lt`** **closes** `Real.sin x < x` from `hx : 0 < x`. Lemma: `0 < x → sin x < x`.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `hx : 0 < x ⊢ Real.sin x < x` | no goals |

**R17 · `one_pos`** **closes** `0 < 1` in an ordered type such as `ℝ` (`norm_num` also does).

| Before | After |
|---|---|
| `⊢ 0 < 1` | no goals |

---

## Part 4 · `dottie_unique`

Statement: `∃! p, p ∈ Set.Icc (0:ℝ) 1 ∧ Real.cos p = p`. Existence by the intermediate value theorem
(R18–R20); uniqueness from Parts 2 and 3 (R21–R25).

### Existence

**R18 · `obtain ⟨p, hp, hfp⟩ := intermediate_value_Icc' hab hf ⟨h1, h2⟩`** changes the **context**. Lemma:
`a ≤ b → ContinuousOn f (Set.Icc a b) → Set.Icc (f b) (f a) ⊆ f '' Set.Icc a b`. The primed version is
for a function that goes *down* (`f b ≤ y ≤ f a`); unprimed `intermediate_value_Icc` is for `f a ≤ y ≤ f b`.
`⊆` applied to the membership `⟨h1, h2⟩ : y ∈ Set.Icc (f b) (f a)` gives `y ∈ f '' Set.Icc a b`, i.e.
`∃ p, p ∈ Set.Icc a b ∧ f p = y`, which `obtain` takes apart. In the exercise `f` is
`fun x => Real.cos x - x`: write the target type out, `obtain ⟨p, hp, hfix⟩ : ∃ p ∈ Set.Icc (0:ℝ) 1,
Real.cos p - p = 0 := …`, and Lean infers `f`; the two endpoint goals then read `Real.cos 1 - 1 ≤ 0`
(R4, R5) and `0 ≤ Real.cos 0 - 0` (R20). Placeholders: `(f : ℝ → ℝ) (a b y : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `p : ℝ, hp : p ∈ Set.Icc a b, hfp : f p = y ⊢ G` |

**R19 · `fun_prop`** **closes** continuity goals (`Continuous`, `ContinuousOn`, also differentiability) for
functions built from `+`, `-`, `*`, constants and known continuous functions such as `Real.sin`, `Real.cos`.

| Before | After |
|---|---|
| `⊢ ContinuousOn (fun x => Real.sin x + 2 * x) (Set.Icc a b)` | no goals |

**R20 · `Real.cos_zero`** (`Real.cos 0 = 1`) changes the **goal**; `simp` applies it and `sub_zero`
(`a - 0 = a`) by itself, and closes the goal outright when it becomes `0 ≤ 1`.

| Before | After |
|---|---|
| `⊢ P (Real.cos 0 - 0)` | `⊢ P 1` |

**W3** in `guide.lean` is the same `obtain` on `2 - x - x³` (decreasing from 2 to 0 on `[0,1]`, value 1).

### Uniqueness

**R21 · `refine ⟨a, ha, fun y hy => ?_⟩`** on `∃! x, P x` changes the **goal and the context**: give the
witness `a` and `ha : P a`; what is left is that any `y` with `P y` equals `a`. When `P` is a conjunction,
destructure it right there: `fun q ⟨hq, hqfix⟩ => ?_`, and the parts arrive beta-reduced (the
undestructured original stays in the context as `x✝`). Placeholders:
`{α : Type} (P : α → Prop) (a : α)`.

| Before | After |
|---|---|
| `⊢ ∃! x, P x` | `y : α, hy : (fun x => P x) y ⊢ y = a` |

**R22 · `rw [h₁, h₂] at h`** changes the **context**: it rewrites inside hypothesis `h`, left to right, and
leaves the goal alone. An equation can be proved inline: `rw [show Real.cos p = p by linarith] at h`.
Placeholders: `(u v w : ℝ) (P : ℝ → ℝ → Prop) (h₁ : u = w) (h₂ : v = w)`.

| Before | After |
|---|---|
| `h : P u v ⊢ P w w` | `h : P w w ⊢ P w w` |

**R23 · `abs_nonneg a`** **closes** `0 ≤ |a|`; mostly passed as an extra fact to `nlinarith`.

| Before | After |
|---|---|
| ⊢ 0 ≤ \|a\| | no goals |

```lean-goal
⊢ 0 ≤ |a|
```

**R24 · `nlinarith [facts]`** **closes** goals that need *products* of hypotheses. It multiplies pairs of
hypotheses (and the negated goal) and then runs `linarith`. In the example it multiplies `1 - s > 0` with
the negated goal `d > 0` to contradict `d ≤ s * d`. In the exercise `d` is `|q - p|` and `s` is
`Real.sin 1`; pass `abs_nonneg (q - p)` and `sin_one_lt_one` in brackets. Placeholders: `(d s : ℝ)`.

| Before | After |
|---|---|
| `hs : s < 1, h : d ≤ s * d ⊢ d ≤ 0` | no goals |

**R25 · `abs_nonpos_iff.mp`** changes the **context** (used with `have`). Lemma: `|a| ≤ 0 ↔ a = 0`; `.mp`
is the left-to-right direction. The example has `h0 : |a| ≤ 0` in the context. Then `linarith` turns `q - p = 0` into `q = p`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `h : a = 0 ⊢ G` |

**W4** in `guide.lean` runs R21–R25 for any map `g` with `|g u − g v| ≤ ½ |u − v|`. Its goal before and
after R21:

```lean-goal
⊢ ∃! x, g x = x
⊢ y = a
```

---

## Traps

- The mean value lemma's conclusion is `‖f y - f x‖ ≤ C * ‖y - x‖`: to get `cos x - cos y` you pass the
  membership of `y` first, then of `x` (R9).
- The derivative bound must use exactly the `f' t` that R6 produces: `‖-Real.sin t‖ ≤ Real.sin 1`, with the
  minus sign and the norm, not `|Real.sin t| ≤ …`; R10–R12 then reduce it to `Real.sin t ≤ Real.sin 1`.
- `linarith` knows nothing about `Real.pi`, `Real.sin`, `Real.cos`; feed it `Real.pi_pos`,
  `Real.pi_gt_three`, `Real.cos_le_one 1` in brackets (R5).
- `linarith` fails on `|q - p| ≤ Real.sin 1 * |q - p| → |q - p| ≤ 0`: the right side is a product of two
  unknowns. Use `nlinarith` (R24).
- `intermediate_value_Icc` vs `intermediate_value_Icc'`: `cos x - x` decreases, so you need the primed one,
  with endpoint goals `f 1 ≤ 0` and `0 ≤ f 0` (R18).
- `fun y hy => ?_` on `∃!` shows `hy : (fun x => …) y`; `rw` and `linarith` still see through it, but
  destructuring `fun q ⟨hq, hqfix⟩ => ?_` gives clean hypotheses (R21).
- In `dottie_unique` you may use `cos_contracts` and `sin_one_lt_one`: earlier theorems of the file are
  available by name.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unpack `Set.MapsTo f (Set.Icc a b) t` / `∀ x ∈ Set.Icc a b, …` | `intro x ⟨h0, h1⟩` / `fun x ⟨h0, h1⟩ => …` | R1 |
| prove `y ∈ Set.Icc a b` | `refine ⟨?_, ?_⟩` / `exact ⟨_, _⟩` | R2 |
| `0 ≤ cos x` | `Real.cos_nonneg_of_mem_Icc ⟨_, _⟩` | R3 |
| `cos x ≤ 1` | `Real.cos_le_one x` | R4 |
| linear arithmetic with π | `linarith [Real.pi_pos, Real.pi_gt_three]` | R5 |
| `cos' = −sin`, within a set | `(Real.hasDerivAt_cos t).hasDerivWithinAt` | R6, R7 |
| `[a, b]` is convex | `convex_Icc a b` | R8 |
| mean value bound | `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hC hs hy hx` | R9 |
| `‖-a‖ → ‖a‖`, `‖r‖ → \|r\|`, `\|a\| → a` | `rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg h]` | R10–R12 |
| `0 ≤ sin x` | `Real.sin_nonneg_of_nonneg_of_le_pi h0 hπ` | R13 |
| `sin x ≤ sin y` | `Real.sin_le_sin_of_le_of_le_pi_div_two h₁ h₂ hxy` | R14 |
| close from `h` with norms | `simpa [Real.norm_eq_abs] using h` | R15 |
| `sin x < x` | `Real.sin_lt hx` with `one_pos` | R16, R17 |
| IVT for a decreasing `f` | `obtain ⟨p, hp, hfp⟩ : ∃ p ∈ Set.Icc a b, f p = y := intermediate_value_Icc' hab hf ⟨_, _⟩` | R18 |
| continuity | `fun_prop` | R19 |
| `cos 0` | `simp` (`Real.cos_zero`) | R20 |
| `∃! x, P x` | `refine ⟨a, ha, fun y hy => ?_⟩` | R21 |
| rewrite a hypothesis | `rw [h₁, h₂] at h` | R22 |
| `\|d\| ≤ s * \|d\|`, `s < 1` ⇒ `\|d\| ≤ 0` | `nlinarith [abs_nonneg d, hs]` | R23, R24 |
| `\|a\| ≤ 0 ⇒ a = 0` | `abs_nonpos_iff.mp h` | R25 |
| see the state | infoview | |
