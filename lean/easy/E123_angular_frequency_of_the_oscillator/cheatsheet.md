# E123 · Angular frequency of the oscillator: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), structures and their fields (E017). **New here:**
physlib's `ClassicalMechanics.HarmonicOscillator` and its angular frequency `ω`, Mathlib's real numbers
`ℝ`, square root `√`, and the Mathlib tactic `field_simp`.

The physics: a mass `m > 0` on a spring of constant `k > 0` obeys `m ẍ = -k x`, which oscillates at the
angular frequency `ω = √(k/m)`. Squaring gives `ω² = k/m`, so `m ω² = k`. In Lean, one rewrite (R1)
replaces `S.ω ^ 2` by `S.k / S.m`; what is left, `S.m * (S.k / S.m) = S.k`, is true only because
`S.m ≠ 0` (R2), and `field_simp` (R3) or `mul_div_cancel₀` (R4) uses that fact to cancel.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. `G : Prop` is a goal the step leaves alone.
- Placeholders are written as Lean binders. `{K : Type}` is any type. A bracket such as `[Field K]` is a
  requirement on `K` (a *type class*); each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `HarmonicOscillator` | `ClassicalMechanics.HarmonicOscillator` (the file says `open ClassicalMechanics`): a physlib structure with fields `m k : ℝ`, `m_pos : 0 < m`, `k_pos : 0 < k` |
| `ℝ` | Mathlib's real numbers (`Real`) |
| `S.m`, `S.k` | the mass and the spring constant of `S`, real numbers |
| `S.m_pos`, `S.k_pos` | the proof fields: `S.m_pos : 0 < S.m`, `S.k_pos : 0 < S.k` |
| `S.m_ne_zero`, `S.k_ne_zero` | physlib lemmas `S.m ≠ 0`, `S.k ≠ 0`, derived from the proof fields (R2) |
| `S.ω` | `HarmonicOscillator.ω S : ℝ`, defined as `√(S.k / S.m)`. Lean prints it `S.ω`, never unfolded |
| `√x` | `Real.sqrt x`, the real square root (and `0` for `x < 0`) |
| `S.ω ^ 2` | `S.ω` squared; the exponent `2 : ℕ` is a natural number |
| `a / b` | real division. Lean's `x / 0 = 0`, so `b * (a / b) = a` needs `b ≠ 0` |

---

## Part 1 · `m_mul_omega_sq`

Statement: for every oscillator `S`, `S.m * S.ω ^ 2 = S.k`. In words: `m ω² = k`.

### From `ω ^ 2` to the data `k` and `m`

**R1 · `rw [HarmonicOscillator.ω_sq]`** changes the **goal**. The lemma is
`HarmonicOscillator.ω_sq (S : HarmonicOscillator) : S.ω ^ 2 = S.k / S.m` (physlib proves it from the
definition of `ω` and `Real.sq_sqrt`, using `0 ≤ k/m`). `rw` needs `S.ω ^ 2` to appear literally: `S.ω * S.ω`
would not match. Placeholders: `(S : HarmonicOscillator) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (S.ω ^ 2)` | `⊢ P (S.k / S.m)` |

**R2 · `have hm := S.m_ne_zero`** changes the **context**. The lemma is
`HarmonicOscillator.m_ne_zero (S : HarmonicOscillator) : S.m ≠ 0`, proved from the field `S.m_pos`.
Dot notation `S.m_ne_zero` finds it because `S : HarmonicOscillator`. `have hm := e` takes its type from
`e`. You can also skip the `have` and hand the fact straight to R3 or R4. Placeholders:
`(S : HarmonicOscillator) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hm : S.m ≠ 0 ⊢ G` |

### Cancelling the mass

**R3 · `field_simp [hb]`** changes the **goal** by multiplying out every denominator it can prove
nonzero, then simplifying; on `b * (a / b) = a` nothing is left and it **closes** the goal. It proves
`b ≠ 0` from the facts in brackets, from hypotheses in context, and from `@[simp]` lemmas
(`m_ne_zero` is one, so here a bare `field_simp` also works; naming the fact is the robust habit).
Placeholders: `{K : Type} [Field K] (a b : K) (hb : b ≠ 0)`; `[Field K]` means `+ - * /` with the usual
laws, met by `ℝ`, `ℚ`, `ℂ`.

| Before | After |
|---|---|
| `hb : b ≠ 0 ⊢ b * (a / b) = a` | no goals |

**R4 · `exact mul_div_cancel₀ a hb`** **closes** the same goal with one named lemma instead of a tactic.
The lemma is `mul_div_cancel₀ (a : G₀) (h : b ≠ 0) : b * (a / b) = a` (`b` implicit, found from the
goal). It must match the goal's shape exactly: `b * (a / b)`, not `(a / b) * b`. Write `_` for `a` to let
Lean find it too. Placeholders: `{G₀ : Type} [CommGroupWithZero G₀] (a b : G₀) (hb : b ≠ 0)`;
`[CommGroupWithZero G₀]` means commutative `*` with inverses of nonzero elements, met by `ℝ`, `ℚ`, `ℂ`.

| Before | After |
|---|---|
| `hb : b ≠ 0 ⊢ b * (a / b) = a` | no goals |

### Worked combinations (W1–W2, on statements that are not the exercise's)

**W1: unfolding `ω` leaves a square root.** `unfold HarmonicOscillator.ω` replaces `S.ω` by its
definition. Squaring that by hand needs `Real.sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x` and a proof of
`0 ≤ S.k / S.m`; R1 has done this already, so prefer R1.

```lean-goal
⊢ P S.ω
⊢ P √(S.k / S.m)
```

**W2: another oscillator, an LC circuit.** Inductance `L`, capacitance `C` (both `≠ 0`), angular
frequency `w` with `hw : w ^ 2 = 1 / (L * C)`; show `L * C * w ^ 2 = 1`. `rw [hw]` plays the role of
R1, then R3 with both nonzero facts (`field_simp [hL, hC]`), since the denominator is the product `L * C`:

```lean-goal
⊢ L * C * w ^ 2 = 1
⊢ L * C * (1 / (L * C)) = 1
```

---

## Traps

- `HarmonicOscillator` here is `ClassicalMechanics.HarmonicOscillator`, available unqualified because of
  `open ClassicalMechanics`. Its lemmas are `HarmonicOscillator.ω_sq`, `HarmonicOscillator.m_ne_zero`
  (or `S.m_ne_zero` by dot notation).
- Do not unfold `ω` (W1): you would have to redo physlib's proof of `ω_sq`.
- `S.m * (S.k / S.m) = S.k` is not a ring identity (`ring` fails: it knows nothing about `S.m ≠ 0`, and
  Lean's `x / 0 = 0` makes the statement false for `m = 0`). Cancel with R3 or R4.
- `S.m_pos : 0 < S.m` is not literally `S.m ≠ 0`; `mul_div_cancel₀` needs the `≠` form (`S.m_ne_zero`, or
  `S.m_pos.ne'`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `S.ω ^ 2` → `S.k / S.m` | `rw [HarmonicOscillator.ω_sq]` | R1 |
| `S.m ≠ 0` in context | `have hm := S.m_ne_zero` | R2 |
| `0 < S.m` | `S.m_pos` (structure field) | R2 |
| `b * (a / b) = a` (`b ≠ 0` known) | `field_simp [hb]` | R3 |
| the same as one lemma | `exact mul_div_cancel₀ _ hb` | R4 |
| a denominator `a * b` (`ha : a ≠ 0`, `hb : b ≠ 0`) | `field_simp [ha, hb]` | R3, W2 |
| see the state | infoview | |
