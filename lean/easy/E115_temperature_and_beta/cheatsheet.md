# E115 · Temperature and β: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `Temperature` and inverse
temperature `β`, Boltzmann's constant `kB`, Mathlib's non-negative reals `ℝ≥0` and their cast into `ℝ`,
and the Mathlib tactics `positivity`, `field_simp`, `gcongr`.

The physics: an absolute temperature `T ≥ 0` and Boltzmann's constant `k_B > 0` give the thermal energy
`k_B T` and the inverse temperature `β = 1/(k_B T)`. For `T > 0`, `β > 0` and `β · k_B T = 1`; and since
`x ↦ 1/x` is decreasing on `x > 0`, a hotter body has a smaller `β`. In Lean, every statement about `β`
becomes, after one rewrite (R1), a statement about the real number `1 / (kB * T.toReal)`; the rest is
real-number algebra, which the three tactics R5–R7 do once the positivity facts are in context (R2–R4).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is a goal the step leaves alone.
- Placeholders are written as Lean binders: `(T : Temperature)`, `(a b : ℝ)`. No type classes appear here;
  everything lives in `ℝ` or `ℝ≥0`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (`Real`); `+`, `*`, `/`, `<` on it are the usual ones |
| `ℝ≥0` | Mathlib's `NNReal`: the real numbers `x` with `0 ≤ x`, a structure holding a real and a proof of `0 ≤` it |
| `Temperature` | physlib structure with one field `val : ℝ≥0`, the absolute temperature in some fixed units |
| `T.val` | that field: the temperature as an element of `ℝ≥0` |
| `T.toReal` | the temperature as a real number; by definition `NNReal.toReal T.val`, i.e. `↑T.val` |
| `↑x` (with `x : ℝ≥0`) | the cast `NNReal.toReal x : ℝ`. You write it `(x : ℝ)` |
| `kB` | `Constants.kB : ℝ`, Boltzmann's constant. Its value is never used; only `kB_pos : 0 < kB` (R4) |
| `T.β` | `Temperature.β T : ℝ≥0`, the inverse temperature `1 / (kB * T.toReal)` packaged with its proof of `≥ 0` |
| `↑T.β` | `T.β` cast into `ℝ`, written `(T.β : ℝ)` in the statement |
| `0 < T.val` | `<` in `ℝ≥0`. By definition this is `0 < ↑T.val` in `ℝ` (R2) |
| `1 / (kB * T.toReal)` | real division. Lean's `x / 0 = 0`, so facts like `β · k_B T = 1` need `T.toReal ≠ 0` |
| `case left`, `case right` | labels of the two goals `constructor` makes from `A ∧ B` (`A` first). Not something you type |

---

## Part 1 · `beta_inverse`

Statement: for a temperature `T` with `0 < T.val`, both `0 < (T.β : ℝ)` and
`(T.β : ℝ) * (kB * T.toReal) = 1`. In words: `β > 0` and `β · k_B T = 1`.

### From `β` to a formula in ℝ

**R1 · `rw [Temperature.β_toReal]`** changes the **goal**. The lemma is
`Temperature.β_toReal (T : Temperature) : (T.β : ℝ) = 1 / (kB * T.toReal)` (it holds by `rfl`: it is
the definition of `β`). Placeholders: `(T : Temperature) (P : ℝ → Prop)`. `rw` rewrites every `↑T.β` for
the same `T` at once, so in Part 1 one `rw` handles both conjuncts.

| Before | After |
|---|---|
| `⊢ P ↑T.β` | `⊢ P (1 / (kB * T.toReal))` |

### Putting the positivity facts in context

**R2 · `have h : (0 : ℝ) < T.toReal := hT`** changes the **context**: it adds the real-number version of
`hT : 0 < T.val`. No lemma is needed: `T.toReal` unfolds to `↑T.val`, and `<` on `ℝ≥0` is defined as `<`
of the casts, so the two statements are the same term and `hT` proves both. The named lemma is
`NNReal.coe_pos : 0 < ↑r ↔ 0 < r` (use `NNReal.coe_pos.mpr hT`). Placeholders:
`(T : Temperature) (hT : 0 < T.val) (G : Prop)`. The `(0 : ℝ)` is optional here: `T.toReal : ℝ`
already fixes the type, so a bare `0 < T.toReal` means the same.

| Before | After |
|---|---|
| `hT : 0 < T.val ⊢ G` | `h : 0 < T.toReal ⊢ G` |

**R3 · `have h : T₁.toReal < T₂.toReal := hlt`** changes the **context**: the same move for `<` between
two temperatures. The named lemma is `NNReal.coe_lt_coe : ↑r₁ < ↑r₂ ↔ r₁ < r₂`. Placeholders:
`(T₁ T₂ : Temperature) (hlt : T₁.val < T₂.val) (G : Prop)`. Used in Part 2 only.

| Before | After |
|---|---|
| `hlt : T₁.val < T₂.val ⊢ G` | `h : T₁.toReal < T₂.toReal ⊢ G` |

**R4 · `have hk := kB_pos`** changes the **context**. The lemma is `Constants.kB_pos : 0 < kB`; with
`open Constants` the short name works. `have hk := e` takes its type from `e`. Placeholders: `(G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hk : 0 < kB ⊢ G` |

### Closing the two conjuncts

Split `A ∧ B` with `constructor` (TACTIC_STATES, "Structure"), then one tactic per goal.

**R5 · `positivity`** **closes** a goal `0 < e`, `0 ≤ e` or `e ≠ 0` where `e` is built from `*`, `/`, `+`,
`^`, numerals and atoms. For an atom (a variable, `kB`, `T.toReal`) it looks for `0 < atom` among the
hypotheses; it does not search for lemmas. Placeholders: `(a b : ℝ) (ha : 0 < a) (hb : 0 < b)`; in the
exercise `a = kB`, `b = T.toReal`.

| Before | After |
|---|---|
| `ha : 0 < a, hb : 0 < b ⊢ 0 < 1 / (a * b)` | no goals |

**R6 · `field_simp`** changes the **goal** by multiplying out every denominator it can prove nonzero,
then simplifying; on a goal like `1 / a * a = 1` nothing is left and it **closes** it. It proves `a ≠ 0`
from a hypothesis `a ≠ 0` or `0 < a` in context. In the exercise the denominator is `kB * T.toReal`, so it
needs both `hk` and the ℝ version of `hT`. Placeholders: `(a : ℝ) (ha : 0 < a)`.

| Before | After |
|---|---|
| `ha : 0 < a ⊢ 1 / a * a = 1` | no goals |

---

## Part 2 · `beta_antitone`

Statement: for temperatures `T₁ T₂` with `0 < T₁.val` and `T₁.val < T₂.val`, `(T₂.β : ℝ) < T₁.β`. In words:
hotter means smaller `β`. After R1 twice (once per temperature, see W1) the goal is
`1 / (kB * T₂.toReal) < 1 / (kB * T₁.toReal)`; R2, R3, R4 supply `0 < T₁.toReal`, `T₁.toReal < T₂.toReal`,
`0 < kB`, and R7 closes it.

**R7 · `gcongr`** ("generalized congruence") **closes** an inequality between two expressions of the same
shape that differ in some places, by monotonicity. For `1 / y < 1 / x` it uses that `t ↦ 1 / t` is
decreasing on `t > 0`: the **main goal** is `x < y` (the differing parts, here in reverse order because
`1 / ·` is decreasing) and the **side goal** is `0 < x`. It closes main goals that are hypotheses and side
goals with `positivity` (R5); whatever it cannot close is left as a new goal (W3). On
`1 / (kB * b) < 1 / (kB * a)` it goes one level further: `kB * a < kB * b` needs `a < b` and `0 < kB`
(W2). Placeholders: `(x y : ℝ) (hx : 0 < x) (hxy : x < y)`.

| Before | After |
|---|---|
| `hx : 0 < x, hxy : x < y ⊢ 1 / y < 1 / x` | no goals |

### Worked combinations (W1–W3, on statements that are not the exercise's)

**W1: two temperatures, two rewrites.** `rw [Temperature.β_toReal]` picks `T` from the first `↑·.β` it
finds and rewrites only that temperature's `β`; the second `rw` rewrites the other one. (Or write
`rw [Temperature.β_toReal, Temperature.β_toReal]`.) The states:

```lean-goal
⊢ P (↑T₁.β + ↑T₂.β)
⊢ P (1 / (kB * T₁.toReal) + ↑T₂.β)
⊢ P (1 / (kB * T₁.toReal) + 1 / (kB * T₂.toReal))
```

**W2: hotter means larger thermal energy.** From `hlt : T₁.val < T₂.val`, R3 and R4 put
`h : T₁.toReal < T₂.toReal` and `hk : 0 < kB` in context, then `gcongr` closes:

```lean-goal
⊢ kB * T₁.toReal < kB * T₂.toReal
```

**W3: what `gcongr` leaves when the facts are not hypotheses of their own.** With only
`h : 0 < x ∧ x < y`, `gcongr` on the first goal leaves its side goal and its main goal, closed by
`exacts [h.1, h.2]`:

```lean-goal
⊢ 1 / y < 1 / x
⊢ 0 < x
⊢ x < y
```

---

## Traps

- `positivity`, `field_simp` and `gcongr` only see facts that are hypotheses in context, stated about the
  exact terms in the goal. `hT : 0 < T.val` is about `ℝ≥0`; the goal mentions `T.toReal`. State
  `0 < T.toReal` (R2) and `0 < kB` (R4) with `have` first (W3 shows what happens otherwise).
- With only `hb : 0 < b` in context (no fact about `a`), `field_simp` on `1 / (a * b) * (a * b) = 1`
  cancels `b` but not `a` and leaves `a / a = 1`, which is false for `a = 0` (Lean's `x / 0 = 0`).
- In Part 2 the hypothesis to transfer is `T₁.val < T₂.val` (R3), and positivity is needed only for the
  smaller temperature `T₁`.
- `Temperature.beta_pos` is banned: prove `0 < β` from the formula.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `↑T.β` → `1 / (kB * T.toReal)` | `rw [Temperature.β_toReal]` | R1 |
| two temperatures | `rw [Temperature.β_toReal, Temperature.β_toReal]` | R1, W1 |
| `0 < T.val` (ℝ≥0) → `0 < T.toReal` (ℝ) | `have h : (0 : ℝ) < T.toReal := hT` | R2 |
| `T₁.val < T₂.val` → `T₁.toReal < T₂.toReal` | `have h : T₁.toReal < T₂.toReal := hlt` | R3 |
| `0 < kB` in context | `have hk := kB_pos` | R4 |
| split `A ∧ B` | `constructor` | TACTIC_STATES |
| `0 < 1 / (a * b)` | `positivity` | R5 |
| `1 / a * a = 1` (`a ≠ 0` known) | `field_simp` | R6 |
| `1 / y < 1 / x` from `x < y`, `0 < x` | `gcongr` | R7 |
| see the state | infoview | |
