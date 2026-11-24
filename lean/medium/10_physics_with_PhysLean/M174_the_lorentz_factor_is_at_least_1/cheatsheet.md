# M174 · The Lorentz factor is at least 1: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ` with `|·|`, `√` and
`/`, the arithmetic tactic `nlinarith`, and using an `↔` lemma with `.mp`, `.mpr` and `rw`; physlib's Lorentz
group `LorentzGroup d`, the boost `boost i β hβ`, its Lorentz factor `γ`, and the lemma naming its time-time
entry.

**The physics (units with c = 1).** Spacetime has one time and `d` space coordinates; a Lorentz
transformation is a real `(1 + d) × (1 + d)` matrix `Λ`, rows and columns indexed by `Fin 1 ⊕ Fin d` (time,
or one of the `d` space axes). The boost along axis `i` with speed `β` (a fraction of `c`, `|β| < 1`) has
time-time entry

$$\Lambda^0{}_0 = \gamma(\beta) = \frac{1}{\sqrt{1 - \beta^2}}.$$

Since $0 \le \beta^2 < 1$, the radicand $1 - \beta^2$ lies in $(0, 1]$, so $\sqrt{1 - \beta^2} \in (0, 1]$ and
its reciprocal is $\ge 1$. Physically: a moving clock is never seen to run fast.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. A bare `P : Prop` with `k : … → P` is any goal you will finish with the new fact.
- Placeholders are written as Lean binders. `{d : ℕ}` is implicit: Lean infers it. Every entry here is over
  `ℝ`; the lemmas themselves hold more generally (each entry says for which types).
- `|` cannot appear literally inside a table, so `|a|` is written `\|a\|` there.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers |
| `\|β\|` | absolute value of `β : ℝ` (Mathlib's `abs`) |
| `√x` | `Real.sqrt x`, the non-negative square root; it is `0` for `x < 0` |
| `a / b` | real division; Mathlib defines `a / 0 = 0`, so facts about `/` need `0 < b` or `b ≠ 0` |
| `β ^ 2` | `β` squared (`^` with a natural-number exponent) |
| `Fin 1 ⊕ Fin d` | the index type "time or one of `d` space axes"; `⊕` is the sum (disjoint union) type |
| `Sum.inl 0`, `Sum.inr k` | the time index, and space axis `k : Fin d` |
| `LorentzGroup d`, printed `↑(𝓛 d)` | the Lorentz group: `𝓛 d` is physlib's notation for the set of real matrices on `Fin 1 ⊕ Fin d` preserving the Minkowski metric; `↑` turns that set into a type (a subtype), whose elements are a matrix plus a proof it lies in the set |
| `↑Λ`, written `Λ.1` | the matrix underlying `Λ : LorentzGroup d` (the coercion out of the subtype) |
| `↑Λ r c` | entry in row `r`, column `c` of that matrix |
| `boost i β hβ` | the boost along axis `i : Fin d` with speed `β`; `hβ : \|β\| < 1` is a proof that `β` is allowed |
| `γ β` | physlib's `LorentzGroup.γ β = 1 / √(1 - β ^ 2)`, the Lorentz factor (R2) |
| `h.mp`, `h.mpr` | for `h : A ↔ B`: `h.mp : A → B` and `h.mpr : B → A` |

---

## Part 1 · `one_le_gamma`

Statement: for every axis `i : Fin d`, speed `β : ℝ` and proof `hβ : |β| < 1`,
`1 ≤ (boost i β hβ).1 (Sum.inl 0) (Sum.inl 0)`, i.e. $1 \le \gamma(\beta)$. Plan: name the entry as `γ β`
(R1), unfold `γ` (R2), prove `0 < 1 - β ^ 2` (R3, R5), turn `1 ≤ 1 / s` into `s ≤ 1` (R6, R7), and finish
`√(1 - β ^ 2) ≤ 1` (R8, R4, R5).

### From the matrix entry to a real number

**R1 · `rw [boost_inl_0_inl_0]`** changes the **goal**. The lemma is
`LorentzGroup.boost_inl_0_inl_0 (i : Fin d) {β : ℝ} (hβ : |β| < 1) : ↑(boost i β hβ) (Sum.inl 0) (Sum.inl 0) = γ β`:
the time-time entry of a boost is the Lorentz factor. It is a `@[simp]` lemma, so `simp` also uses it.
Placeholders: `{d : ℕ} (i : Fin d) (β : ℝ) (hβ : |β| < 1)`.

| Before | After |
|---|---|
| `⊢ P (↑(boost i β hβ) (Sum.inl 0) (Sum.inl 0))` | `⊢ P (γ β)` |

**R2 · `unfold γ`** changes the **goal**: `γ β` becomes its definition. Placeholders: `(β : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (γ β)` | `⊢ P (1 / √(1 - β ^ 2))` |

### Facts about `β`

**R3 · `abs_lt.mp`** changes the **context** (with `have`). The lemma is `abs_lt : |a| < b ↔ -b < a ∧ a < b`, and
`.mp` uses it left to right, so `abs_lt.mp hab` is a proof of `-b < a ∧ a < b`. Placeholders: `(a b : ℝ)`
(any linearly ordered additive group: `ℤ`, `ℚ`, `ℝ`). You can also pass `abs_lt.mp hβ` straight to
`nlinarith [...]` (R5) without a `have`.

| Before | After |
|---|---|
| `hab : \|a\| < b`, `⊢ P` | `h : -b < a ∧ a < b ⊢ P` |

**R4 · `sq_nonneg a`** changes the **context** (with `have`). The lemma is `sq_nonneg (a : R) : 0 ≤ a ^ 2`.
`nlinarith` may not find this by itself; give it as a hint, `nlinarith [sq_nonneg a]`. Placeholders:
`(a : ℝ)` (any ordered semiring: `ℕ`, `ℤ`, `ℚ`, `ℝ`).

| Before | After |
|---|---|
| `⊢ P` | `h : 0 ≤ a ^ 2 ⊢ P` |

**R5 · `nlinarith [t₁, t₂]`** **closes** a goal `<`, `≤`, `=` (or `False`) between polynomial expressions over
an ordered field such as `ℝ`. The terms `tᵢ` are extra facts. It splits `∧` facts, multiplies pairs of facts and
hypotheses (here `(2 + a) * (2 - a) > 0`), then finds a linear combination. It treats `√x` and `a / b` as
opaque atoms and knows no facts about them, so remove them from the goal first (R7, R8). Placeholders: `(a : ℝ) (hab : -2 < a ∧ a < 2)`.

| Before | After |
|---|---|
| `⊢ 0 < 4 - a ^ 2` | `∅` |

### Square roots and `1 ≤ a / b`

**R6 · `Real.sqrt_pos.mpr`** changes the **context** (with `have`). The lemma is `Real.sqrt_pos : 0 < √x ↔ 0 < x`,
and `.mpr` uses it right to left: `Real.sqrt_pos.mpr hx : 0 < √x` for `hx : 0 < x`. Usually written inline as
the premise of R7. Placeholders: `(x : ℝ) (hx : 0 < x)`.

| Before | After |
|---|---|
| `hx : 0 < x ⊢ P` | `h : 0 < √x ⊢ P` |

**R7 · `rw [one_le_div hb]`** changes the **goal**. The lemma is `one_le_div (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a`; `rw`
with an `↔` replaces the proposition `1 ≤ a / b` by `b ≤ a`. Without `hb` the lemma cannot be used: it is false
for `b = 0`, where `a / 0 = 0`. Placeholders: `(a b : ℝ) (hb : 0 < b)` (any ordered field: `ℚ`, `ℝ`).

| Before | After |
|---|---|
| `⊢ 1 ≤ a / b` | `⊢ b ≤ a` |

**R8 · `apply Real.sqrt_le_one.mpr`** changes the **goal**. The lemma is `Real.sqrt_le_one : √x ≤ 1 ↔ x ≤ 1`;
`apply` with its `.mpr : x ≤ 1 → √x ≤ 1` leaves the premise as the new goal. Equivalently,
`exact Real.sqrt_le_one.mpr (by …)`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ √x ≤ 1` | `⊢ x ≤ 1` |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: a strict bound from `|a| < 3`.** R3 as a hint inside R5: `nlinarith [abs_lt.mp ha]` closes

```lean-goal
⊢ 0 < 9 - a ^ 2
```

**W2: `1 ≤ 1 / √(x / 2)` for `0 < x ≤ 2`.** `have hpos : 0 < x / 2` (by `linarith`), then R6 inside R7, then
R8, then `linarith` (it handles division by a numeral):

```lean-goal
⊢ 1 ≤ 1 / √(x / 2)
⊢ √(x / 2) ≤ 1
⊢ x / 2 ≤ 1
```

---

## Traps

- `nlinarith` and `linarith` treat `√x` and `a / b` as opaque atoms. Rewrite them away (R7, R8) before calling
  arithmetic, and prove the radicand facts on `1 - β ^ 2` itself.
- `0 < 1 - β ^ 2` needs **both** bounds `-1 < β` and `β < 1` (their product): pass the whole pair
  `abs_lt.mp hβ` to `nlinarith`, not only one half.
- `rw [one_le_div]` with no argument leaves a side goal `0 < √(1 - β ^ 2)` for later; give the positivity
  proof on the spot instead: `rw [one_le_div (Real.sqrt_pos.mpr h1)]`.
- `.mp` goes left to right of an `↔`, `.mpr` right to left. `Real.sqrt_pos.mp` would need `0 < √x` as input.
- `boost i β hβ` is an element of `LorentzGroup d`, not a matrix; `.1` (printed `↑`) takes its matrix. `rw [R1]`
  only matches the `.1 (Sum.inl 0) (Sum.inl 0)` form.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| time-time boost entry → `γ β` | `rw [boost_inl_0_inl_0]` (or `simp`) | R1 |
| `γ β` → `1 / √(1 - β ^ 2)` | `unfold γ` | R2 |
| `\|a\| < b` → `-b < a ∧ a < b` | `abs_lt.mp h` | R3 |
| `0 ≤ a ^ 2` as a hint | `sq_nonneg a` | R4 |
| polynomial inequality | `nlinarith [facts]` | R5 |
| `0 < x` → `0 < √x` | `Real.sqrt_pos.mpr h` | R6 |
| `1 ≤ a / b` → `b ≤ a` (with `0 < b`) | `rw [one_le_div hb]` | R7 |
| `√x ≤ 1` → `x ≤ 1` | `apply Real.sqrt_le_one.mpr` | R8 |
| add a fact | `have h : T := by …` | TACTIC_STATES |
| see the state | infoview | |
