# M109 · One Babylonian step: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, the square root
`Real.sqrt`, and the arithmetic automation `field_simp`, `positivity`, `linarith`, `nlinarith`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal that a step leaves alone.
- Placeholders are written as Lean binders, e.g. `(a b c : ℝ)`; a hypothesis such as `(hc : 0 < c)` is one
  the step needs.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- "closed" in an After cell means the tactic proves the goal outright (no goal is left).

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers |
| `√a` | `Real.sqrt a`, the nonnegative square root. Lean makes it total: for `a < 0` it is `0`, so facts about `√a` need `0 ≤ a` |
| `a / x` | real division. Lean makes it total too: `a / 0 = 0`, so facts about `/` need `x ≠ 0` or `0 < x` |
| `x ^ 2` | `x` to the natural-number power `2` (the `2` is a `ℕ`) |
| `√a ^ 2` | `(√a) ^ 2`: `√` binds tighter than `^`, so this is the square of the root, not `√(a ^ 2)` |
| `(x - √a) ^ 2 / (2 * x)` | `((x - √a) ^ 2) / (2 * x)`: `^` binds tighter than `/` and `*` |
| `x * 2 * √a` | `(x * 2) * √a`: `*` groups to the left |
| `noncomputable def` | a definition Lean cannot run as a program (real division is not computable); you can still unfold it and prove things about it |
| `babylon a x` | the step `(x + a / x) / 2`, until you `unfold babylon` (R1) |
| `this : T` | a fact added by `have : T := …` without a name; refer to it as `this` |
| `b / c ≤ a ↔ b ≤ a * c` | "if and only if"; `rw` with an `↔` lemma replaces one side by the other in the goal |

---

## Part 1 · `babylon_error`

Statement: for `a ≥ 0` and `x > 0`, `babylon a x - √a = (x - √a) ^ 2 / (2 * x)`. Writing `e = x - √a` for the
old error, the new error is `e² / (2x)`: quadratic in `e`. Proof shape: unfold the step, record
`√a ^ 2 = a`, clear the denominators, and close a polynomial identity that holds once `√a ^ 2` is read as `a`.

**R1 · `unfold f`** changes the **goal**: every `f u v` becomes the body of `f`. Placeholders: a definition
`noncomputable def mid (u v : ℝ) : ℝ := (u + v) / 2`, `(u v : ℝ)`. `simp only [f]` does the same.

| Before | After |
|---|---|
| `⊢ P (mid u v)` | `⊢ P ((u + v) / 2)` |

**R2 · `Real.sq_sqrt`** changes the **context**. The lemma is `Real.sq_sqrt : 0 ≤ b → √b ^ 2 = b`; applied to
`hb : 0 ≤ b` it is a proof of `√b ^ 2 = b`, and `have hs := Real.sq_sqrt hb` adds it. Placeholders:
`(b : ℝ) (hb : 0 ≤ b)`. This is the only thing you need to know about `√b` for the identity: from here on,
`√b` is an unknown `s` with `s ^ 2 = b`.

| Before | After |
|---|---|
| `⊢ G` | `hs : √b ^ 2 = b ⊢ G` |

**R3 · `field_simp`** changes the **goal**: an equation between fractions becomes an equation without
denominators (both sides multiplied out, common nonzero factors cancelled). It must prove every denominator
`≠ 0`; it finds `hw : 0 < w` (or `w ≠ 0`) in the context by itself, and numerals such as `2` are automatic.
Placeholders: `(u v w : ℝ) (hw : 0 < w)`. The exact arrangement of the result (which side, factor order) is
`field_simp`'s choice: read it off the infoview, do not predict it.

| Before | After |
|---|---|
| `hw : 0 < w ⊢ u + v / w = 3` | `⊢ u * w + v = w * 3` |

In `babylon_error`, after R1 and R2, `field_simp` leaves an equation between two polynomials in `x`, `a` and
`√a`, with no `/` left.

**R4 · `nlinarith [t₁, t₂]`** **closes** a polynomial equation or inequality over `ℝ`. It is `linarith` (R6)
that first also multiplies pairs of hypotheses and hint terms `tᵢ` together, so it can use facts like
`s ^ 2 = b` inside products. An equation is proved as two inequalities `≤`, `≥`. Pass the facts it needs
as hints. Placeholders: `(s b : ℝ) (hs : s ^ 2 = b)`, and for the inequality `(s y : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ y)`.

| Before | After |
|---|---|
| `hs : s ^ 2 = b ⊢ (1 + s) ^ 2 = 1 + 2 * s + b` | closed by `nlinarith [hs]` |
| `h0 : 0 ≤ s, h1 : s ≤ y ⊢ s * s ≤ y * y` | closed by `nlinarith [h0, h1]` |

If it fails, it says `linarith failed to find a contradiction`: give it the missing product or fact as a hint.

**W1.** `1 / y - 1 / (y + 1) = 1 / (y * (y + 1))` with `hy : 0 < y`: `field_simp` (R3) leaves a polynomial
identity, and `ring` closes it.

```lean-goal
⊢ 1 / y - 1 / (y + 1) = 1 / (y * (y + 1))
⊢ y + 1 - y = 1
```

**W2.** `(√3 - 1) ^ 2 = 4 - 2 * √3`: `ring` alone fails (it does not know `√3 ^ 2 = 3`). Add the fact with R2,
`have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)`, then `nlinarith [hs]` (R4).

```lean-goal
⊢ (√3 - 1) ^ 2 = 4 - 2 * √3
```

---

## Part 2 · `sqrt_le_babylon`

Statement: for `a ≥ 0` and `x > 0`, `√a ≤ babylon a x`: one step from any positive start lands at or above
`√a`. Proof shape: Part 1 says the difference `babylon a x - √a` equals a square over a positive number,
which is `≥ 0`. Bring Part 1 in with `have he := babylon_error a x ha hx` (a theorem applied to its
arguments is a proof, TACTIC_STATES "Adding facts"); you do not need to unfold `babylon` here.

**R5 · `positivity`** **closes** a goal `0 ≤ e` or `0 < e` when `e` is built from pieces whose sign it can see:
even powers and squares are `≥ 0`, sums/products/quotients of nonnegatives are `≥ 0`, and a variable is
`> 0` if the context says so. Placeholders: `(u t : ℝ) (ht : 0 < t)`. It never proves `e ≤ f` for two
nonconstant sides: state the fact as `0 ≤ …` in a `have`.

| Before | After |
|---|---|
| `ht : 0 < t ⊢ 0 ≤ (u + t) ^ 2 / (5 * t)` | closed |

**R6 · `linarith`** **closes** a goal `t ≤ u`, `t < u`, `t = u` (or `False`) that follows from the context
by adding up hypotheses with nonnegative coefficients. Any nonlinear piece, such as `p / q`, `e ^ 2 / (2 * x)`,
or `babylon a x`, is one opaque unknown: two occurrences must be literally the same term. Placeholders:
`(p q r : ℝ)`.

| Before | After |
|---|---|
| `h1 : p - q = r, h2 : 0 ≤ r ⊢ q ≤ p` | closed |

**W3.** From `hE : E - s = (y - s) ^ 4 / y` and `hy : 0 < y`, prove `s ≤ E`: add
`have hq : 0 ≤ (y - s) ^ 4 / y := by positivity` (R5), then `linarith` (R6) treats the quotient as one unknown.

```lean-goal
⊢ s ≤ E
```

---

## Part 3 · `babylon_le`

Statement: for `a ≥ 0`, `x > 0` and `√a ≤ x`, `babylon a x ≤ x`: once at or above `√a`, a step does not go up.
Proof shape: `(x + a / x) / 2 ≤ x` is linear in the unknown `a / x` and follows from `a / x ≤ x`. Prove that
as a `have`: clear the denominator (R7) to get `a ≤ x * x`, then `a = √a ^ 2 ≤ x * x` because
`0 ≤ √a ≤ x` (R8, R2, R4). Finish with `linarith` (R6). This uses R1 again to unfold `babylon`.

**R7 · `rw [div_le_iff₀ hc]`** changes the **goal**. The lemma is `div_le_iff₀ (hc : 0 < c) : b / c ≤ a ↔ b ≤ a * c`
(the `₀` is part of the name: plain `div_le_iff` does not exist in this Mathlib). Placeholders: `(a b c : ℝ) (hc : 0 < c)`;
it holds in any ordered field, `ℝ` and `ℚ` included. Note the product is `a * c`, not `c * a`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ b / c ≤ a` | `⊢ b ≤ a * c` |

**R8 · `Real.sqrt_nonneg`** changes the **context**. The lemma is `Real.sqrt_nonneg (b : ℝ) : 0 ≤ √b`, for
every `b`, with no hypothesis. Use `have hn := Real.sqrt_nonneg b`, or pass `Real.sqrt_nonneg b` straight
to `nlinarith` as a hint. Placeholders: `(b : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hn : 0 ≤ √b ⊢ G` |

**W4.** `1 / y ≤ y` from `hy : 0 < y` and `h1 : 1 ≤ y`: R7, then `nlinarith [h1]` (R4) multiplies `1 ≤ y`
by itself.

```lean-goal
⊢ 1 / y ≤ y
⊢ 1 ≤ y * y
```

---

## Traps

- `grind` (and `try?`, which would suggest it) closes the error identity once `babylon` is unfolded. Both are
  BANNED: do the algebra with R1–R4.
- `√a` and `a / x` are total functions in Lean (`√(-1) = 0`, `a / 0 = 0`), so every fact about them carries a
  hypothesis: `Real.sq_sqrt` needs `0 ≤ a` (R2), `field_simp` and `div_le_iff₀` need `0 < x` (R3, R7).
- `field_simp` with no `0 < x` or `x ≠ 0` in the context leaves the goal with its `/ x` unchanged. Keep `hx` around (do not
  `clear` it) or add `have hx' : x ≠ 0 := hx.ne'`.
- `ring` does not use hypotheses, so it cannot use `√a ^ 2 = a`; that is why the identity ends with
  `nlinarith [hs]` (R4), not `ring`.
- `linarith` is linear: from `√a ≤ x` alone it cannot get `a ≤ x * x`. That needs `nlinarith` with
  `0 ≤ √a` and `√a ^ 2 = a` as hints (R8, R2, R4).
- In `babylon_le`, unfold first (R1). With `babylon a x` still folded, `linarith` sees it as one opaque unknown,
  unrelated to `a / x`, and fails even with `a / x ≤ x` in the context. (`sqrt_le_babylon` needs no unfolding: there
  `he` and the goal mention the same folded term.)
- `positivity` proves only `0 ≤ e` / `0 < e`. State the sign fact in that form, then let `linarith` combine it.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| replace `babylon a x` by its body | `unfold babylon` | R1 |
| `√a ^ 2 = a` as a fact | `have hs := Real.sq_sqrt ha` | R2 |
| `0 ≤ √a` as a fact or hint | `Real.sqrt_nonneg a` | R8 |
| use an earlier theorem | `have he := thm args` | TACTIC_STATES |
| equation with `/ x` → without | `field_simp` (needs `0 < x` in context) | R3 |
| polynomial (in)equality using square facts | `nlinarith [hs, …]` | R4 |
| `0 ≤ square / positive` | `positivity` | R5 |
| combine linear facts | `linarith` | R6 |
| `b / c ≤ a` → `b ≤ a * c` | `rw [div_le_iff₀ hc]` | R7 |
| polynomial identity, no hypotheses | `ring` | TACTIC_STATES |
| see the state | infoview | |
