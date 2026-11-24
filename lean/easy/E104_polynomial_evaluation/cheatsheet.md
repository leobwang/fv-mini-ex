# E104 · Polynomial evaluation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's polynomials `R[X]`: the
variable `X`, constant polynomials `C a`, evaluation `p.eval x`, the `eval_*` rewrite lemmas, and roots
`p.IsRoot r`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : R → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. R7 uses a two-argument `P : R → R → Prop` to show two lemmas side by side.
- Placeholders are written as Lean binders. `{R : Type} [CommRing R]` is any type `R` with `+`, `-`, `*`,
  `0`, `1` obeying the commutative-ring laws (a *type class* requirement); `ℝ`, `ℚ`, `ℤ` meet it.
  `(p q : R[X])` are polynomials over `R`, `(x a r : R)` are elements of `R`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

A polynomial in Mathlib is a formal object (a finite list of coefficients), not a function. `eval`
turns it into a number by substituting a point for `X`. All three parts reduce to: push `eval` inside
with R1–R7, then do arithmetic on numbers.

| You see | It means |
|---|---|
| `ℝ[X]`, `R[X]` | `Polynomial ℝ`: polynomials with real (resp. `R`) coefficients. Notation from `open Polynomial` |
| `X` | `Polynomial.X`, the variable, a polynomial itself |
| `C a` | `Polynomial.C a`, the constant polynomial with value `a : R` (`C` is the inclusion `R → R[X]`) |
| `2 * X`, `1` inside `R[X]` | numerals typed as polynomials: the constants `2`, `1`. Equal to `C 2`, `C 1`, but written differently, so `eval_C` does not rewrite them (R7 does) |
| `p.eval x` | `Polynomial.eval x p`, the value of `p` at `x`, an element of `R` |
| `eval x p` | how the infoview prints `p.eval x`: **the point comes first** |
| `p.IsRoot r` | `Polynomial.IsRoot p r`, defined as `eval r p = 0` |
| `eval 3 2` | the constant polynomial `2` evaluated at `3`: still to be rewritten by R7 |

---

## Part 1 · `eval_quadratic`

Statement: the polynomial $X^2 - 2X + 1$ evaluated at $3$ is $4$. Push `eval` through `+`, `-`, `^`, `*`
(R1–R4), replace `X` by the point (R5) and numeral polynomials by numerals (R7), then compute (R8).
`norm_num` does all of it in one call (W2).

**R1 · `eval_add`** changes the **goal**. Lemma: `eval x (p + q) = eval x p + eval x q`. Placeholders:
`{R : Type} [CommRing R] (p q : R[X]) (x : R)`.

| Before | After |
|---|---|
| `⊢ P (eval x (p + q))` | `⊢ P (eval x p + eval x q)` |

**R2 · `eval_sub`** changes the **goal**. Lemma: `eval x (p - q) = eval x p - eval x q`. Same placeholders.

| Before | After |
|---|---|
| `⊢ P (eval x (p - q))` | `⊢ P (eval x p - eval x q)` |

**R3 · `eval_mul`** changes the **goal**. Lemma: `eval x (p * q) = eval x p * eval x q`. Same placeholders.

| Before | After |
|---|---|
| `⊢ P (eval x (p * q))` | `⊢ P (eval x p * eval x q)` |

**R4 · `eval_pow`** changes the **goal**. Lemma: `eval x (p ^ n) = eval x p ^ n`. Placeholders:
`{R : Type} [CommRing R] (p : R[X]) (n : ℕ) (x : R)`.

| Before | After |
|---|---|
| `⊢ P (eval x (p ^ n))` | `⊢ P (eval x p ^ n)` |

**R5 · `eval_X`** changes the **goal**: the variable evaluates to the point. Lemma: `eval x X = x`.
`rw` replaces every `eval x X` in the goal at once. Placeholders: `{R : Type} [CommRing R] (x : R)`.

| Before | After |
|---|---|
| `⊢ P (eval x X)` | `⊢ P x` |

**R6 · `eval_C`** changes the **goal**: a constant polynomial evaluates to its constant. Lemma:
`eval x (C a) = a`. Placeholders: `{R : Type} [CommRing R] (a x : R)`.

| Before | After |
|---|---|
| `⊢ P (eval x (C a))` | `⊢ P a` |

**R7 · `eval_ofNat`, `eval_one`** change the **goal**: a numeral polynomial evaluates to the same numeral.
Lemmas: `eval x (OfNat.ofNat n) = OfNat.ofNat n` for numerals `n ≥ 2`, and `eval x 1 = 1` (also `eval_zero`
for `0`). Placeholders: `{R : Type} [CommRing R] (x : R)`, `P : R → R → Prop`.

| Before | After |
|---|---|
| `⊢ P (eval x 2) (eval x 1)` | `⊢ P 2 1` |

**R8 · `norm_num`** **closes** a goal made of numerals, such as `5 ^ 2 - 3 * 5 + 2 = 12` in `ℝ`. R1–R7
are `simp` lemmas, so `norm_num` (which runs `simp` first) also pushes `eval` inside by itself.

| Before | After |
|---|---|
| `⊢ 5 ^ 2 - 3 * 5 + 2 = 12` | no goals |

**W1 / W2: a concrete polynomial.** `(X ^ 3 + C 2 * X : ℝ[X]).eval 2 = 12`. One `rw` with R1, R3, R4, R6, R5
leaves only numbers, which R8 closes; or `norm_num` alone does everything:

```lean-goal
⊢ eval 2 (X ^ 3 + C 2 * X) = 12
⊢ 2 ^ 3 + 2 * 2 = 12
```

---

## Part 2 · `eval_product`

Statement: if `eval x p = 2` and `eval x q = 5`, then `(p * q + C 1).eval x = 11`. Nothing is known about
`p` and `q` except their values at `x`, so the only way in is to push `eval` down to `eval x p` and
`eval x q` (R1, R3, R6), then substitute the hypotheses with `rw [hp, hq]` (TACTIC_STATES, "Rewriting"),
then compute (R8).

**W3: the same pattern on `p - q * C 2`** with `hp : eval x p = 3`, `hq : eval x q = 4`. After
`rw [eval_sub, eval_mul, eval_C]` (R2, R3, R6), the hypotheses match literally, and `rw [hp, hq]` leaves a
numeral goal for R8:

```lean-goal
⊢ eval x (p - q * C 2) = -5
⊢ eval x p - eval x q * 2 = -5
⊢ 3 - 4 * 2 = -5
```

---

## Part 3 · `eval_root_factor`

Statement: if `r` is a root of `p`, then `r` is a root of `p * (X - C 7)`. Turn the hypothesis into an
equation (R9), push `eval` through the product (R3), substitute, and `0 * a = 0` (R10). `simp` given the
equation from R9 does all of this in one call.

**R9 · `IsRoot.eq_zero`** changes the **context**. Lemma: `p.IsRoot r → eval r p = 0`; with dot notation
`h.eq_zero` is the proof of `eval r p = 0`. `IsRoot` is *defined* as that equation, but `rw` and `simp`
match names, not definitions, so they need the equation form. Placeholders:
`{R : Type} [CommRing R] (p : R[X]) (r : R) (h : p.IsRoot r)`.

| Before | After `have h0 := h.eq_zero` |
|---|---|
| `h : p.IsRoot r ⊢ eval r p = 0` | `h0 : eval r p = 0 ⊢ eval r p = 0` |

**R10 · `zero_mul`** changes the **goal**. Lemma: `0 * a = 0` (its mirror is `mul_zero : a * 0 = 0`).
Placeholders: `{R : Type} [CommRing R] (a : R)`.

| Before | After |
|---|---|
| `⊢ P (0 * a)` | `⊢ P 0` |

**W4: a root of `p` makes `X ^ 2 * p` vanish at `r`.** Plain `simp` uses
`mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0` (and `X ^ 2` evaluates to `r ^ 2`, which is `0` iff `r = 0`), so it
stops at a disjunction (still provable, with `right; exact h.eq_zero`):

```lean-goal
⊢ eval r (X ^ 2 * p) = 0
⊢ r = 0 ∨ eval r p = 0
```

Rewriting instead: R3, then `rw [h.eq_zero]`, then `mul_zero` (the factor `0` is on the right here):

```lean-goal
⊢ eval r (X ^ 2) * eval r p = 0
⊢ eval r (X ^ 2) * 0 = 0
```

---

## Traps

- The infoview prints `p.eval x` as `eval x p`. When you write a `have`, either form works; the point is
  the first explicit argument of `Polynomial.eval`.
- `simp [h]` with `h : p.IsRoot r` does not use `h`: the goal contains `eval r p`, not `IsRoot`. Pass
  `h.eq_zero` (R9).
- `rw [eval_C]` does not touch `eval x 2` or `eval x 1`: numerals in `R[X]` are not syntactically `C 2`.
  Use R7, or let `norm_num` handle them.
- `rw [hp]` needs `eval x p` to appear literally, so push `eval` all the way down first (R1, R3).
- Rewrite from the outside in. `rw [eval_mul]` fails on `eval x (p * q + C 1)` ("Did not find an
  occurrence of the pattern `eval ?m (?m * ?m)`", with numbered `?m`s): `eval` is applied to the sum, so `eval_add` (R1) must
  split the `+` first.
- `simp [h]` with an unused `h` also triggers a linter warning ("This simp argument is unused").

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `eval` of `+`, `-`, `*`, `^` | `rw [eval_add]`, `rw [eval_sub]`, `rw [eval_mul]`, `rw [eval_pow]` | R1–R4 |
| `eval x X → x` | `rw [eval_X]` | R5 |
| `eval x (C a) → a` | `rw [eval_C]` | R6 |
| `eval x 2 → 2`, `eval x 1 → 1` | `rw [eval_ofNat, eval_one]` | R7 |
| numeric goal, or a concrete polynomial at a point | `norm_num` | R8 |
| use known values `hp : eval x p = c` | `rw [hp]` after R1–R6 | TACTIC_STATES |
| `p.IsRoot r → eval r p = 0` | `h.eq_zero` | R9 |
| `0 * a → 0` / `a * 0 → 0` | `rw [zero_mul]` / `rw [mul_zero]` | R10 |
| everything at once, given an equation | `simp [h.eq_zero]` | R3, R9, R10 |
| see the state | infoview | |
