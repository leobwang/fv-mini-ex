# H075 · Explicit heat scheme: stability, instability, convergence: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033: `intro`, `exact`, `have`, `rw`, `simp`,
`induction … with`, `calc`, `funext`). **New here:** Mathlib's real numbers `ℝ` with the
absolute value `|·|`; functions on the grid `ℤ → ℝ`; the iterate `f^[n]`; integer powers (`zpow`)
`a ^ (j : ℤ)`; the casts `↑n : ℝ` of natural numbers; limits `Tendsto … atTop atTop` (Mathlib's
filters); the tactics `linarith`, `gcongr`, `simp_rw`, `set`, `push_cast`, `ring_nf` (entries below)
and `ring`, `norm_num` (TACTIC_STATES, "Closing": `ring` proves identities of commutative rings,
`norm_num` proves numeric facts such as `(-1 : ℝ) ≠ 0`).

**The mathematics.** A grid function `u : ℤ → ℝ` holds the values `uⱼ` at the points `j Δx`. One step
of the scheme is `S u = heatStep r u`, `(S u)ⱼ = r uⱼ₋₁ + (1 − 2r) uⱼ + r uⱼ₊₁`, with `r = Δt/Δx²`
(time step `Δt`, grid spacing `Δx`). `Sⁿ = (heatStep r)^[n]` is `n` steps.

1. *Stability* (`heat_stable`). For `0 ≤ r ≤ 1/2` all three weights are `≥ 0` and sum to 1, so
   `|(S u)ⱼ| ≤ sup |u|` (`step_bound`); induction on `n` gives `|(Sⁿ u)ⱼ| ≤ M`.
2. *Instability* (`heat_unstable`). On the checkerboard `vⱼ = (−1)ʲ ε`, `S v = (1 − 4r) v`
   (`checkerboard`), so `|(Sⁿ v)₀| = |1 − 4r|ⁿ |ε|`, and `r > 1/2` gives `|1 − 4r| > 1`.
3. *Lax convergence* (`heat_lax`). `U n j` is the exact solution at step `n`, point `j`, and `τ` bounds
   the local error `|U(n+1) − S(U n)|`. With `eₙ = sup |U n − Sⁿ U 0|` (the global error):
   `U(n+1) − S(Sⁿ U0) = [U(n+1) − S(U n)] + [S(U n) − S(Sⁿ U0)]`, and `S(U n) − S(Sⁿ U0) = S(U n − Sⁿ U0)`
   (`step_sub`: `S` is linear), so `eₙ₊₁ ≤ τ + eₙ` and `eₙ ≤ n τ`. Consistency + stability ⇒ convergence.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`, `have` or `exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. A hypothesis `h` in an entry only finishes the example.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid α]` is a
  requirement on `α` (a *type class*); `ℝ` meets every bracket used here.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℤ → ℝ` | a grid function: one real value per grid point `j : ℤ` (no boundary) |
| `heatStep r u j` | the value at point `j` after one step from `u` |
| `f^[n] x` | `f` applied `n` times to `x` (`Nat.iterate`); `f^[0] x` is `x` |
| `\|a\|` | absolute value of `a : ℝ` |
| `(-1) ^ j` with `j : ℤ` | an integer power (`zpow`); `(-1) ^ (j - 1)` does NOT simplify by itself |
| `a ^ n` with `n : ℕ` | a natural power (`Monoid.npow`); `pow_succ` applies, `zpow_add_one₀` does not |
| `a ^ 0` | ambiguous on screen: check whether `0 : ℕ` (`pow_zero`) or `0 : ℤ` (`zpow_zero`) |
| `a⁻¹` | the inverse `1 / a` (`a⁻¹ = 0` when `a = 0` in Lean) |
| `↑n` | the natural number `n` cast to `ℝ` (`Nat.cast`); `↑(n + 1)` is not literally `↑n + 1` (R30) |
| `Tendsto f atTop atTop` | `f n → +∞` as `n → ∞`; `atTop` is the filter of "eventually large" values (`Filter.atTop`; `open Filter` lets you drop the prefix) |
| `V : ℤ → ℝ := e` | a local definition made by `set` (R27): `V` stands for `e` |
| `n✝`, `a✝` | inaccessible names: Lean made them, you cannot type them; name them with `with`/`case` |
| `V : ℤ → ℝ := ⋯` | the same local definition, its body elided by the infoview (`⋯` hides a term) |
| `case h₁`, `case succ` | the name of a goal after `gcongr` / `induction` |

---

## Part 1 · `step_bound` (milestone)

Statement: if `0 ≤ r ≤ 1/2` and `|u j| ≤ M` for all `j`, then `|heatStep r u j| ≤ M`. Prove this first:
Parts 4 and 6 use it.

**R1 · `have h1 := hu x`** changes the **context**: from `hu : ∀ y, Q y` it adds the instance
`h1 : Q x`. Placeholders: `(Q : ℤ → Prop) (hu : ∀ y, Q y) (x : ℤ)`.

| Before | After `have h1 := hu (x - 1)` |
|---|---|
| `⊢ Q (x - 1)` | `h1 : Q (x - 1) ⊢ Q (x - 1)` |

**R2 · `linarith`** **closes** a goal `t ≤ s`, `t < s` or `t = s` that follows from the hypotheses by
adding them up with nonnegative coefficients (linear arithmetic over `ℝ`). It does not multiply two
unknowns. Placeholders: `(r : ℝ) (hr : r ≤ 1 / 3)`.

| Before | After |
|---|---|
| `⊢ 0 ≤ 1 - 3 * r` | no goals |

**R3 · `unfold D`** changes the **goal**: the defined name `D` applied to its arguments becomes its body.
Placeholders: the guide's `upwind (c : ℝ) (v : ℤ → ℝ) : ℤ → ℝ := fun j => (1 - c) * v j + c * v (j - 1)`.

| Before | After |
|---|---|
| `⊢ P (upwind c v j)` | `⊢ P ((1 - c) * v j + c * v (j - 1))` |

**R4 · `calc`** changes the **goal list**: a chain `a ≤ b`, `_ ≤ c`, … proves `a ≤ c`; each link is
proved after its `:=` (a term, `by tac`, or `?_` to leave it as a goal). Links may mix `=`, `≤`, `<`.
Placeholders: `{α : Type} [LinearOrder α] (a b c : α)`. The first link must start with the goal's left
side, written out in full; later links start with `_`.

| Before | After `calc a ≤ b := ?_` / `_ ≤ c := ?_` |
|---|---|
| `⊢ a ≤ c` | `⊢ a ≤ b`, `⊢ b ≤ c` |

**R5 · `abs_add_three`** **closes** the first link. The lemma is `abs_add_three a b c : |a + b + c| ≤ |a| + |b| + |c|`;
`abs_add_three _ _ _` lets Lean read `a b c` off the goal. Placeholders: `(a b c : ℝ)`.

Before `exact abs_add_three a b c` (after it: no goals):

```lean-goal
⊢ |a + b + c| ≤ |a| + |b| + |c|
```

**R6 · `rw [abs_mul]`** changes the **goal**. The lemma is `abs_mul : |a * b| = |a| * |b|`; one `rw`
rewrites the first product pattern it finds (all its copies), so repeat it per product. Placeholders: `(a b : ℝ)`.

Before, then after `rw [abs_mul]`:

```lean-goal
⊢ P |a * b|
⊢ P (|a| * |b|)
```

**R7 · `rw [abs_of_nonneg ha]`** changes the **goal**. The lemma is `abs_of_nonneg : 0 ≤ a → |a| = a`.
Placeholders: `(a : ℝ) (ha : 0 ≤ a)`.

Before (with `ha : 0 ≤ a` in the context), then after `rw [abs_of_nonneg ha]`:

```lean-goal
⊢ P |a|
⊢ P a
```

**R8 · `gcongr`** changes the **goal list**: for `lhs ≤ rhs` with the same shape on both sides, it keeps
only the parts that differ (`x ≤ M`, `y ≤ M`). It closes the side goals `0 ≤ r`, `0 ≤ s` (positivity or
a hypothesis) and every remaining goal that is a hypothesis (here `hy`). Placeholders:
`(r s x y M : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hy : y ≤ M)`. For a sum `a + b ≤ c + d` it gives `a ≤ c`, `b ≤ d`.

| Before | After |
|---|---|
| `hy : y ≤ M ⊢ r * x + s * y ≤ r * M + s * M` | `⊢ x ≤ M` |

The last link `r * M + (1 - 2 * r) * M + r * M = M` is `ring` (TACTIC_STATES, "Closing").

**W1 (the upwind scheme, not the exercise's).** For `0 ≤ c ≤ 1`, one step `(1 − c) vₖ + c vₖ₋₁` is a
two-point average. R1 twice, R2 for `0 ≤ 1 - c`, R3, then a `calc` (R4) with `abs_add_le` (R29), R6, R7,
R8, `ring`. After `unfold upwind`:

```lean-goal
⊢ |(1 - c) * v k + c * v (k - 1)| ≤ B
```

---

## Part 2 · `checkerboard` (milestone)

Statement: `Sⁿ` applied to `j ↦ (-1) ^ j * ε` is `j ↦ (1 - 4r) ^ n * ((-1) ^ j * ε)`. Induction on `n`;
`(-1) ^ j` is an integer power, so `(-1) ^ (j - 1)` and `(-1) ^ (j + 1)` need R12, R13.

**R9 · `Function.iterate_zero`, `id_eq`** change the **goal**: `f^[0] = id` and `id x = x`. `simp` uses them
by itself, and `exact` accepts `f^[0] x` where `x` is expected (they are equal by definition).
Placeholders: `(f : ℝ → ℝ) (x : ℝ)`.

| Before | After `simp only [Function.iterate_zero, id_eq]` |
|---|---|
| `⊢ P (f^[0] x)` | `⊢ P x` |

**R10 · `rw [Function.iterate_succ_apply']`** changes the **goal**. The lemma is
`f^[n.succ] x = f (f^[n] x)` (`n.succ` is `n + 1`): it peels off the LAST application, which is the one
the induction step needs. (Without the prime, `Function.iterate_succ_apply` peels the first:
`f^[n] (f x)`.) Placeholders: `(f : ℝ → ℝ) (x : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (f^[n + 1] x)` | `⊢ P (f (f^[n] x))` |

**R11 · `simp only [D]`** changes the **goal**: like R3, and it also beta-reduces `(fun j => …) k` to the
body at `k`. Use it when the argument is a `fun`. Placeholders: `upwind` from R3, `(c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (upwind c (fun x => 1) 0)` | `⊢ P ((1 - c) * 1 + c * 1)` |

**R12 · `rw [zpow_sub_one₀ ha]`** changes the **goal**. The lemma is
`zpow_sub_one₀ : a ≠ 0 → ∀ n : ℤ, a ^ (n - 1) = a ^ n * a⁻¹`. Placeholders: `(a : ℝ) (ha : a ≠ 0) (n : ℤ)`.
For `a = -1` write `zpow_sub_one₀ (by norm_num)`.

| Before | After |
|---|---|
| `⊢ P (a ^ (n - 1))` | `⊢ P (a ^ n * a⁻¹)` |

**R13 · `rw [zpow_add_one₀ ha]`** changes the **goal**. The lemma is
`zpow_add_one₀ : a ≠ 0 → ∀ n : ℤ, a ^ (n + 1) = a ^ n * a`. Placeholders: `(a : ℝ) (ha : a ≠ 0) (n : ℤ)`.

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

**R14 · `rw [pow_succ]`** changes the **goal**. The lemma is `pow_succ : a ^ (n + 1) = a ^ n * a` for
`n : ℕ`. Same picture as R13, different exponent type: `(1 - 4 * r) ^ (n + 1)` has `n : ℕ`, so it needs
this one. Placeholders: `{α : Type} [Monoid α] (a : α) (n : ℕ)` (α has an associative `*` with `1`).

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

**R15 · `ring`** **closes** an identity of fields. It evaluates inverses of numerals (`(-1)⁻¹ = -1`) and
treats `(-1) ^ j` with `j : ℤ` as an unknown, which is why R12, R13 come first: afterwards every power
is the same unknown `(-1) ^ j`. Placeholders: `(s a : ℝ) (j : ℤ)`.

| Before | After |
|---|---|
| `⊢ s * ((-1) ^ j * (-1)⁻¹ * a) = -(s * ((-1) ^ j * a))` | no goals |

**W2 (upwind on the checkerboard).** `upwind c` maps `(-1) ^ j` to `(1 - 2c) (-1) ^ j`: `funext j`, R11,
R12, R15.

```lean-goal
⊢ (upwind c fun j => (-1) ^ j) = fun j => (1 - 2 * c) * (-1) ^ j
⊢ upwind c (fun j => (-1) ^ j) j = (1 - 2 * c) * (-1) ^ j
⊢ (1 - c) * (-1) ^ j + c * (-1) ^ (j - 1) = (1 - 2 * c) * (-1) ^ j
⊢ (1 - c) * (-1) ^ j + c * ((-1) ^ j * (-1)⁻¹) = (1 - 2 * c) * (-1) ^ j
```

---

## Part 3 · `step_sub` (milestone)

Statement: `heatStep r u j - heatStep r v j = heatStep r (fun k => u k - v k) j` (the step is linear).
R11 on `heatStep` unfolds all three occurrences and beta-reduces `(fun k => u k - v k) (j - 1)`; then
`ring`. No new entries.

---

## Part 4 · `heat_stable`

Statement: `0 ≤ r ≤ 1/2` and `|u j| ≤ M` for all `j` give `|(heatStep r)^[n] u j| ≤ M` for all `n, j`.

**R16 · `induction n generalizing j`** changes the **goal list and the context**: one goal for `n = 0`
and one for `n + 1`, and the IH is stated for **every** `j` (because `j` is generalized). That matters:
`step_bound` needs the bound at `j - 1`, `j`, `j + 1`. Placeholders: `(Q : ℕ → ℤ → Prop) (n : ℕ) (j : ℤ)`.
The plain form leaves inaccessible names `n✝ a✝`; the `with` form (`| zero => … | succ n ih => …`), or
`case succ n ih => …`, names them `n` and `ih`.

| Before | After |
|---|---|
| `j : ℤ ⊢ Q n j` | `⊢ Q 0 j`, `n✝ : ℕ ⊢ Q (n✝ + 1) j` |

In the second goal the IH is `a✝ : ∀ (j : ℤ), Q n✝ j`: every `j`, not just the goal's.

**R17 · `have hb := lem _ ih`** changes the **context**. When a lemma wants `hu : ∀ j, |u j| ≤ M` and you
pass `ih : ∀ j, |f j - g j| ≤ M`, Lean solves the `_` for `u` by matching `u j` with `f j - g j`, so
`u := fun j => f j - g j`. Use the same with `exact`. Placeholders: `(f g : ℤ → ℝ)`,
`(lem : ∀ u : ℤ → ℝ, (∀ j, |u j| ≤ 1) → L u)`.

With `ih : ∀ (j : ℤ), |f j - g j| ≤ 1` in the context:

| Before | After |
|---|---|
| `⊢ L fun k => f k - g k` | `hb : L fun j => f j - g j ⊢ L fun k => f k - g k` |

(`fun j => …` and `fun k => …` are the same function; `exact hb` accepts it.)

**W4 (an iterate of `x ↦ x + 2`).** `(fun x => x + 2)^[n] 0 = 2 * ↑n` by `induction n with`, R10, `ih`,
R30, `ring`:

```lean-goal
⊢ (fun x => x + 2)^[n] 0 = 2 * ↑n
```

---

## Part 5 · `heat_unstable`

Statement: `r > 1/2` and `ε ≠ 0` give `|(Sⁿ checkerboard)₀| → +∞`.

**R18 · `rw [abs_of_neg ha]`** changes the **goal**. The lemma is `abs_of_neg : a < 0 → |a| = -a`.
Placeholders: `(a : ℝ) (ha : a < 0)`. Inline: `rw [abs_of_neg (by linarith)]` leaves the `1 < -(1 - 4 * r)`
that R2 closes.

Before, then after `rw [abs_of_neg ha]`:

```lean-goal
⊢ P |a|
⊢ P (-a)
```

**R19 · `simp_rw [l₁, l₂, …]`** changes the **goal**: it rewrites with each `lᵢ` in turn, also inside
`fun n => …`. `rw` cannot: under a binder the term mentions the bound `n`, and `rw` fails with
"did not find an occurrence". Placeholders: `(g : ℕ → ℝ) (P : (ℕ → ℝ) → Prop)`.

Before, then after `simp_rw [abs_mul]`:

```lean-goal
⊢ P fun n => |g n * 2|
⊢ P fun n => |g n| * |2|
```

**R20 · `zpow_zero`** changes the **goal**: `a ^ (0 : ℤ) = 1`. It prints as `a ^ 0`. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a ^ 0)` | `⊢ P 1` |

**R21 · `one_mul`** changes the **goal**: `1 * a = a`. Placeholders: `{α : Type} [Monoid α] (a : α)`.

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

**R22 · `abs_pow`** changes the **goal**: `|a ^ n| = |a| ^ n` for `n : ℕ`. Placeholders: `(a : ℝ) (n : ℕ)`.

Before, then after `rw [abs_pow]`:

```lean-goal
⊢ P |a ^ n|
⊢ P (|a| ^ n)
```

**R23 · `tendsto_pow_atTop_atTop_of_one_lt`** **closes** `aⁿ → +∞`. The lemma is
`1 < a → Tendsto (fun n : ℕ => a ^ n) atTop atTop`. Placeholders: `(a : ℝ) (ha : 1 < a)`.

| Before | After `exact tendsto_pow_atTop_atTop_of_one_lt ha` |
|---|---|
| `⊢ Tendsto (fun n => a ^ n) atTop atTop` | no goals |

**R24 · `Tendsto.atTop_mul_const`** **closes** `f n * c → +∞`. The lemma is
`0 < c → Tendsto f l atTop → Tendsto (fun x => f x * c) l atTop` (`l` is any filter; here `atTop`).
Written with dot notation on `hf`: `hf.atTop_mul_const hc`. Placeholders: `(f : ℕ → ℝ) (c : ℝ) (hc : 0 < c)`,
`(hf : Tendsto f atTop atTop)`.

| Before | After `exact hf.atTop_mul_const hc` |
|---|---|
| `⊢ Tendsto (fun n => f n * c) atTop atTop` | no goals |

**R25 · `abs_pos`** is the iff `0 < |a| ↔ a ≠ 0`; `abs_pos.mpr ha` proves `0 < |a|` from `ha : a ≠ 0`
(`.mpr` uses an iff right to left). Placeholders: `(a : ℝ) (ha : a ≠ 0)`.

Before `exact abs_pos.mpr ha` (after it: no goals):

```lean-goal
⊢ 0 < |a|
```

**W3 (`(-3) ^ n * 2`, not the exercise's).** R19 with R6 and R22, then R23 and R24, each side fact
`1 < |(-3)|`, `0 < |2|` by `norm_num`:

```lean-goal
⊢ Tendsto (fun n => |(-3) ^ n * 2|) atTop atTop
⊢ Tendsto (fun n => |(-3)| ^ n * |2|) atTop atTop
```

---

## Part 6 · `heat_lax`

Statement: `0 ≤ r ≤ 1/2` and local errors `|U (n + 1) j - heatStep r (U n) j| ≤ τ` give
`|U n j - (heatStep r)^[n] (U 0) j| ≤ ↑n * τ`. Induction on `n` generalizing `j` (R16), as in Part 4.

**R26 · `simp`** **closes** the base case once R9 has turned `f^[0] x` into `x`: it uses `sub_self`
(`a - a = 0`), `abs_zero`, `Nat.cast_zero` (`↑0 = 0`), `zero_mul` and `le_refl`. Placeholders: `(x τ : ℝ)`.

Before `simp` (after it: no goals):

```lean-goal
⊢ |x - x| ≤ ↑0 * τ
```

**R27 · `set V := e`** changes the **context and the goal**: it adds the local definition `V := e` and
replaces every `e` in the goal and in all hypotheses by `V`. Use it to give the scheme's value
`(heatStep r)^[n] (U 0)` a short name. Placeholders: `(e : ℤ → ℝ) (P Q : (ℤ → ℝ) → Prop) (ih : Q e)`.
`set V := e with hV` also adds `hV : V = e`.

| Before | After |
|---|---|
| `ih : Q e ⊢ P e` | `V : ℤ → ℝ := e, ih : Q V ⊢ P V` |

**R28 · `ring_nf`** **closes** an equation whose two sides have the same ring normal form, also inside
`|·|`, where `ring` fails (`|·|` is not a ring operation, but `ring_nf` normalizes its argument). Use it for
the "add and subtract" link. Placeholders: `(a b c : ℝ)`.

Before `ring_nf` (after it: no goals):

```lean-goal
⊢ |a - c| = |a - b + (b - c)|
```

**R29 · `abs_add_le`** **closes** the triangle inequality `|a + b| ≤ |a| + |b|`; in a `calc` link write
`abs_add_le _ _`. Placeholders: `(a b : ℝ)`.

Before `exact abs_add_le a b` (after it: no goals):

```lean-goal
⊢ |a + b| ≤ |a| + |b|
```

Then the link `… ≤ τ + ↑n * τ`: `rw [step_sub]` makes its second term exactly `hb`'s left side, `gcongr`
(R8) closes that part with `hb` and leaves the goal `|U (n + 1) j - heatStep r (U n) j| ≤ τ`, which is `hU n j`.

**R30 · `push_cast`** changes the **goal**: it pushes casts inward, `↑(n + 1)` → `↑n + 1`
(`Nat.cast_add`, `Nat.cast_one`), so `ring` can treat `↑n` as an unknown. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑(n + 1)` | `⊢ P (↑n + 1)` |

---

## Traps

- `(-1 : ℝ) ^ j` with `j : ℤ` is an integer power (`zpow`), not `pow`. `pow_succ` and `ring` do not
  simplify `(-1) ^ (j + 1)`: rewrite with R12, R13 first. The exponent `n` in `(1 - 4 * r) ^ n` is `ℕ`:
  there R14 (`pow_succ`), and `abs_pow` (R22) applies.
- `induction n` without `generalizing j` gives an IH only at the fixed `j`; `step_bound` needs it at
  `j - 1` and `j + 1` too.
- `Function.iterate_succ_apply'` (with the prime) is the one that matches `S (Sⁿ u)`. The unprimed
  version gives `Sⁿ (S u)`.
- `rw` cannot rewrite inside `fun n => …` (R19): use `simp_rw`.
- The `≤ τ + ↑n * τ` link needs `step_sub` first, or `gcongr` cannot match `hb`.
- The goal's `↑(n + 1) * τ` is a cast of a sum; `ring` alone fails until `push_cast` (R30).
- `U n j` is the exact solution at time step `n`, grid point `j`. The grid `ℤ` has no boundary, so no
  boundary conditions appear anywhere.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| use `hu : ∀ j, …` at a point | `have h1 := hu (j - 1)` | R1 |
| linear (in)equality from hypotheses | `linarith` | R2 |
| unfold the step | `unfold heatStep` / `simp only [heatStep]` | R3, R11 |
| chain of `≤` and `=` | `calc a ≤ b := … ` / `_ = c := …` | R4 |
| `\|a + b + c\| ≤ …`, `\|a + b\| ≤ …` | `abs_add_three _ _ _`, `abs_add_le _ _` | R5, R29 |
| `\|a * b\|`, `\|a ^ n\|` | `rw [abs_mul]`, `abs_pow` | R6, R22 |
| drop `\|·\|` by sign | `rw [abs_of_nonneg h]` / `rw [abs_of_neg h]` | R7, R18 |
| compare sums/products termwise | `gcongr` | R8 |
| `f^[0] x`, `f^[n+1] x` | `simp` / `rw [Function.iterate_succ_apply']` | R9, R10 |
| `(-1) ^ (j ∓ 1)` with `j : ℤ` | `rw [zpow_sub_one₀ (by norm_num), zpow_add_one₀ (by norm_num)]` | R12, R13 |
| `a ^ (n + 1)` with `n : ℕ` | `rw [pow_succ]` | R14 |
| close with `(-1)⁻¹` around | `ring` | R15 |
| IH at every grid point | `induction n generalizing j with` | R16 |
| apply a lemma, Lean finds `u` | `step_bound … _ M ih j` | R17 |
| rewrite under `fun n =>` | `simp_rw [l₁, l₂]` | R19 |
| `a ^ (0 : ℤ)`, `1 * a` | `zpow_zero`, `one_mul` | R20, R21 |
| `aⁿ → +∞`, times a constant | `(tendsto_pow_atTop_atTop_of_one_lt h).atTop_mul_const hc` | R23, R24 |
| `0 < \|a\|` | `abs_pos.mpr ha` | R25 |
| name a subterm | `set V := e` | R27 |
| add-and-subtract inside `\|·\|` | `by ring_nf` | R28 |
| `↑(n + 1)` → `↑n + 1` | `push_cast` | R30 |
| see the state | infoview | |
