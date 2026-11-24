# M122 · Harmonic oscillator: Euler vs symplectic Euler: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `induction`, `simp`, `rw`, `have`, pairs and `.1`/`.2`.
**New here:** Mathlib's real numbers `ℝ`, recursive functions whose value is a pair in `ℝ × ℝ`, and the
Mathlib arithmetic tactics `linear_combination`, `linarith`, `nlinarith`, plus `set`.

The physics, with `q` the position, `p` the momentum, `ω` the angular frequency and `h` the step size:
the oscillator `q' = p`, `p' = -ω²q` has energy `E = p² + ω²q²`.

| Scheme | One step `(q, p) ↦ (q₁, p₁)` | What the exercise proves |
|---|---|---|
| explicit Euler `eulerHO` | `q₁ = q + h p`, `p₁ = p - h ω² q` | `E₁ = (1 + h²ω²) E`: the energy grows geometrically |
| symplectic Euler `sympHO` | `p₁ = p - h ω² q` first, then `q₁ = q + h p₁` | the shadow energy `S = E - h ω² q p` is exactly conserved |
| | | for `0 ≤ hω < 2`: `E ≤ (2 + hω)/(2 - hω) · E₀` at every step |

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. A `P : Prop` with `k : T → P` is "whatever the goal is": the entry only adds a fact.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[DivisionCommMonoid α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- `orbit f g x₀ y₀ n` and `leap f g x₀ y₀ n` are recursions defined in `guide.lean` with the same shape as
  `eulerHO` and `sympHO`; `f g : ℝ → ℝ → ℝ` are placeholders for the update formulas.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (`Real`). `0 ≤ x`, `x < y`, `x / y` are the usual order and division; numerals such as `2` in `h * ω < 2` are reals here |
| `a / b * c` | `(a / b) * c`: `*` and `/` group to the left, so `(2 + h * ω) / (2 - h * ω) * E₀` is the fraction times `E₀` (R11 moves the `/` outside) |
| `let p' := e` then a body (in `sympHO`) | a local name: `p'` stands for `e` inside the body. `simp only [sympHO]` substitutes it, so goals never show `let` (R6) |
| `ℝ × ℝ` | pairs of reals (`Prod ℝ ℝ`); here a state `(q, p)` |
| `(a, b)` | the pair with first component `a`, second `b` |
| `s.1`, `s.2` | first and second component of the pair `s` (`Prod.fst`, `Prod.snd`): position `q`, momentum `p` |
| `(eulerHO ω h q₀ p₀ n).2` | the momentum after `n` Euler steps from `(q₀, p₀)` |
| `x ^ 2`, `c ^ n` | power with a natural-number exponent (`n : ℕ`) |
| `a / b` | real division; Lean sets `a / 0 = 0`, so `le_div_iff₀` needs `0 < b` |
| `case zero`, `case succ` | the base case and the step case after `induction n` |
| `ih :` followed by indented lines | a long hypothesis is printed on the lines below its name |
| `q : ℝ := (sympHO ω h q₀ p₀ n).1` | a local definition made by `set` (R8): `q` abbreviates that term |
| `fun x x_1 => 2 * x` | a function of two arguments that ignores the second (written `fun x _ => 2 * x`) |
| `inst✝ : DivisionCommMonoid α` | an unnamed type-class assumption from a `[…]` binder |

---

## Part 1 · `euler_energy_grows`

Statement: after `n` explicit Euler steps, `p² + ω²q² = (1 + h²ω²)ⁿ (p₀² + ω²q₀²)`.
Why: with `(q, p)` the step-`n` state, `(p - hω²q)² + ω²(q + hp)² = (1 + h²ω²)(p² + ω²q²)`, because the
cross terms `∓2hω²qp` cancel. So the step is a polynomial identity plus `ih` scaled by `1 + h²ω²`.

**R1 · `induction n with | zero => ?_ | succ n ih => ?_`** changes the **goal list and the context**: one goal
`P n` becomes the base case `P 0` and the step `P (n + 1)` with `ih : P n`. Placeholders: `(P : ℕ → Prop)
(n : ℕ)`. In your proof write the tactics directly after each `=>`; `?_` just leaves the goal open.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `n : ℕ, ih : P n ⊢ P (n + 1)` |

**R2 · `simp [d]` on step `0`** **closes** the base case. It applies the defining equation of `d` at `0`
(here `orbit f g x₀ y₀ 0 = (x₀, y₀)`), the projections `(a, b).1 = a`, `(a, b).2 = b`, `pow_zero : a ^ 0 = 1`
and `one_mul : 1 * a = a`. Placeholders: `(f g F : ℝ → ℝ → ℝ) (x₀ y₀ c : ℝ)`.

| Before | After |
|---|---|
| `⊢ F (orbit f g x₀ y₀ 0).1 (orbit f g x₀ y₀ 0).2 = c ^ 0 * F x₀ y₀` | no goals |

**R3 · `simp only [d]` on step `n + 1`** changes the **goal**: it applies the defining equation of `d` at
`n + 1` once and takes `.1`/`.2` of the new pair. Step `n` stays folded (the equation only matches
`n + 1`), so `ih`, which talks about step `n`, still matches. Placeholders: `(f g : ℝ → ℝ → ℝ) (x₀ y₀ : ℝ)
(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (orbit f g x₀ y₀ (n + 1)).1` | `⊢ P (f (orbit f g x₀ y₀ n).1 (orbit f g x₀ y₀ n).2)` |

**R4 · `linear_combination e * ih`** **closes** an equation `lhs = rhs`. With `ih : a = b` it checks, by
`ring`, that `lhs - rhs - e * (a - b) = 0`. Several facts: `linear_combination e₁ * h₁ + e₂ * h₂`.
Placeholders: `(a b e r : ℝ) (ih : a = b)`, with `r` the part of both sides that `ih` does not touch; `e` may be any
expression, including powers like `(1 + c) ^ n`.

| Before | After |
|---|---|
| `ih : a = b ⊢ e * a + r = e * b + r` | no goals |

**W1: doubling both components multiplies `x² + y²` by 4 each step** (R1, R2, R3, R4). After `simp only
[orbit]` the step goal is a polynomial in the step-`n` components, and `linear_combination 4 * ih` closes it:

```lean-goal
⊢ (2 * (orbit (fun x x_1 => 2 * x) (fun x y => 2 * y) x₀ y₀ n).1) ^ 2 + (2 * (orbit (fun x x_1 => 2 * x) (fun x y => 2 * y) x₀ y₀ n).2) ^ 2 = 4 ^ (n + 1) * (x₀ ^ 2 + y₀ ^ 2)
```

`ring` inside `linear_combination` knows `4 ^ (n + 1) = 4 ^ n * 4`, so no `pow_succ` is needed.

---

## Part 2 · `symp_shadow_energy`

Statement: the shadow energy `S = p² + ω²q² - hω²qp` after `n` symplectic Euler steps equals its value at
`(q₀, p₀)`. Why: with `p₁ = p - hω²q` and `q₁ = q + hp₁`, the step identity `S(q₁, p₁) = S(q, p)` is a
polynomial identity in `q, p` (expand it, or see that `ω²q₁² - hω²q₁p₁ = ω²q₁q`).

**R1, R2** as in Part 1 (`simp [sympHO]` for the base case).

**R5 · `rw [← ih]`** with `ih : E n = c` changes the **goal**: every `c` becomes `E n`. When `c` is the
initial value of a conserved quantity, this turns "`E (n + 1)` equals the initial value" into the one-step
claim "`E (n + 1) = E n`". Placeholders: `(E : ℕ → ℝ) (c : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `ih : E n = c ⊢ E (n + 1) = c` | `⊢ E (n + 1) = E n` |

**R6 · `simp only [d]` with a `let` in the step** changes the **goal**: as R3, and the local `let y' := …` is
substituted into the body (`simp` inlines `let`s by default), so the new first component shows the new
second component written out. Placeholders: `(f g : ℝ → ℝ → ℝ) (x₀ y₀ : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (leap f g x₀ y₀ (n + 1)).1` | `⊢ P (f (leap f g x₀ y₀ n).1 (g (leap f g x₀ y₀ n).1 (leap f g x₀ y₀ n).2))` |

Then `ring` (TACTIC_STATES, "Closing") closes the polynomial identity: it treats each `(sympHO … n).1`,
`(sympHO … n).2` as an unknown.

**W2: the shear `y₁ = y + 1`, `x₁ = x + 2y₁ - 1` conserves `x - y²`** (R1, R2, R5, R6, `ring`). After
`rw [← ih]` and `simp only [leap]` the step goal is

```lean-goal
⊢ (leap (fun x y' => x + 2 * y' - 1) (fun x y => y + 1) x₀ y₀ n).1 + 2 * ((leap (fun x y' => x + 2 * y' - 1) (fun x y => y + 1) x₀ y₀ n).2 + 1) - 1 - ((leap (fun x y' => x + 2 * y' - 1) (fun x y => y + 1) x₀ y₀ n).2 + 1) ^ 2 = (leap (fun x y' => x + 2 * y' - 1) (fun x y => y + 1) x₀ y₀ n).1 - (leap (fun x y' => x + 2 * y' - 1) (fun x y => y + 1) x₀ y₀ n).2 ^ 2
```

and `ring` closes it.

---

## Part 3 · `symp_energy_bounded`

Statement: for `0 ≤ ω`, `0 ≤ h`, `hω < 2`, the true energy stays below `(2 + hω)/(2 - hω)` times its
initial value at every step. Why, with `E = p² + ω²q²` at step `n`, `E₀ = p₀² + ω²q₀²`, `S = E - hω²qp`, and
`S = S₀` by Part 2:

- `hω (ωq - p)² ≥ 0` expands to `2hω²qp ≤ hωE`, so `(2 - hω) E ≤ 2S`;
- `hω (ωq₀ + p₀)² ≥ 0` expands to `-2hω²q₀p₀ ≤ hωE₀`, so `2S₀ ≤ (2 + hω) E₀`;
- chain: `(2 - hω) E ≤ 2S = 2S₀ ≤ (2 + hω) E₀`, then divide by `2 - hω > 0`.

**R7 · `have hS := thm n`** changes the **context**: it adds the theorem `thm` at the argument `n`. A theorem
proved earlier in the file (Part 2) is used the same way, with all its arguments. Placeholders:
`(E : ℕ → ℝ) (c : ℝ) (thm : ∀ n, E n = c) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P` | `hS : E n = c ⊢ P` |

**R8 · `set x := e`** changes the **goal and the context**: every occurrence of `e`, in the goal and in the
hypotheses, is replaced by the new name `x`, and the context gains `x : ℝ := e`. `set x := e with hx` also adds
`hx : x = e`. Use it after R7, so `hS` is rewritten too. Placeholders: `(s : ℕ → ℝ × ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `hP : P (s n).1 ⊢ P (s n).1` | `x : ℝ := (s n).1, hP : P x ⊢ P x` |

**R9 · `mul_nonneg`** changes the **context** (used in `have`). The lemma is `0 ≤ a → 0 ≤ b → 0 ≤ a * b`.
Placeholders: `(a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)`; it holds in any ordered semiring (`ℕ`, `ℚ`, `ℝ`).
It also builds the hint terms for R14: `mul_nonneg hc (sq_nonneg t) : 0 ≤ c * t ^ 2`.

| Before | After |
|---|---|
| `⊢ P` | `hc : 0 ≤ a * b ⊢ P` |

**R10 · `sq_nonneg`** changes the **context** (used in `have`). The lemma is `sq_nonneg a : 0 ≤ a ^ 2`, for
any `a` (here `a - b`). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P` | `hq : 0 ≤ (a - b) ^ 2 ⊢ P` |

**R11 · `rw [div_mul_eq_mul_div]`** changes the **goal**. The lemma is `a / b * c = a * c / b`: it moves the
division to the outside, where R12 can remove it. Placeholders: `{α : Type} [DivisionCommMonoid α] (a b c : α)`
(α has a commutative `*` and `/`; `ℝ` and `ℚ` qualify).

| Before | After |
|---|---|
| `⊢ P (a / b * c)` | `⊢ P (a * c / b)` |

**R12 · `rw [le_div_iff₀]`** changes the **goal list**. The lemma is `0 < c → (a ≤ b / c ↔ a * c ≤ b)`: the
goal loses the division, and a side goal `0 < c` is added. Write `rw [le_div_iff₀ (by linarith)]` to close
the side goal on the spot (R13). Placeholders: `(a b c : ℝ)` (Mathlib states it for any ordered group with
zero, `ℝ` and `ℚ` included).

| Before | After |
|---|---|
| `⊢ a ≤ b / c` | `⊢ a * c ≤ b`, `⊢ 0 < c` |

**R13 · `linarith`** **closes** a goal that is a linear consequence (sums and numeral multiples) of the
hypotheses, `<`, `≤`, `=` alike. Nonlinear terms such as `h * ω` count as one unknown. Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `ha : a < 2 ⊢ 0 < 2 - a` | no goals |

**R14 · `nlinarith [t₁, t₂]`** **closes** a goal like `linarith`, after adding the facts `tᵢ` and the products
of pairs of hypotheses and facts. Placeholders: `(a b c : ℝ) (hc : 0 ≤ c)`. In the example it needs the
product of `hc` with `0 ≤ (a - b) ^ 2`; `linarith [sq_nonneg (a - b)]` fails. If you pass the products
yourself (`mul_nonneg hc (sq_nonneg (a - b))`), the rest is linear in the monomials.

| Before | After |
|---|---|
| `hc : 0 ≤ c ⊢ 2 * c * a * b ≤ c * (a ^ 2 + b ^ 2)` | no goals |

**W3: from a conserved `x² + y² = c` to `xy ≤ c/2`** (R7, R8, R11, R12, R14). After `have hS := thm n`,
`set x := (s n).1`, `set y := (s n).2` and `rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]`:

```lean-goal
⊢ x * y ≤ 1 / 2 * c
⊢ x * y * 2 ≤ 1 * c
```

and `nlinarith [sq_nonneg (x - y)]` closes it, using `hS : x ^ 2 + y ^ 2 = c`.

---

## Traps

- `grind` and `try?` are banned: they close the two identities of Parts 1 and 2 without the algebra.
- Prefer `simp only [eulerHO]` in the step: it unfolds exactly one step and nothing else, so the goal is the
  predictable polynomial of R3. Full `simp [eulerHO]` happens to work here too, but it also applies arithmetic
  lemmas, and in other problems that reshapes the goal so that `ih` no longer matches.
- `linear_combination ih` (coefficient 1) fails in Part 1: the right side of the step carries one extra factor
  `1 + h ^ 2 * ω ^ 2`, so `ih` must be scaled by it.
- `rw [← ih]` replaces every copy of the initial value `p₀ ^ 2 + ω ^ 2 * q₀ ^ 2 - h * ω ^ 2 * q₀ * p₀`; it must
  appear literally (it does, as the right side). `linear_combination ih` works there too.
- `set` only renames occurrences that already exist. Do R7 (`have hS := …`) **before** R8, or `hS` keeps the
  long `(sympHO ω h q₀ p₀ n).1`.
- `le_div_iff₀` needs `0 < 2 - h * ω`, which `linarith` gets from `hstab : h * ω < 2`.
- `nlinarith` with no hints fails here: give it the two products `h ω (ω q - p)² ≥ 0` and
  `h ω (ω q₀ + p₀)² ≥ 0` (Part 3, "Why"), built with R9 and R10. With exactly these two hints the rest is
  linear in the monomials, so `linarith [same hints]` also closes it.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on the step count | `induction n with \| zero => … \| succ n ih => …` | R1 |
| base case of a recursion | `simp [eulerHO]` | R2 |
| unfold one step | `simp only [eulerHO]` | R3 |
| unfold one step with a `let` | `simp only [sympHO]` | R6 |
| equation = `e` × hypothesis, up to `ring` | `linear_combination e * ih` | R4 |
| conserved quantity: constant → step-`n` value | `rw [← ih]` | R5 |
| polynomial identity | `ring` | TACTIC_STATES |
| use an earlier theorem | `have hS := thm args` | R7 |
| name a long subterm everywhere | `set q := (sympHO ω h q₀ p₀ n).1` | R8 |
| `0 ≤ a * b`, `0 ≤ a ^ 2` | `mul_nonneg ha hb`, `sq_nonneg a` | R9, R10 |
| `a / b * c → a * c / b` | `rw [div_mul_eq_mul_div]` | R11 |
| `a ≤ b / c → a * c ≤ b` | `rw [le_div_iff₀ (by linarith)]` | R12, R13 |
| linear consequence | `linarith` | R13 |
| needs products of facts | `nlinarith [t₁, t₂]` | R14 |
| see the state | infoview | |
