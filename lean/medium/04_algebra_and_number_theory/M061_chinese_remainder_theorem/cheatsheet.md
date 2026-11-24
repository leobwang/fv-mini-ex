# M061 · Chinese remainder theorem: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `∃`, `∧`, anonymous constructors `⟨_, _⟩`, `obtain`,
`refine`, `exact`, `rw`, `<;>`, `·`. **New here:** Mathlib's integer congruences `Int.ModEq`
(`x ≡ a [ZMOD m]`), `IsCoprime`, divisibility `∣` on `ℤ` as an existential, and the
`linear_combination` tactic.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P`, `Q` are "the rest of your goal" (`P : α → Prop`); `G : Prop` is an arbitrary goal.
- Placeholders are written as Lean binders. `{R : Type}` is any type. A bracket such as `[CommRing R]` is a
  requirement on `R` (a *type class*): `[CommSemiring R]` means `R` has commutative `+`, `*`, `0`, `1`
  (`ℕ`, `ℤ`, `ℝ` qualify); `[CommRing R]` adds subtraction (`ℤ`, `ℚ`, `ℝ`, `ℂ` qualify, `ℕ` does not).
- `inst✝ : CommRing R` in the infoview is that bracket, an unnamed instance hypothesis.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℤ` | the integers (`Int`) |
| `x ≡ a [ZMOD m]` | `Int.ModEq m x a`, defined as `x % m = a % m`: `x` and `a` have the same remainder mod `m` |
| `IsCoprime m n` | `∃ u v, u * m + v * n = 1` (Bézout coefficients `u, v`); over `ℤ` this is `gcd m n = 1` |
| `m ∣ k` | `m` divides `k` (typed `\mid`, not the bar `\|`); by definition `∃ c, k = m * c` |
| `m ∣ y - x` | `m ∣ (y - x)`: `-` binds tighter than `∣` |
| `m * n ∣ y - x` | `(m * n) ∣ (y - x)` |
| `case refine_1`, `case refine_2` | the goals left by the first and second `?_` of a `refine` |
| `inst✝ : CommRing R` | an anonymous type-class hypothesis (see above) |

The math. With `u * m + v * n = 1`: `v * n ≡ 1 (mod m)` and `v * n ≡ 0 (mod n)`, and symmetrically
`u * m ≡ 0 (mod m)`, `u * m ≡ 1 (mod n)`. So `x₀ = a * (v * n) + b * (u * m)` is `≡ a (mod m)` and
`≡ b (mod n)`. For uniqueness, if `m ∣ d` and `n ∣ d` with `d = y - x`, then
`d = d * (u * m + v * n) = u * m * d + v * n * d`, and each term is a multiple of `m * n`.

---

## Part 1 · `crt_exists`

Statement: for `m n : ℤ` with `IsCoprime m n` and any `a b : ℤ`, there is `x` with `x ≡ a [ZMOD m]` and
`x ≡ b [ZMOD n]`.

**R1 · `obtain ⟨u, v, huv⟩ := h`** changes the **context**: the hypothesis `h : IsCoprime m n` is replaced by
its Bézout coefficients `u v` and the equation `huv`. It works because `IsCoprime m n` is *defined* as
`∃ u v, u * m + v * n = 1`. Placeholders: `{R : Type} [CommSemiring R] (m n : R) (G : Prop)`.

| Before | After |
|---|---|
| `h : IsCoprime m n ⊢ G` | `u v : R, huv : u * m + v * n = 1 ⊢ G` |

**R2 · `refine ⟨x₀, ?_, ?_⟩`** changes the **goal list**: it picks the witness `x₀` for `∃ x` and leaves one
goal per conjunct (`∃ x, P x ∧ Q x` is `∃ x, (P x ∧ Q x)`, and the anonymous constructor flattens the
nesting). Placeholders: `{α : Type} (P Q : α → Prop) (x₀ : α)`. In the exercise `x₀` is an expression
in `a, b, u, v, m, n`.

| Before | After |
|---|---|
| `⊢ ∃ x, P x ∧ Q x` | `⊢ P x₀`, `⊢ Q x₀` |

**R3 · `rw [Int.modEq_iff_dvd]`** changes the **goal**. The lemma is
`Int.modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a`. Note the order: **right side minus left side**.
Placeholders: `(n a b : ℤ)`. After R2 use `<;> rw [Int.modEq_iff_dvd]` to rewrite both goals at once.

| Before | After |
|---|---|
| `⊢ a ≡ b [ZMOD n]` | `⊢ n ∣ b - a` |

**R4 · `refine ⟨c, ?_⟩`** (or `exact ⟨c, proof⟩`) changes the **goal**: `a ∣ k` is defined as
`∃ c, k = a * c`, so giving the witness `c` leaves the equation. The divisor stands **on the left** of the
product. Placeholders: `{R : Type} [CommRing R] (a k c : R)`.

| Before | After |
|---|---|
| `⊢ a ∣ k` | `⊢ k = a * c` |

**R5 · `linear_combination e₁ * h₁ + … + eₖ * hₖ`** **closes** an equation goal `L = R'` from equation
hypotheses `hᵢ : Lᵢ = Rᵢ` and coefficients `eᵢ` (any terms). It checks with `ring` that
`L - R' - Σ eᵢ * (Lᵢ - Rᵢ) = 0`. Placeholders: `{R : Type} [CommRing R] (a b c d : R)`,
`h₁ : a = b`, `h₂ : c = d`.

| Before | After |
|---|---|
| `⊢ a + 2 * c = b + 2 * d` | no goals (`linear_combination h₁ + 2 * h₂`) |

*Finding the coefficients.* First write `linear_combination` with no argument (all `eᵢ = 0`). It fails
with `ring failed, ring expressions not equal` and prints the remainder `L - R' - Σ eᵢ * (Lᵢ - Rᵢ)`,
expanded, as a goal `… = 0`. In Part 1 the only hypothesis is `huv : u * m + v * n = 1`, so you need one
`e` with `L - R' = e * (u * m + v * n - 1)`. The terms of the printed remainder that contain neither
`u` nor `v` must equal `-e`, so `e` is minus those terms. Rerun with `e * huv`: if the remainder is not
`0`, it is printed again; adjust and repeat. In Part 2 the coefficients of `hs` and `ht` are given by the
substitution in its skeleton, and `e` is found the same way.

### Worked combination (W1, not the exercise's objects)

**W1.** `∃ x : ℤ, x ≡ 2 [ZMOD 3] ∧ x ≡ 3 [ZMOD 5]` with `x₀ = 8`: after
`refine ⟨8, ?_, ?_⟩ <;> rw [Int.modEq_iff_dvd]` (R2, R3) the two goals are

```lean-goal
⊢ 3 ∣ 2 - 8
⊢ 5 ∣ 3 - 8
```

and `exact ⟨-2, by norm_num⟩`, `exact ⟨-1, by norm_num⟩` close them (R4; `2 - 8 = 3 * (-2)`).

---

## Part 2 · `crt_unique`

Statement: for coprime `m n : ℤ`, if `x ≡ y [ZMOD m]` and `x ≡ y [ZMOD n]` then `x ≡ y [ZMOD m * n]`.
Unpack Bézout (R1), turn all three congruences into divisibilities at once (R6), unpack the two
hypotheses (R7), and give the witness for `m * n ∣ y - x` (R4, R5).

**R6 · `rw [Int.modEq_iff_dvd] at *`** changes the **goal and the context**: `at *` rewrites with R3's
lemma in every hypothesis and in the goal (it fails only if it rewrites nothing anywhere).
Placeholders: `(m k x y : ℤ)`, `hm : x ≡ y [ZMOD m]`.

| Before | After |
|---|---|
| `hm : x ≡ y [ZMOD m] ⊢ x ≡ y [ZMOD k]` | `hm : m ∣ y - x ⊢ k ∣ y - x` |

**R7 · `obtain ⟨s, hs⟩ := hdvd`** changes the **context**: a divisibility hypothesis `hdvd : a ∣ k` is
replaced by its quotient `s` and the equation `hs : k = a * s`. Placeholders:
`{R : Type} [CommRing R] (a k : R) (G : Prop)`.

| Before | After |
|---|---|
| `hdvd : a ∣ k ⊢ G` | `s : R, hs : k = a * s ⊢ G` |

Then R4 with the witness for `m * n` and R5 with **three** hypotheses: `huv`, and the two equations from R7.

### Worked combinations (W2, W3, not the exercise's objects)

**W2: `3 ∣ a` and `5 ∣ a` give `15 ∣ a`,** using `2 * 3 + (-1) * 5 = 1`. After R7 twice:

```lean-goal
⊢ 15 ∣ a
```

with `hs : a = 3 * s` and `ht : a = 5 * t`. Since `a = 2 * 3 * a - 5 * a`, replace `a` by `5 * t` in the
first term and by `3 * s` in the second: `a = 15 * (2 * t - s)`. So the witness is `2 * t - s`, and
`linear_combination (-5) * hs + 6 * ht` closes `a = 15 * (2 * t - s)` (R4, R5).

**W3: multiplying a congruence by `k`.** From `h : a ≡ b [ZMOD m]` to `k * a ≡ k * b [ZMOD m]`, one step at a
time: R6, R7, R4 with witness `k * s`, then R5.

```lean-goal
⊢ m ∣ k * b - k * a
⊢ k * b - k * a = m * (k * s)
```

The first line is the goal after R6 (and R7, which changes only the context: `hs : b - a = m * s`); the
second after `refine ⟨k * s, ?_⟩`; `linear_combination k * hs` closes it.

---

## Traps

- `Int.modEq_iff_dvd` gives `n ∣ b - a`, **not** `n ∣ a - b`: for `x ≡ a [ZMOD m]` the goal is
  `m ∣ a - x`. Your witness and coefficient signs depend on it.
- `a ∣ k` unfolds to `k = a * c` with the divisor first. A witness proof of `k = c * a` does not fit.
- `rw [...] at *` rewrites the goal **and** every hypothesis it matches, and keeps their names: after R6,
  `hm` and `hn` are divisibilities, no longer congruences, so unpack them with R7, not as congruences.
- `linear_combination` only closes the goal; it does not leave a simpler one. When it fails, read the
  remainder it prints and fix the coefficients.
- Search tactics (`exact?`, `apply?`, `rw?`, `hint`, `try?`) are fine for exploring, but they are on the
  `BANNED:` line: they close goals with banned library lemmas such as `Int.modEq_and_modEq_iff_modEq_mul`,
  so they cannot stay in the submitted proof.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| Bézout coefficients from `IsCoprime m n` | `obtain ⟨u, v, huv⟩ := h` | R1 |
| prove `∃ x, P x ∧ Q x` | `refine ⟨x₀, ?_, ?_⟩` | R2 |
| congruence goal → divisibility | `rw [Int.modEq_iff_dvd]` (gives `n ∣ b - a`) | R3 |
| same in every hypothesis and the goal | `rw [Int.modEq_iff_dvd] at *` | R6 |
| prove `a ∣ k` | `refine ⟨c, ?_⟩` / `exact ⟨c, by …⟩` (goal `k = a * c`) | R4 |
| use `hdvd : a ∣ k` | `obtain ⟨s, hs⟩ := hdvd` (`hs : k = a * s`) | R7 |
| equation from equations | `linear_combination e₁ * h₁ + e₂ * h₂` | R5 |
| run a tactic on all goals | `t <;> u` | TACTIC_STATES |
| see the state | infoview | |
