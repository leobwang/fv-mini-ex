# E043 · Primes by norm_num: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `have` (E021), `exact`, `rcases` on `∨` (E006), `omega`
(E011), dot notation and implicit arguments (E023).
**New here:** Mathlib's `Nat.Prime`, `Odd` and `∣`; `norm_num`'s primality check for numerals; three library
lemmas about a symbolic prime `p`, called by dot notation on its proof `hp`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P`, `G : Prop` are "the rest of your goal". A hypothesis `g` in an example only finishes it: it shows what
  the goal or context became.
- Placeholders are written as Lean binders: `(q a : ℕ)` are natural numbers, `(hq : Nat.Prime q)` a proof that
  `q` is prime, `(A B : Prop)` arbitrary statements.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ` | natural numbers `0, 1, 2, …` |
| `Nat.Prime p` | `p` is prime: `2 ≤ p` and its only divisors are `1` and `p`. You may write it `p.Prime`; Lean always prints `Nat.Prime p` |
| `¬Nat.Prime 91` | `91` is not prime (`¬A` is `A → False`) |
| `a ∣ b` | `a` divides `b`: `∃ c, b = a * c`. The bar is `\mid`, not the keyboard `\|` |
| `Odd p` | `∃ m, p = 2 * m + 1`. Mathlib's definition; it works in any type with `+`, `*`, `1` (`ℕ`, `ℤ`, `ℝ`), here `ℕ` |
| `p ≠ 2` | `p = 2 → False` |
| `hp.two_le` | dot notation: `Nat.Prime.two_le hp`, because `hp : Nat.Prime p` |
| `case inl`, `case inr` | the two goals of `rcases h with h1 \| h1`: left and right side of the `∨` |

---

## Part 1 · `prime_97`

Statement: `Nat.Prime 97`. A concrete numeral: let `norm_num` check it.

**R1 · `norm_num`** **closes** a goal `Nat.Prime n` for a numeral `n`. Mathlib's `norm_num` has a primality
extension: it checks that no `d` with `2 ≤ d` and `d * d ≤ n` divides `n`, and builds the proof.

| Before | After |
|---|---|
| `⊢ Nat.Prime 13` | no goals |

## Part 2 · `not_prime_91`

Statement: `¬ Nat.Prime 91`. Concrete again; `91 = 7 * 13`.

**R2 · `norm_num`** **closes** a goal `¬Nat.Prime n` for a composite numeral `n`: it finds a factor and uses it.

| Before | After |
|---|---|
| `⊢ ¬Nat.Prime 21` | no goals |

## Part 3 · `prime_ge_two`

Statement: every prime `p` satisfies `2 ≤ p`. `p` is a variable now, so `norm_num` has nothing to compute; use
the library lemma. A proof of the goal can be the lemma applied to `hp`, written in term mode or after `exact`.

**R3 · `Nat.Prime.two_le`** changes the **context** (used with `have`). Statement:
`Nat.Prime.two_le : Nat.Prime p → 2 ≤ p`, with `{p : ℕ}` implicit. Dot notation: `hq.two_le` is
`Nat.Prime.two_le hq`. Placeholders: `(q : ℕ) (hq : Nat.Prime q) (P : Prop)`.

| Before | After `have h := hq.two_le` |
|---|---|
| `hq : Nat.Prime q ⊢ P` | `h : 2 ≤ q ⊢ P` |

**W1.** From `h : 2 ≤ q`, `omega` (R7) proves `q ≠ 0 ∧ q ≠ 1`:

```lean-goal
⊢ q ≠ 0 ∧ q ≠ 1
```

## Part 4 · `prime_odd`

Statement: a prime `p ≠ 2` is odd. Again one library lemma, which takes the proof of `p ≠ 2` as its second
argument.

**R4 · `Nat.Prime.odd_of_ne_two`** changes the **context**. Statement:
`Nat.Prime.odd_of_ne_two : Nat.Prime p → p ≠ 2 → Odd p`. Placeholders:
`(q : ℕ) (hq : Nat.Prime q) (hne : q ≠ 2) (P : Prop)`.

| Before | After `have h := hq.odd_of_ne_two hne` |
|---|---|
| `hne : q ≠ 2 ⊢ P` | `h : Odd q ⊢ P` |

## Part 5 · `three_dvd_prime`

Statement: if `3 ∣ p` and `p` is prime, then `p = 3`. A divisor of a prime is `1` or the prime itself (R5);
`3 = 1` is impossible and `3 = p` is the goal turned around (R6, R7).

**R5 · `Nat.Prime.eq_one_or_self_of_dvd`** changes the **context**. Statement:
`Nat.Prime.eq_one_or_self_of_dvd : Nat.Prime p → ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p`. After `hq.` come the
divisor `a` (explicit) and the proof of `a ∣ q`. Placeholders: `(q a : ℕ) (hq : Nat.Prime q) (ha : a ∣ q)`.

| Before | After `have h := hq.eq_one_or_self_of_dvd a ha` |
|---|---|
| `ha : a ∣ q ⊢ P` | `h : a = 1 ∨ a = q ⊢ P` |

**W2.** The proof of `Nat.Prime 7` can come from R1 inline, and dot notation works on it:
`exact (by norm_num : Nat.Prime 7).eq_one_or_self_of_dvd a ha` closes

```lean-goal
⊢ a = 1 ∨ a = 7
```

**R6 · `rcases h with h1 | h1`** changes the **goal list and the context**: one goal per side of the `∨`, both
with the old goal. `rcases` also takes a term directly: `rcases hq.eq_one_or_self_of_dvd a ha with h1 | h1`
skips the `have`. Placeholders: `(A B G : Prop) (h : A ∨ B)`.

| Before | After |
|---|---|
| `h : A ∨ B ⊢ G` | `h1 : A ⊢ G`, `h1 : B ⊢ G` |

**R7 · `omega`** **closes** a goal of linear arithmetic over `ℕ`/`ℤ`, using the hypotheses. A false numeral
hypothesis such as `5 = 1` proves any such goal, and `5 = n` proves `n = 5`.

| Before | After |
|---|---|
| `h : 5 = 1 ⊢ n = 5` | no goals |
| `h : 5 = n ⊢ n = 5` | no goals |

In the exercise the two branches are `h3 : 3 = 1 ⊢ p = 3` and `h3 : 3 = p ⊢ p = 3`.

---

## Traps

- `norm_num` decides `Nat.Prime 97` only because `97` is a numeral. On `Nat.Prime p` with a variable `p` it
  does nothing useful: use the lemmas R3–R5.
- The second branch of R5 is `3 = p`, not `p = 3`: `exact h3` fails. Use `omega` or `h3.symm`; or the pattern `rcases … with
  h3 | rfl`, which substitutes `3` for `p` and leaves `⊢ 3 = 3` for `rfl`.
- The divisor in `eq_one_or_self_of_dvd` is explicit: `hp.eq_one_or_self_of_dvd 3 h`, not
  `hp.eq_one_or_self_of_dvd h`.
- `∣` is `\mid`. The ASCII `|` is the pattern separator in `rcases … with h1 | h1` and does not parse as
  divisibility.
- Dot notation needs the hypothesis's type to be literally `Nat.Prime p`: `hp.two_le` works, `p.two_le` does
  not (`p : ℕ`, so Lean looks for `Nat.two_le`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `Nat.Prime n` for a numeral `n` | `norm_num` | R1 |
| `¬ Nat.Prime n` for a numeral `n` | `norm_num` | R2 |
| `2 ≤ p` from `hp : Nat.Prime p` | `hp.two_le` | R3 |
| `Odd p` from `hp`, `h : p ≠ 2` | `hp.odd_of_ne_two h` | R4 |
| `a = 1 ∨ a = p` from `hp`, `h : a ∣ p` | `hp.eq_one_or_self_of_dvd a h` | R5 |
| split an `∨` | `rcases h with h1 \| h1` | R6 |
| finish linear `ℕ` goals, flip `3 = p` | `omega` | R7 |
| a lemma about a concrete prime | `(by norm_num : Nat.Prime 7).lemma …` | W2 |
| see the state | infoview | |
