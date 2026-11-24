# M055 · Primes and products: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's divisibility `∣` on `ℕ`, primes
`Nat.Prime`, Euclid's lemma `Nat.Prime.dvd_mul`, and `pow_two`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`exact`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" or of a hypothesis (`P : M → Prop`). The step changes only the part inside
  `P (…)`. `G : Prop` is an arbitrary goal that the step leaves alone.
- Placeholders are written as Lean binders. `{M : Type}` is any type. A bracket such as `[Monoid M]` is a
  requirement on `M` (a *type class*). Each entry says which familiar types meet it; `ℕ` meets all of them here.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ` | the natural numbers `0, 1, 2, …` (`Nat`) |
| `p ∣ m` | `p` divides `m`: `∃ c, m = p * c`. Typed `\mid`; it is **not** the bar `\|` |
| `Nat.Prime p` | `p` is prime: `p ≥ 2` and its only divisors are `1` and `p`. You may write it `p.Prime` |
| `hp.dvd_mul` | dot notation: `Nat.Prime.dvd_mul hp`, because `hp : Nat.Prime p` |
| `a ^ 2` | `a` squared (`Monoid.npow`); the exponent is a natural number |
| `a * b * c` | `(a * b) * c`: `*` groups to the left |
| `A ∨ B ∨ C` | `A ∨ (B ∨ C)`: `∨` groups to the right |
| `h✝` | an older hypothesis named `h`, shadowed by a newer `h`; you can no longer name it |
| `case inl`, `case inr` | the goals for the left and the right side of an `∨` after `rcases` |

---

## Part 1 · `prime_dvd_sq`

Statement: if a prime `p` divides `a ^ 2`, then `p` divides `a`. Write `a ^ 2` as `a * a`, apply Euclid's
lemma, and both cases are `p ∣ a`.

**R1 · `rw [pow_two] at h`** changes the **context**: the hypothesis `h` is rewritten, the goal is not. The
lemma is `pow_two a : a ^ 2 = a * a` (`sq` is the same lemma). Placeholders: `{M : Type} [Monoid M] (a : M)`
(`M` has an associative `*` with `1`; `ℕ`, `ℤ`, `ℝ` qualify), `(P : M → Prop) (G : Prop)`.

| Before | After |
|---|---|
| `h : P (a ^ 2) ⊢ G` | `h : P (a * a) ⊢ G` |

**R2 · `Nat.Prime.dvd_mul`** (Euclid's lemma) changes the **context** when used as
`have h' := hp.dvd_mul.mp h`. The lemma is `Nat.Prime.dvd_mul : p.Prime → (p ∣ m * n ↔ p ∣ m ∨ p ∣ n)`, with
`p m n` implicit. `hp.dvd_mul` is the `↔`; `.mp` is its left-to-right direction (`Iff.mp`). Placeholders:
`(p m n : ℕ) (hp : p.Prime) (h : p ∣ m * n)`.

| Before | After |
|---|---|
| `h : p ∣ m * n ⊢ G` | `h' : p ∣ m ∨ p ∣ n ⊢ G` |

**R3 · `rcases h with h | h`** changes the **goal list and the context**: a goal with `h : A ∨ B` becomes
two goals, one with `h : A` and one with `h : B`. You may give it a term instead of a name:
`rcases hp.dvd_mul.mp h with h | h` does R2 and R3 in one line (then the old `h` shows as `h✝`).
Placeholders: `(A B G : Prop)`. Close both goals at once with `<;> exact h` when they look the same.

| Before | After |
|---|---|
| `h : A ∨ B ⊢ G` | `h : A ⊢ G`, `h : B ⊢ G` |

---

## Part 2 · `prime_sq_dvd_sq`

Statement: if a prime `p` divides `a ^ 2`, then `p ^ 2` divides `a ^ 2`. Get `p ∣ a` from Part 1, write both
squares as products, and multiply the divisibility by itself.

**R4 · `have ha := thm args`** changes the **context**. A theorem proved earlier in the file is a function:
apply it to its explicit arguments, in order, and you get its conclusion as a hypothesis. For
`prime_dvd_sq (p a : ℕ) (hp : p.Prime) (h : p ∣ a ^ 2)` the arguments are `p a hp h`. Placeholders:
`(T U : ℕ → Prop) (thm : ∀ n, T n → U n) (n : ℕ) (hn : T n)`.

| Before | After |
|---|---|
| `hn : T n ⊢ G` | `hu : U n ⊢ G` |

**R5 · `rw [pow_two]` on the goal** changes the **goal**, but only for **one base**. `rw` matches `?a ^ 2`
against the first square it finds, fixes `?a := x`, and rewrites every `x ^ 2`; `y ^ 2` is left alone.
Write `rw [pow_two, pow_two]`. Placeholders: `{M : Type} [Monoid M] (x y : M) (P : M → M → Prop)`.

| Before | After `rw [pow_two]` | After the second `rw [pow_two]` |
|---|---|---|
| `⊢ P (x ^ 2) (y ^ 2)` | `⊢ P (x * x) (y ^ 2)` | `⊢ P (x * x) (y * y)` |

**R6 · `mul_dvd_mul`** **closes** the goal with `exact mul_dvd_mul hab hcd`. The lemma is
`mul_dvd_mul : a ∣ b → c ∣ d → a * c ∣ b * d`. Placeholders: `{α : Type} [CommSemigroup α] (a b c d : α)`
(`α` has an associative, commutative `*`; `ℕ` and `ℤ` qualify), `(hab : a ∣ b) (hcd : c ∣ d)`. Nothing stops
`hab` and `hcd` from being the same hypothesis.

| Before | After |
|---|---|
| `⊢ a * c ∣ b * d` | no goals |

**W2.** `p ^ 2 ∣ a * b` from `ha : p ∣ a`, `hb : p ∣ b`: R5 turns the goal into `p * p ∣ a * b`, then R6
closes it.

```lean-goal
⊢ p ^ 2 ∣ a * b
⊢ p * p ∣ a * b
```

---

## Part 3 · `prime_dvd_three`

Statement: if a prime `p` divides `a * b * c`, it divides one of the three factors. `a * b * c` is
`(a * b) * c`, so Euclid's lemma (R2) first gives `p ∣ a * b ∨ p ∣ c`; the first case needs Euclid's lemma
again. That is three goals, each closed by choosing the right side of `A ∨ B ∨ C`.

**R7 · `Or.inl`, `Or.inr`** **close** a disjunction from a proof of one side: `Or.inl : A → A ∨ B` and
`Or.inr : B → A ∨ B`. Since `A ∨ B ∨ C` is `A ∨ (B ∨ C)`, the three sides are `Or.inl ha`,
`Or.inr (Or.inl hb)` and `Or.inr (Or.inr hc)`. Placeholders: `(A B C : Prop)`. The tactics `left` and
`right` do the same one layer at a time.

| Before | After |
|---|---|
| `ha : A ⊢ A ∨ B ∨ C` | no goals (`exact Or.inl ha`) |
| `hb : B ⊢ A ∨ B ∨ C` | no goals (`exact Or.inr (Or.inl hb)`) |
| `hc : C ⊢ A ∨ B ∨ C` | no goals (`exact Or.inr (Or.inr hc)`) |

**W1.** Euclid's lemma and a split in one line (R2 + R3), then each branch into the other side (R7):

```lean-goal
⊢ p ∣ b ∨ p ∣ a
```

after `rcases hp.dvd_mul.mp h with h | h` gives `case inl` with `h : p ∣ a` and `case inr` with `h : p ∣ b`;
`Or.inr h` and `Or.inl h` close them. Use `·` to focus each case (TACTIC_STATES, "Structure").

**W3.** Ruling a branch out: `absurd : A → ¬A → B` proves any goal from `A` and `¬A`. With `hb : ¬p ∣ b`,
the `case inr` goal `h : p ∣ b ⊢ p ∣ a` closes by `exact absurd h hb`.

---

## Traps

- `∣` (`\mid`) is divisibility; `|` is the bar used in `rcases … with h | h` and in `match`. They look alike.
- `rw [pow_two]` rewrites only one base (R5). In `p ^ 2 ∣ a ^ 2` you need `rw [pow_two, pow_two]`.
- `rw [pow_two] at h` changes `h`, not the goal (R1). Without `at h`, `rw` looks in the goal and fails if there
  is no square there.
- `a * b * c` is `(a * b) * c`: the first use of Euclid's lemma splits off `c`, not `a`.
- `A ∨ B ∨ C` is `A ∨ (B ∨ C)`: `p ∣ b` is `Or.inr (Or.inl h)`, not `Or.inl (Or.inr h)`.
- After `rcases … with h | h` the new `h` hides the old one (`h✝`). Pick other names (`hab | hc`) when you
  still need both.
- `Nat.Prime.dvd_of_dvd_pow`, `Prime.dvd_of_dvd_pow` and `Nat.Prime.dvd_mul_of_dvd_left` are banned: they
  would do Part 1 in one step.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `a ^ 2 → a * a` in a hypothesis | `rw [pow_two] at h` | R1 |
| Euclid: `p ∣ m * n → p ∣ m ∨ p ∣ n` | `hp.dvd_mul.mp h` | R2 |
| case split on `h : A ∨ B` | `rcases h with h \| h` | R3 |
| both cases identical | `rcases … with h \| h <;> exact h` | R3 |
| use an earlier theorem | `have ha := thm p a hp h` | R4 |
| `x ^ 2`, `y ^ 2` → products in the goal | `rw [pow_two, pow_two]` | R5 |
| `a * c ∣ b * d` from `a ∣ b`, `c ∣ d` | `exact mul_dvd_mul hab hcd` | R6 |
| first / second / third of `A ∨ B ∨ C` | `Or.inl h` / `Or.inr (Or.inl h)` / `Or.inr (Or.inr h)` | R7 |
| contradictory branch `h : A`, `hn : ¬A` | `exact absurd h hn` | W3 |
| see the state | infoview | |
