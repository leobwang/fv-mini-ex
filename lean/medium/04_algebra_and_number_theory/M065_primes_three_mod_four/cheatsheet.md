# M065 · Infinitely many primes ≡ 3 mod 4: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's natural-number API: `%` residues,
divisibility `∣`, `Nat.Prime`, `Nat.factorial`; the tactics `interval_cases`, `simp_all`, `omega`,
`by_contra`, `push Not`; and truncated subtraction on `ℕ`.

## How to read an entry

Each entry is one tactic or one lemma (used with `rw`, or as a term in `have`). It says what changes
(**goal**, **context**, or **goal list**), gives the lemma's statement, lists the placeholders with their
types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses the step uses or
  changes. A `have` keeps the hypotheses it uses, so its After cell lists only the new one.
- `P` is "the rest of your goal" (`P : ℕ → Prop`). The step changes only the part inside `P (…)`.
- `G : Prop` is an arbitrary goal; a hypothesis `g : … → G` is there only to finish the example.
- Placeholders are written as Lean binders. `{α : Type}` is any type; a bracket such as `[CommMonoid α]`
  is a requirement on `α` (a *type class*); each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ` | the natural numbers `0, 1, 2, …` (`Nat`) |
| `a % n` | remainder of `a` on division by `n` (`a mod n`); `a % 0 = a` |
| `a * b % n` | `(a * b) % n`: `*` and `%` have the same precedence and group to the left |
| `a ≡ 3 mod 4` (comments only) | `a % 4 = 3`; Lean's goals here always use `%` |
| `m - n` on `ℕ` | **truncated** subtraction: `m - n = 0` when `n ≥ m`, so `0 - 1 = 0` |
| `m ∣ n` | `m` divides `n`: `∃ c, n = m * c` (typed `\mid`, not the keyboard bar `\|`) |
| `Nat.Prime p`, `p.Prime` | `p` is prime (`p ≥ 2`, only divisors `1` and `p`); the two spellings are the same |
| `n.factorial` | `n! = 1 · 2 ⋯ n`, with `0! = 1` (`Nat.factorial n`) |
| `¬A` | `A → False` |
| `a ≠ b` | `¬(a = b)`, i.e. `a = b → False` |
| `hp.pos`, `hp.one_lt` | dot notation: `Nat.Prime.pos hp`, `Nat.Prime.one_lt hp`, because `hp : Nat.Prime p` |
| `h.mp` for `h : A ↔ B` | the direction `A → B` (`.mpr` is `B → A`) |
| `case «2».«3»` | after two `interval_cases`, the goal with first value `2` and second value `3` |
| `inst✝ : CommMonoid α` | an anonymous type-class hypothesis from a `[…]` binder |

---

## Part 1 · `mod4_of_mul`

Statement: for `a b : ℕ`, if `a * b % 4 = 3` then `a % 4 = 3 ∨ b % 4 = 3`. Since
$ab \bmod 4$ depends only on $a \bmod 4$ and $b \bmod 4$, this is a check of the $4 \times 4 = 16$
residue pairs: in each, either the hypothesis is false or one disjunct is `3 = 3`.

**R1 · `rw [Nat.mul_mod] at h`** changes the **context**: it rewrites the hypothesis `h`, not the goal.
The lemma is `Nat.mul_mod : a * b % n = a % n * (b % n) % n`. Placeholders: `(a b n : ℕ)`,
`(P : ℕ → Prop)`.

| Before | After |
|---|---|
| `h : P (a * b % n) ⊢ P (a % n * (b % n) % n)` | `h : P (a % n * (b % n) % n) ⊢ P (a % n * (b % n) % n)` |

**R2 · `have ha : a % n < n := Nat.mod_lt a hn`** changes the **context**: it adds the bound that
`interval_cases` (R3) needs. The lemma is `Nat.mod_lt : ∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y`; `y` is
implicit (inferred from the goal you state). With a numeral `n = 4`, write `Nat.mod_lt a (by norm_num)`.
Placeholders: `(a n : ℕ) (hn : 0 < n)`.

| Before | After |
|---|---|
| `hn : 0 < n ⊢ G` | `ha : a % n < n ⊢ G` |

**R3 · `interval_cases e`** changes the **goal list and the context**. With a bound `e < k` in the context
(and `0 ≤ e`, automatic on `ℕ`), it makes one goal per value `0, …, k - 1` and replaces `e` by that numeral
**everywhere**, in the goal and in every hypothesis. `e` may be a compound term such as `a % 3`. The bound
itself becomes e.g. `hr : 1 < 3`. Placeholders: `(a : ℕ) (P Q : ℕ → Prop)`, bound `hr : a % 3 < 3`.

| Before | After |
|---|---|
| `hq : Q (a % 3) ⊢ P (a % 3)` | `hq : Q 0 ⊢ P 0`, `hq : Q 1 ⊢ P 1`, `hq : Q 2 ⊢ P 2` |

Two in a row, `interval_cases a % 4 <;> interval_cases b % 4`, give all 16 pairs; the residue form of `h`
from R1 becomes closed arithmetic such as `h : 2 * 3 % 4 = 3`.

**R4 · `simp_all`** **closes** the goal (or fails). It simplifies every hypothesis and the goal with each
other and with `simp`'s lemmas, which evaluate numeral arithmetic. After R3 each goal is one of two kinds:
a hypothesis evaluates to `False` (here `2 * 3 % 5 = 4` is `1 = 4`), so the goal holds vacuously; or the
goal evaluates to `True` (`3 = 3` is a disjunct). Placeholders: `(G : Prop)`.

| Before | After |
|---|---|
| `h : 2 * 3 % 5 = 4 ⊢ G` | no goals |
| `⊢ 2 = 3 ∨ 3 = 3` | no goals |

**W1** in the guide runs R1–R4 for the residue statement mod 3 (`a * b % 3 = 2 → a % 3 = 2 ∨ b % 3 = 2`):

```lean-goal
⊢ a % 3 = 2 ∨ b % 3 = 2
```

with `h : a % 3 * (b % 3) % 3 = 2`, `ha : a % 3 < 3`, `hb : b % 3 < 3` in the context, then one line
`interval_cases a % 3 <;> interval_cases b % 3 <;> simp_all`.

---

## Given · `exists_prime_three`

Already proved and frozen: every `m` with `m % 4 = 3` has a prime factor `p` with `p % 4 = 3`. Its proof
is a strong induction that calls `mod4_of_mul`, so `./check` counts it as open until Part 1 is done. You
only **use** it, in Part 2, as a term:
`exists_prime_three m hm : ∃ p, Nat.Prime p ∧ p ∣ m ∧ p % 4 = 3`.

---

## Part 2 · `primes_three_mod_four`

Statement: for every `n : ℕ` there is `p` with `n < p`, `Nat.Prime p` and `p % 4 = 3`. Euclid's argument:
$N = 4 \cdot n! - 1$ satisfies $N \bmod 4 = 3$, so the given lemma yields a prime $p \mid N$ with
$p \equiv 3 \pmod 4$. If $p \le n$ then $p \mid n!$, so $p \mid 4 \cdot n!$, so $p \mid 4 \cdot n! - N = 1$,
contradicting $p > 1$.

**R5 · `have hf := Nat.factorial_pos n`** changes the **context**. The lemma is
`Nat.factorial_pos : ∀ (n : ℕ), 0 < n.factorial`. `have hf := e` with no type takes the type of `e`.
You need `hf` because `omega` (R6) cannot know `n.factorial ≥ 1` on its own. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ G` | `hf : 0 < n.factorial ⊢ G` |

**R6 · `omega`** **closes** a goal of linear arithmetic over `ℕ` or `ℤ` (`+`, `-`, `*` by numerals, `%` and
`/` by numerals, `<`, `≤`, `=`, `∧`, `∨`, `¬`), using the hypotheses of that kind in the context. It knows
truncated subtraction. Any other term, such as `n.factorial`, is an opaque unknown, so facts about it
(`hf`) must be in the context. Use it as `(by omega)` for the argument `hm : m % 4 = 3` of the given lemma.
Placeholders: `(n : ℕ) (hf : 0 < n.factorial)`.

| Before | After |
|---|---|
| `hf : 0 < n.factorial ⊢ (6 * n.factorial - 1) % 6 = 5` | no goals |
| `hf : 0 < n.factorial ⊢ 6 * n.factorial - (6 * n.factorial - 1) = 1` | no goals |

**R7 · `obtain ⟨p, hA, hB, hC⟩ := e`** changes the **context**: an `∃` with an `∧` chain becomes the witness
and one hypothesis per conjunct. `e` may be a lemma application, `exists_prime_three m (by omega)`.
Placeholders: `{α : Type} (A B C : α → Prop)`, `e : ∃ p, A p ∧ B p ∧ C p`.

| Before | After |
|---|---|
| `⊢ G` (with `e` in the context) | `p : α, hA : A p, hB : B p, hC : C p ⊢ G` (`e` is gone) |

**R8 · `refine ⟨p, ?_, hB, hC⟩`** changes the **goal**: it gives the witness `p` and the conjuncts you
already have, and leaves the one marked `?_`. Placeholders as in R7, with `p : α`.

| Before | After |
|---|---|
| `⊢ ∃ x, A x ∧ B x ∧ C x` | `⊢ A p` |

**R9 · `by_contra hle`** changes the **goal and the context**: the goal becomes `False`, and its negation is
added as `hle`. Placeholders: `(n p : ℕ)`.

| Before | After |
|---|---|
| `⊢ n < p` | `hle : ¬n < p ⊢ False` |

**R10 · `push Not at hle`** changes the **context**: it pushes `¬` inward through `hle` and turns
`¬n < p` into `p ≤ n` (also `¬a ≤ b` → `b < a`, `¬∀` → `∃ ¬`, …). It is Mathlib's newer spelling of
`push_neg`. Placeholders: `(n p : ℕ)`.

| Before | After |
|---|---|
| `hle : ¬n < p ⊢ G` | `hle : p ≤ n ⊢ G` |

**R11 · `hp.pos`** (`Nat.Prime.pos : Nat.Prime p → 0 < p`) changes the **context** when used in a `have`.
It supplies the `0 < m` argument of R12. Placeholders: `(p : ℕ) (hp : Nat.Prime p)`.

| Before | After |
|---|---|
| `hp : Nat.Prime p ⊢ G` | `h0 : 0 < p ⊢ G` |

**R12 · `Nat.dvd_factorial`** changes the **context** when used in a `have`. The lemma is
`Nat.dvd_factorial : 0 < m → m ≤ n → m ∣ n.factorial` (`m`, `n` implicit). Placeholders: `(m n : ℕ)`,
`hm : 0 < m`, `hle : m ≤ n`.

| Before | After |
|---|---|
| `hle : m ≤ n ⊢ G` | `hd : m ∣ n.factorial ⊢ G` |

**R13 · `dvd_mul_of_dvd_right`** changes the **context** when used in a `have`. The lemma is
`dvd_mul_of_dvd_right : a ∣ b → ∀ (c : α), a ∣ c * b`: a divisor of `b` divides any multiple `c * b`.
"right" names the side of `b`. Placeholders: `{α : Type} [CommMonoid α] (a b c : α)`; `α` has a commutative
`*`, so `ℕ`, `ℤ`, `ℝ` qualify (Mathlib states the lemma for the weaker `[CommSemigroup α]`: commutative, associative `*`, no `1` needed). Write `dvd_mul_of_dvd_right hab 4` for `a ∣ 4 * b`.

| Before | After |
|---|---|
| `hab : a ∣ b ⊢ G` | `hd : a ∣ c * b ⊢ G` |

**R14 · `Nat.dvd_sub`** changes the **context** when used in a `have`. The lemma is
`Nat.dvd_sub : k ∣ m → k ∣ n → k ∣ m - n` (truncated `-`, no side condition needed). Write
`have h2 := Nat.dvd_sub h₁ h₂` without a type, so Lean spells out `m - n` for you. Placeholders:
`(k m n : ℕ)`, `hm : k ∣ m`, `hn : k ∣ n`.

| Before | After |
|---|---|
| `hn : k ∣ n ⊢ G` | `h2 : k ∣ m - n ⊢ G` |

**R15 · `rw [show a = b by omega] at h`** changes the **context**. `show a = b by tac` builds a proof of
`a = b` on the spot; `rw … at h` replaces `a` by `b` in `h`. On `ℕ`, `2x - (2x - 1) = 1` holds only because
`x ≥ 1`, which `omega` reads from `hx`. Placeholders: `(k x : ℕ) (hx : 0 < x)`.

| Before | After |
|---|---|
| `h : k ∣ 2 * x - (2 * x - 1) ⊢ G` | `h : k ∣ 1 ⊢ G` |

**R16 · `Nat.dvd_one.mp h`** changes the **context** when used in a `have`. The lemma is
`Nat.dvd_one : n ∣ 1 ↔ n = 1`; `.mp` is its `→` direction. Placeholders: `(k : ℕ) (h : k ∣ 1)`.

| Before | After |
|---|---|
| `h : k ∣ 1 ⊢ G` | `h1 : k = 1 ⊢ G` |

**R17 · `hp.one_lt`** (`Nat.Prime.one_lt : Nat.Prime p → 1 < p`) changes the **context** when used in a
`have`. Placeholders: `(p : ℕ) (hp : Nat.Prime p)`.

| Before | After |
|---|---|
| `hp : Nat.Prime p ⊢ G` | `hlt : 1 < p ⊢ G` |

**R18 · `hlt.ne'`** (`LT.lt.ne' : b < a → a ≠ b`) **closes** a `False` goal when applied to an equation:
`hlt : 1 < p` gives `hlt.ne' : p ≠ 1`, which is `p = 1 → False`, so `hlt.ne' h1 : False`. The prime `'`
means the sides are swapped compared to `ne : a < b → a ≠ b`. Placeholders: `(p : ℕ)`.

| Before | After |
|---|---|
| `hlt : 1 < p, h1 : p = 1 ⊢ False` | no goals |

R16–R18 compose into one term: `exact hp.one_lt.ne' (Nat.dvd_one.mp h2)`.

**W2** in the guide runs R5–R12 and R14–R18 for plain Euclid, `∀ n, ∃ p, n < p ∧ Nat.Prime p`, with
`n.factorial + 1` and `Nat.exists_prime_and_dvd : n ≠ 1 → ∃ p, Nat.Prime p ∧ p ∣ n` in place of the given
lemma. Its goal after `by_contra hle; push Not at hle`, and the two divisibility facts it builds:

```lean-goal
⊢ n < p
⊢ False
```

with `hpd : p ∣ n.factorial + 1`, `h1 : p ∣ n.factorial`, then `h2 : p ∣ n.factorial + 1 - n.factorial`,
rewritten by R15 to `h2 : p ∣ 1`. In the exercise the order of the subtraction is reversed: the multiple
`4 * n.factorial` comes first, so `Nat.dvd_sub h1 hpd`.

---

## Traps

- **Truncated subtraction.** `4 * n.factorial - 1` is `0` when `n.factorial = 0`. `omega` proves
  `(4 * n.factorial - 1) % 4 = 3` and `4 * n.factorial - (4 * n.factorial - 1) = 1` only with
  `hf : 0 < n.factorial` (R5) in the context. Put `hf` there **before** the `(by omega)` argument.
- `interval_cases a % 4` fails without the bound `a % 4 < 4` in the context (R2).
- Do `rw [Nat.mul_mod] at h` **before** `interval_cases`: only the residue form `a % 4 * (b % 4) % 4 = 3`
  contains the terms `a % 4`, `b % 4` that `interval_cases` replaces. In `a * b % 4 = 3` they do not occur.
- `t1 ; t2` runs `t2` on the first goal only. After `interval_cases`, chain with `<;>`.
- `Nat.dvd_sub h₁ h₂ : k ∣ m - n` takes the larger number's divisibility first: `h₁ : p ∣ 4 * n.factorial`,
  then `h₂ : p ∣ 4 * n.factorial - 1`. In the other order you get `p ∣ (4 * n! - 1) - 4 * n! = 0`, which is
  useless.
- `dvd_mul_of_dvd_right h 4 : p ∣ 4 * n.factorial` (factor on the left); `dvd_mul_of_dvd_left` gives
  `p ∣ n.factorial * 4`, which does not match `4 * n.factorial`.
- Prove `mod4_of_mul` first: the given `exists_prime_three` uses it, and stays "open" until it is proved.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `a * b % n` → residues, in `h` | `rw [Nat.mul_mod] at h` | R1 |
| bound for a case split | `have ha : a % 4 < 4 := Nat.mod_lt a (by norm_num)` | R2 |
| split on the value of `e < k` | `interval_cases e` | R3 |
| close closed-arithmetic goals | `simp_all` | R4 |
| `0 < n!` | `have hf := Nat.factorial_pos n` | R5 |
| linear ℕ arithmetic, `%` by numerals, truncated `-` | `omega` | R6 |
| unpack `∃ p, A ∧ B ∧ C` | `obtain ⟨p, hA, hB, hC⟩ := e` | R7 |
| give the witness, keep one goal | `refine ⟨p, ?_, hB, hC⟩` | R8 |
| prove `G` by contradiction | `by_contra hle` | R9 |
| `¬n < p` → `p ≤ n` | `push Not at hle` | R10 |
| `0 < p`, `1 < p` from `hp : p.Prime` | `hp.pos`, `hp.one_lt` | R11, R17 |
| `m ≤ n → m ∣ n!` | `Nat.dvd_factorial hm hle` | R12 |
| `a ∣ b → a ∣ c * b` | `dvd_mul_of_dvd_right hab c` | R13 |
| `k ∣ m`, `k ∣ n` → `k ∣ m - n` | `Nat.dvd_sub hm hn` | R14 |
| rewrite an arithmetic subterm in `h` | `rw [show a = b by omega] at h` | R15 |
| `k ∣ 1 → k = 1` | `Nat.dvd_one.mp h` | R16 |
| `1 < p` and `p = 1` → `False` | `hlt.ne' h1` | R18 |
| see the state | infoview | |
