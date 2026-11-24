# E092 · zify and lift: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `exact` (E003), `have` (E021) and
`omega` (E011). E063 (casts into `ℝ`) uses the same cast machinery but is not required.
**New here:** Mathlib's integers `ℤ` with the cast `Nat.cast : ℕ → ℤ` (printed `↑`), the tactics
`zify`, `lift`, `norm_cast`, `ring`, `norm_num`, divisibility `∣`, `Nat.Prime`, and the lemmas
`Nat.one_le_pow`, `Nat.dvd_prime`, `Or.resolve_left`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
gives the lemma's statement, lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P`, `Q` are "the rest of a goal or hypothesis" (`P Q : ℤ → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger statement. `G : Prop` is an arbitrary goal.
- "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## ℕ subtraction and casts in one paragraph

In `ℕ`, subtraction is *truncated*: `a - b = 0` whenever `b > a` (`2 - 5 = 0`). So ring algebra fails in
`ℕ`: `(n - 1) * (n + 1) = n ^ 2 - 1` is true for `n ≥ 1` (and for `n = 0`), but `ring` cannot prove it, since
it does not know `ℕ`'s `-`. The fix is to move the statement to `ℤ`, where `-` is honest. For `a : ℕ`,
`(a : ℤ)`, printed `↑a`, is the cast `Nat.cast a`. The cast commutes with `+`, `*`, `^`, numerals, and
preserves and reflects `=`, `≤`, `<`, `∣`. It commutes with `-` **only** under `b ≤ a`:
`↑(a - b) = ↑a - ↑b` needs that fact. `zify` turns a ℕ goal into the equivalent ℤ goal and pushes casts
down; it uses the facts you pass it (`zify [h₁, h₂]`) to remove casts of subtractions. `lift` goes the other
way: an integer `x` with `0 ≤ x` *is* a natural number, and `lift x to ℕ using hx` replaces `x : ℤ` by a
fresh `x : ℕ`, every old occurrence becoming `↑x`. `norm_cast` then strips those casts.

## Reading the goals

| You see | It means |
|---|---|
| `ℤ` | Mathlib's integers |
| `↑a` with `a : ℕ`, in an `ℤ` statement | `Nat.cast a : ℤ`, the natural number `a` as an integer (`(a : ℤ)` in source) |
| `↑(a - b)` | ℕ subtraction (truncated), then cast: it is `0` when `a < b` |
| `↑a - ↑b` | ℤ subtraction of the casts: negative when `a < b` |
| `↑n ^ 2` vs `↑(n ^ 2)` | `(↑n) ^ 2`, the cast binds tighter than `^`, vs the cast of the ℕ power; equal, and `zify` writes the first |
| `↑n - 1` after `zify` | the `1` is now the integer `1` (`zify` turns `↑(1 : ℕ)` into `(1 : ℤ)`) |
| `↑a ∣ 10` | `↑a` divides `10` in `ℤ`: `∃ c, 10 = ↑a * c`. The symbol `∣` is typed `\mid`; it is not the ASCII bar |
| `Nat.Prime p`, `p.Prime` | `p` is a prime natural number (the same statement, two spellings) |
| `¬a = 2` | how `a ≠ 2` prints after `norm_cast`; `a ≠ 2` is by definition `¬a = 2` (`a = 2 → False`) |
| `m = 1 ∨ m = p` | "or"; `Or.resolve_left` / `Or.resolve_right` drop one side |

---

## Part 1 · `zify_ex`

Statement: for `n : ℕ` with `h : 1 ≤ n`, `(n - 1) * (n + 1) = n ^ 2 - 1` in `ℕ`. Two truncated
subtractions, `n - 1` and `n ^ 2 - 1`; `zify` needs one `b ≤ a` fact for each. `h` covers the first; prove
`1 ≤ n ^ 2` (R1) for the second. Then `zify` with both (R2) and finish with `ring` in `ℤ` (R3).

**R1 · `Nat.one_le_pow`** changes the **context** when used in a `have`. The lemma is
`Nat.one_le_pow (n m : ℕ) : 0 < m → 1 ≤ m ^ n` (explicit exponent `n` first, then base `m`; `_ _` lets Lean
infer both from the goal of the `have`). In ℕ, `0 < m` unfolds to `0 + 1 ≤ m`, i.e. `1 ≤ m`, so a hypothesis
`1 ≤ m` is accepted as the argument (W3). Placeholders: `(m k : ℕ) (hm : 0 < m)`.

| Before | After `have hp : 1 ≤ m ^ k := Nat.one_le_pow k m hm` |
|---|---|
| `hm : 0 < m ⊢ G` | `hm : 0 < m, hp : 1 ≤ m ^ k ⊢ G` |

**R2 · `zify [hb]`** changes the **goal**: a ℕ equation or inequality becomes the equivalent statement
about the casts in `ℤ`, with casts pushed to the variables. With `hb : b ≤ a` it also rewrites
`↑(a - b)` to `↑a - ↑b`; without it the subtraction stays under one cast (W2). Placeholders:
`(a b c d : ℕ) (hb : b ≤ a)`. `zify [h₁, h₂]` takes any number of facts (W1).

| Before | After |
|---|---|
| `hb : b ≤ a ⊢ a - b + c = d` | `⊢ ↑a - ↑b + ↑c = ↑d` |

**R3 · `ring`** **closes** an equation that holds in every commutative ring. After R2 each `↑a` is an atom
(an unknown integer) to `ring`. Placeholders: `(a b c : ℕ)`.

| Before | After |
|---|---|
| `⊢ (↑a - ↑b) * ↑c = ↑a * ↑c - ↑b * ↑c` | no goals |

**W1:** two subtractions, `hb : b ≤ a`, `hd : d ≤ c`; `zify [hb, hd]` removes both, then `ring`:

```lean-goal
⊢ a - b + (c - d) + b + d = a + c
⊢ ↑a - ↑b + (↑c - ↑d) + ↑b + ↑d = ↑a + ↑c
```

**W2:** plain `zify` without the fact; `↑(a - b)` survives and `ring` would treat it as one unknown:

```lean-goal
⊢ a - b + c = d
⊢ ↑(a - b) + ↑c = ↑d
```

**W3:** the power's fact first. From `hm : 1 ≤ m`, `have hp : 1 ≤ m ^ 3 := Nat.one_le_pow 3 m hm` (R1), then
`zify [hp]` (R2) and `ring` (R3):

```lean-goal
⊢ m ^ 3 - 1 + 1 = m ^ 3
⊢ ↑m ^ 3 - 1 + 1 = ↑m ^ 3
```

## Part 2 · `lift_dvd`

Statement: for `x : ℤ` with `hx : 0 ≤ x`, `h : x ∣ 7` and `h1 : x ≠ 1`, prove `x = 7`. The lemma about
divisors of a prime, `Nat.dvd_prime`, is stated for `ℕ`. So: turn `x` into a natural number (R4), strip
the casts from `h`, `h1` and the goal (R5), split `h` into `x = 1 ∨ x = 7` (R6, with R7 for primality of
`7`), and discard the left case with `h1` (R8).

**R4 · `lift x to ℕ using hx`** changes the **context and the goal**: `x : ℤ` is replaced by a new
`x : ℕ`, `hx` is consumed, and every old `x` becomes `↑x`. Placeholders:
`(x : ℤ) (hx : 0 ≤ x) (P Q : ℤ → Prop) (hq : Q x)`.

| Before | After |
|---|---|
| `x : ℤ, hx : 0 ≤ x, hq : Q x ⊢ P x` | `x : ℕ, hq : Q ↑x ⊢ P ↑x` |

**R5 · `norm_cast at h h1 ⊢`** changes the **context and the goal**: in each named hypothesis and in the
goal (`⊢`), casts are pulled outward and dropped, `↑a ∣ 10` → `a ∣ 10`. Integer numerals count as casts
of ℕ numerals. `↑a ≠ 2` comes out as `¬a = 2`. Placeholders: `(a : ℕ)`.

| Before | After |
|---|---|
| `h : ↑a ∣ 10, h1 : ↑a ≠ 2 ⊢ ↑a = 10` | `h : a ∣ 10, h1 : ¬a = 2 ⊢ a = 10` |

**W4:** lift, strip, then `omega` (ℕ arithmetic). `h : x < 3`, `h0 : x ≠ 0`, `h1 : x ≠ 1`, goal `x = 2`:

```lean-goal
⊢ x = 2
⊢ ↑x = 2
⊢ x = 2
```

**R6 · `Nat.dvd_prime`** changes the **context** when used in a `have`. The lemma is
`Nat.dvd_prime {p m : ℕ} : Nat.Prime p → (m ∣ p ↔ m = 1 ∨ m = p)`: the only divisors of a prime are `1`
and itself. It gives an `↔`; `.mp` (`Iff.mp`) is its left-to-right direction, so
`(Nat.dvd_prime hp).mp h : m = 1 ∨ m = p`. `p` and `m` are implicit, found from `h`. Placeholders:
`(p m : ℕ) (hp : p.Prime) (h : m ∣ p)`.

| Before | After `have h' := (Nat.dvd_prime hp).mp h` |
|---|---|
| `h : m ∣ p ⊢ G` | `h : m ∣ p, h' : m = 1 ∨ m = p ⊢ G` |

**R7 · `norm_num`** **closes** `Nat.Prime n` for a numeral `n` (here `Nat.Prime 11`). Inside a term, write
`(by norm_num)` where the proof of primality goes: `Nat.dvd_prime (by norm_num)`. Lean first learns `p`
from `h`, then runs `norm_num` on `Nat.Prime p`.

**R8 · `Or.resolve_left`** **closes** the goal `B`. The lemma is `Or.resolve_left : A ∨ B → ¬A → B`;
dot notation lets you write `h.resolve_left hna`. `Or.resolve_right : A ∨ B → ¬B → A` is the mirror (W5).
Since `a ≠ 1` is by definition `¬a = 1`, it serves as `hna`. Placeholders: `(A B : Prop) (h : A ∨ B) (hna : ¬A)`.

| Before | After |
|---|---|
| `h : A ∨ B, hna : ¬A ⊢ B` | no goals |

**W5:** divisors of 13: `have h' := (Nat.dvd_prime (by norm_num)).mp h` (R6, R7), then
`exact h'.resolve_right h13` with `h13 : m ≠ 13`:

```lean-goal
⊢ m = 1
```

---

## Traps

- In ℕ, `a - b = 0` when `b > a`. `zify [h₁, h₂]` needs **every** `b ≤ a` that makes a `-` exact; a missing
  one leaves `↑(a - b)` in the goal (W2) and `ring` then fails.
- The fact must match the subtraction literally: for `n ^ 2 - 1` you need `1 ≤ n ^ 2`, not `1 ≤ n`.
- `Nat.one_le_pow` takes the **exponent first**: `Nat.one_le_pow k m hm : 1 ≤ m ^ k`.
- `ring` in `ℕ` does not understand truncated `-`; move to `ℤ` first (R2). `ring` does not use hypotheses.
- After `lift`, the variable keeps its name but is now `x : ℕ`, and `hx` is gone. Hypotheses that mentioned
  `x` show `↑x`; strip them with `norm_cast at h h1 ⊢` (list every one, plus `⊢` for the goal).
- `Nat.dvd_prime` gives an `↔`; use `.mp` to go from `m ∣ p` to the disjunction.
- `x ≠ 1` is `¬x = 1`, exactly the `¬A` that `resolve_left` wants; no conversion needed.
- `linarith`, `nlinarith`, `polyrith`, `interval_cases`, `grind` and `Nat.sub_one_mul` are BANNED here.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `1 ≤ m ^ k` from `0 < m` (or `1 ≤ m`) | `have hp : 1 ≤ m ^ k := Nat.one_le_pow _ _ hm` | R1 |
| ℕ goal with `-` → ℤ goal | `zify [h₁, h₂]` (one `b ≤ a` per subtraction) | R2 |
| ring identity in ℤ | `ring` | R3 |
| `x : ℤ`, `0 ≤ x` → `x : ℕ` | `lift x to ℕ using hx` | R4 |
| strip casts from hypotheses and goal | norm_cast at h h1 ⊢ (⊢ = the goal) | R5 |
| divisors of a prime | `(Nat.dvd_prime hp).mp h : m = 1 ∨ m = p` | R6 |
| `Nat.Prime 7` | `by norm_num` | R7 |
| drop the left / right case of `A ∨ B` | `h.resolve_left hna` / `h.resolve_right hnb` | R8, W5 |
| ℕ arithmetic after lifting | `omega` | W4 |
| see the state | infoview | |
