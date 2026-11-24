# M064 · Infinitely many primes ≡ 1 mod 4: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033: `obtain`/`rcases`, `rintro`, `omega`, `have`, `refine`).
**New here:** Mathlib's primes (`Nat.Prime`), divisibility lemmas, factorials, the ring `ZMod p` of
integers mod `p` with the cast `ℕ → ZMod p`, `Fact` instances, and `push Not`.

**The math.** Fix `n`. Let `N = (2 · n!)² + 1` and let `p` be a prime factor of `N` (`N ≠ 1` because
`n! > 0`). Then:

1. In `ZMod p` (integers mod `p`), `N = 0`, so `y² = −1` for `y = 2 · n!`. A library theorem says: if `−1`
   is a square mod a prime `p`, then `p % 4 ≠ 3`.
2. `p ≠ 2`, since `N` is odd. So `p % 2 = 1`, and with step 1, `p % 4 = 1`.
3. `p > n`: otherwise `p ≤ n` gives `p ∣ n!`, so `p ∣ (2 · n!)²`, so `p ∣ N − (2 · n!)² = 1`, but `p > 1`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `G` is an arbitrary goal (`G : Prop`); `P`, `Q`, `R` are arbitrary predicates (`ℕ → Prop`).
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddGroup α]` is a
  requirement on `α` (a *type class*); each entry says which familiar types meet it.
- A lemma with a hypothesis `h₁ → h₂ → …` is a function: `lemma a b` applies it to proofs `a`, `b`. For an
  `↔` lemma, `.mp` is the `→` direction and `.mpr` the `←` direction.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ` | the natural numbers `0, 1, 2, …` (Lean's `Nat`) |
| `n.factorial` | `n!` (`Nat.factorial n`); `Nat.factorial_pos n : 0 < n.factorial` |
| `Nat.Prime p` | `p` is prime. You may write `p.Prime`; Lean prints `Nat.Prime p` |
| `p ∣ m` | `p` divides `m`: `∃ c, m = p * c`. Typed `\mid`, not the bar `\|` |
| `p % 4` | remainder of `p` divided by 4 |
| `ZMod p` | the ring `ℤ/pℤ` of integers mod `p` (for prime `p` it is a field) |
| `((k : ℕ) : ZMod p)`, printed `↑k` | `k` mod `p`: the cast of a natural number into `ZMod p`. `↑` hides the target type; hover it in the infoview |
| `↑(a ^ 3 + 2)` vs `↑a ^ 3 + 2` | cast of the whole ℕ expression vs the expression built in `ZMod p` from `↑a`; equal, but different text (R7) |
| `-1 : ZMod p` | the class of `p − 1`. In `ℕ` there is no `-1`, so the square-root-of-`−1` fact lives in `ZMod p` |
| `Fact (Nat.Prime p)` | a type class that just stores a proof of `Nat.Prime p`, so instance search can find it (R4) |
| `this : Fact …`, `inst✝ : Monoid α` | an instance in the context: `this` is the default name from `haveI :=`; `inst✝` is an anonymous `[…]` binder (guide entries) |
| `¬A`, `a ≠ b` | `A → False`; `a ≠ b` is `¬(a = b)` |
| `case inl`, `case inr` | the two goals after splitting `A ∨ B` (left, right) |
| `case refine_1`, `case refine_2.inl`, `case hab` | names Lean gives new goals (here: the first `?_` of R12; the left `∨` case inside the second); ignore them |

---

## Part 1 · `primes_one_mod_four`

Statement: for every `n : ℕ`, `∃ p, n < p ∧ p.Prime ∧ p % 4 = 1`: there is a prime above `n` that is `1`
mod `4`. Build `p` and the three facts as `have`s first, then supply the witness (R12) and close the two
remaining goals.

### Getting a prime factor

**R1 · `have hf := Nat.factorial_pos n`** changes the **context**. Lemma: `Nat.factorial_pos (n : ℕ) :
0 < n.factorial`. Placeholders: `(n : ℕ)`. You need it for R3.

| Before | After |
|---|---|
| `⊢ G` | `hf : 0 < n.factorial ⊢ G` |

**R2 · `obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := m) hm`** changes the **context**. Lemma:
`Nat.exists_prime_and_dvd {n : ℕ} : n ≠ 1 → ∃ p, Nat.Prime p ∧ p ∣ n`. `obtain` unpacks the `∃` and the
`∧` into three hypotheses. `n` is implicit (`{n}`); `(n := m)` names it explicitly. Do that whenever the
proof of `n ≠ 1` is a tactic block `(by …)`, which cannot tell Lean what `n` is. Placeholders:
`(m : ℕ) (hm : m ≠ 1)`.

| Before | After |
|---|---|
| `hm : m ≠ 1 ⊢ G` | `p : ℕ, hp : Nat.Prime p, hpd : p ∣ m ⊢ G` |

**R3 · `nlinarith`** **closes** an arithmetic goal (`=`, `≤`, `<`, `≠`) over `ℕ`, `ℤ`, `ℝ` that follows from
the hypotheses after multiplying pairs of them. It needs the positivity fact in the context (R1).
Placeholders: `(a : ℕ) (ha : 0 < a)`. `positivity` does not prove `≠ 2`-shaped goals; `omega` sees
`(3 * a) ^ 2` as an opaque number and cannot relate it to `a`.

| Before | After |
|---|---|
| `ha : 0 < a ⊢ (3 * a) ^ 2 + 2 ≠ 2` | closed |

### `−1` is a square in `ZMod p`

**R4 · `haveI := Fact.mk hp`** changes the **context**: it adds the instance `this : Fact (Nat.Prime p)`.
`Fact.mk : P → Fact P`. Lemmas about `ZMod p` that need `p` prime take it as an instance argument
`[Fact (Nat.Prime p)]`, which Lean finds only in the context, not from `hp : Nat.Prime p`. Placeholders:
`(p : ℕ) (hp : Nat.Prime p)`.

| Before | After |
|---|---|
| `hp : Nat.Prime p ⊢ G` | `this : Fact (Nat.Prime p) ⊢ G` |

**R5 · `rw [eq_neg_iff_add_eq_zero]`** changes the **goal**. Lemma: `eq_neg_iff_add_eq_zero : a = -b ↔
a + b = 0`. Placeholders: `{α : Type} [AddGroup α] (a b : α)` (α has `+`, `0` and negation `-`; `ℤ`, `ℝ`,
`ZMod p` qualify, `ℕ` does not). It turns `y ^ 2 = -1` into `y ^ 2 + 1 = 0`, a statement whose ℕ version
you can get from divisibility.

| Before | After |
|---|---|
| `⊢ a = -b` | `⊢ a + b = 0` |

**R6 · `(ZMod.natCast_eq_zero_iff a p).mpr hd`** adds to the **context** the fact `↑a = 0` in `ZMod p`.
Lemma: `ZMod.natCast_eq_zero_iff (a b : ℕ) : ((a : ZMod b) = 0 ↔ b ∣ a)`: `a` is `0` mod `b` iff `b`
divides `a`. Placeholders: `(a p : ℕ) (hd : p ∣ a)`. Pass `_` for `a` to let Lean read it off `hd`.

| Before | After |
|---|---|
| `hd : p ∣ a ⊢ G` | `h0 : ↑a = 0 ⊢ G` |

**R7 · `exact_mod_cast e`** **closes** the goal with `e` when the two differ only in where the casts sit.
It normalises both by pushing `↑` through `+`, `*`, `^` and numerals (`↑(x + y) = ↑x + ↑y`,
`↑(x ^ k) = ↑x ^ k`, `↑2 = 2`). R6 gives `↑(whole ℕ expression) = 0`; after R5 the goal has the cast on
the inside. Placeholders: `(a p : ℕ)`.

| Before | After |
|---|---|
| `h : ↑(a ^ 3 + 2) = 0 ⊢ ↑a ^ 3 + 2 = 0` | closed |

**R8 · `ZMod.mod_four_ne_three_of_sq_eq_neg_one hy`** adds `p % 4 ≠ 3` to the **context**. Lemma:
`ZMod.mod_four_ne_three_of_sq_eq_neg_one {p : ℕ} [Fact (Nat.Prime p)] {y : ZMod p} : y ^ 2 = -1 →
p % 4 ≠ 3`. It needs the instance from R4. Placeholders: `(p : ℕ) (y : ZMod p) (hy : y ^ 2 = -1)`.

| Before | After |
|---|---|
| `hy : y ^ 2 = -1 ⊢ G` | `h3 : p % 4 ≠ 3 ⊢ G` |

### Ruling out `p = 2`

**R9 · `rintro rfl`** changes the **goal and the context**. `p ≠ 2` is `p = 2 → False`; `rintro rfl`
introduces the equation and substitutes it, so `p` disappears and every hypothesis mentions `2`.
Placeholders: `(p : ℕ) (Q : ℕ → Prop) (hp : Q p)`.

| Before | After |
|---|---|
| `hp : Q p ⊢ p ≠ 2` | `hp : Q 2 ⊢ False` |

**R10 · `⟨c, proof⟩` for `∣`** changes the **goal**. `k ∣ b` unfolds to `∃ c, b = k * c`, so the anonymous
constructor takes a witness `c` and a proof of `b = k * c` (usually `by ring`). As a term:
`⟨k * m ^ 2, by ring⟩`. Placeholders: `(k m : ℕ)`.

| Before | After `refine ⟨k * m ^ 2, ?_⟩` |
|---|---|
| `⊢ k ∣ (k * m) ^ 2` | `⊢ (k * m) ^ 2 = k * (k * m ^ 2)` |

**R11 · `omega`** **closes** a goal of linear arithmetic over `ℕ`/`ℤ` with `+`, `*` by numerals, `%` and
`/` by numerals, and `d ∣ e` for a numeral `d`. Any other term, such as `y ^ 2` or `(2 * x) ^ 2`, is one
opaque number: `3 ∣ t` and `3 ∣ t + 1` contradict each other whatever `t` is. Placeholders: `(x y : ℕ)`.

| Before | After |
|---|---|
| `h1 : 3 ∣ y ^ 2, h2 : 3 ∣ y ^ 2 + 1 ⊢ False` | closed |
| `h : x % 2 = 1, h' : x % 4 ≠ 1 ⊢ x % 4 = 3` | closed |

### The witness

**R12 · `refine ⟨x, ?_, hq, ?_⟩`** changes the **goal list**. `∃ y, A ∧ B ∧ C` nests as
`∃ y, A ∧ (B ∧ C)`, and one flat anonymous constructor fills all four slots: the witness, then the three
conjuncts. Parts you already have go in directly; each `?_` becomes a goal. Placeholders:
`(P Q R : ℕ → Prop) (x : ℕ) (hq : Q x)`.

| Before | After |
|---|---|
| `⊢ ∃ y, P y ∧ Q y ∧ R y` | `⊢ P x`, `⊢ R x` |

### Goal `n < p`

**R13 · `by_contra hle`** changes the **goal and the context**: assume the negation, prove `False`.
Placeholders: `(a b : ℕ)`.

| Before | After |
|---|---|
| `⊢ a < b` | `hle : ¬a < b ⊢ False` |

**R14 · `push Not at hle`** changes the **context**: it moves `¬` inward (`¬a < b` becomes `b ≤ a`,
`¬∀` becomes `∃ ¬`, …). `push_neg` is the older, now deprecated, name: it still runs but warns.
Placeholders: `(a b : ℕ) (hle : ¬a < b)`.

| Before | After |
|---|---|
| `hle : ¬a < b ⊢ False` | `hle : b ≤ a ⊢ False` |

**R15 · `hp.pos`, `hp.one_lt`** add to the **context**. Lemmas `Nat.Prime.pos : Nat.Prime p → 0 < p` and
`Nat.Prime.one_lt : Nat.Prime p → 1 < p`. Dot notation: since `hp : Nat.Prime p`, `hp.pos` means
`Nat.Prime.pos hp`. Placeholders: `(p : ℕ) (hp : Nat.Prime p)`.

| Before | After `have h0 := hp.pos` | After `have h1 := hp.one_lt` |
|---|---|---|
| `hp : Nat.Prime p ⊢ G` | `h0 : 0 < p ⊢ G` | `h1 : 1 < p ⊢ G` |

**R16 · `Nat.dvd_factorial`** changes the **goal list** when applied. Lemma: `Nat.dvd_factorial {m n : ℕ} :
0 < m → m ≤ n → m ∣ n.factorial`. As a term: `Nat.dvd_factorial hm hmn`. Placeholders: `(m n : ℕ)`.

| Before | After `apply Nat.dvd_factorial` |
|---|---|
| `⊢ m ∣ n.factorial` | `⊢ 0 < m`, `⊢ m ≤ n` |

**R17 · `dvd_mul_of_dvd_right`** changes the **goal**. Lemma: `dvd_mul_of_dvd_right : a ∣ b → ∀ (c : α),
a ∣ c * b` (a divisor of `b` divides every multiple `c * b`). As a term: `dvd_mul_of_dvd_right h c`.
Placeholders: `{α : Type} [CommSemigroup α] (a b c : α)` (α has an associative, commutative `*`; `ℕ`
qualifies).

| Before | After `apply dvd_mul_of_dvd_right` |
|---|---|
| `h : a ∣ b ⊢ a ∣ c * b` | `h : a ∣ b ⊢ a ∣ b` |

**R18 · `dvd_pow`, `two_ne_zero`** change the **goal list**. Lemma: `dvd_pow : a ∣ b → n ≠ 0 → a ∣ b ^ n`;
`two_ne_zero : 2 ≠ 0` (in any type where `2 ≠ 0` holds, `ℕ` included). As a term:
`dvd_pow h two_ne_zero : a ∣ b ^ 2`. Placeholders: `{α : Type} [Monoid α] (a b : α) (n : ℕ)` (α has an
associative `*` with `1`; `ℕ` qualifies).

| Before | After `apply dvd_pow` |
|---|---|
| `⊢ a ∣ b ^ n` | `⊢ a ∣ b`, `⊢ n ≠ 0` |

**R19 · `(Nat.dvd_add_right hm).mp hk`** adds to the **context**. Lemma: `Nat.dvd_add_right {k m n : ℕ} :
k ∣ m → (k ∣ m + n ↔ k ∣ n)`: if `k` divides one summand, it divides the sum iff it divides the other.
Note which summand: the divisible one is on the **left** (`m + n`). Placeholders:
`(k m n : ℕ) (hm : k ∣ m) (hk : k ∣ m + n)`.

| Before | After |
|---|---|
| `hm : k ∣ m, hk : k ∣ m + n ⊢ G` | `h1 : k ∣ n ⊢ G` |

**R20 · `Nat.dvd_one.mp`** adds to the **context**. Lemma: `Nat.dvd_one {n : ℕ} : n ∣ 1 ↔ n = 1`.
Placeholders: `(p : ℕ) (hd : p ∣ 1)`.

| Before | After |
|---|---|
| `hd : p ∣ 1 ⊢ G` | `h1 : p = 1 ⊢ G` |

**R21 · `hlt.ne'`** adds to the **context**. Lemma: `LT.lt.ne' : b < a → a ≠ b`, used by dot notation on
`hlt : 1 < p`. Since `p ≠ 1` is `p = 1 → False`, `hne h1 : False`, so `exact hne h1` closes a `False`
goal. Placeholders: `(p : ℕ) (hlt : 1 < p) (h1 : p = 1)`.

| Before | After |
|---|---|
| `hlt : 1 < p ⊢ False` | `hne : p ≠ 1 ⊢ False` |

### Goal `p % 4 = 1`

**R22 · `rcases hp.eq_two_or_odd with h | h`** changes the **goal list**: one goal per side of the `∨`.
Lemma: `Nat.Prime.eq_two_or_odd : Nat.Prime p → p = 2 ∨ p % 2 = 1`. Placeholders:
`(p : ℕ) (hp : Nat.Prime p)`.

| Before | After |
|---|---|
| `hp : Nat.Prime p ⊢ G` | `h : p = 2 ⊢ G`, `h : p % 2 = 1 ⊢ G` |

**R23 · `exact absurd ha hna`** **closes** any goal. Lemma: `absurd : a → ¬a → b`. With `h : p = 2` and
`hp2 : p ≠ 2` (which is `¬(p = 2)`), `absurd h hp2` proves anything. Placeholders: `(A G : Prop)`.

| Before | After |
|---|---|
| `ha : A, hna : ¬A ⊢ G` | closed |

In the other case, `omega` (R11) combines `p % 2 = 1` with `p % 4 ≠ 3`.

### Worked combinations (on objects that are not the exercise's)

**W1: from `p ∣ a ^ 3 + 2` to `(a : ZMod p) ^ 3 = -2`.** R5, then R7 applied to R6:

```lean-goal
⊢ ↑a ^ 3 = -2
⊢ ↑a ^ 3 + 2 = 0
```

`exact_mod_cast (ZMod.natCast_eq_zero_iff _ p).mpr hd` closes the second goal.

**W2: Euclid, a prime factor of `m.factorial + 1` is larger than `m`.** R13, R14, then
`h1 : p ∣ m.factorial := Nat.dvd_factorial hp.pos hle` (R15, R16), then R19 → R20 → R21 in one term:

```lean-goal
⊢ m < p
⊢ False
```

`exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp hd))`. In the exercise, the summand you
remove is `(2 * n.factorial) ^ 2`, so you first lift `p ∣ n.factorial` to it with R17 and R18.

---

## Traps

- **Name the implicit `n` in R2.** `Nat.exists_prime_and_dvd (by nlinarith)` fails: inside the `by` block
  the number is still a metavariable `?m`, so `nlinarith` sees `?m = 1` and cannot use it. Write
  `Nat.exists_prime_and_dvd (n := (2 * n.factorial) ^ 2 + 1) (by nlinarith)`.
- **No instance, no lemma.** Until you run R4, R8 fails with "failed to synthesize instance of type class
  Fact (Nat.Prime p)". `hp : Nat.Prime p` in the context is a hypothesis, not an instance.
- **Say which ring.** `(-1 : ℕ)` does not exist, and `2 * n.factorial` with no ascription is a natural
  number. State the square fact with both types written out: `((2 * n.factorial : ℕ) : ZMod p) ^ 2 = -1`.
- **Cast placement is text.** `rw` and `exact` see `↑(x + 1)` and `↑x + 1` as different; use
  `exact_mod_cast` (R7) or `push_cast` to bridge them.
- **`Nat.dvd_add_right` drops the left summand.** For `p ∣ X + 1` with `p ∣ X` it gives `p ∣ 1`; the
  divisible part must be the left summand, as in `(2 * n.factorial) ^ 2 + 1`.
- **`omega` does not do nonlinear arithmetic.** It cannot show `(2 * a) ^ 2 + 1 ≠ 1` from `0 < a` (use
  `nlinarith`, R3), but it can use `2 ∣ t` and `2 ∣ t + 1` for any `t` (R11).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `0 < n!` | `have hf := Nat.factorial_pos n` | R1 |
| a prime factor of `m ≠ 1` | `obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := m) (by …)` | R2 |
| nonlinear `≠`/`<` from `0 < a` | `nlinarith` | R3 |
| `[Fact (Nat.Prime p)]` instance | `haveI := Fact.mk hp` | R4 |
| `a = -b` → `a + b = 0` | `rw [eq_neg_iff_add_eq_zero]` | R5 |
| `p ∣ a` → `(a : ZMod p) = 0` | `(ZMod.natCast_eq_zero_iff _ p).mpr hd` | R6 |
| goal and fact differ by cast placement | `exact_mod_cast e` | R7 |
| `y ^ 2 = -1` in `ZMod p` → `p % 4 ≠ 3` | `ZMod.mod_four_ne_three_of_sq_eq_neg_one hy` | R8 |
| prove `p ≠ 2` by substituting | `rintro rfl` | R9 |
| prove `k ∣ b` with a witness | `⟨c, by ring⟩` | R10 |
| residues, `∣` by numerals | `omega` | R11 |
| witness + some conjuncts now | `refine ⟨p, ?_, hp, ?_⟩` | R12 |
| proof by contradiction | `by_contra hle` then `push Not at hle` | R13, R14 |
| `0 < p`, `1 < p` from primality | `hp.pos`, `hp.one_lt` | R15 |
| `m ∣ n!` | `Nat.dvd_factorial hm hmn` | R16 |
| `a ∣ b` → `a ∣ c * b` | `dvd_mul_of_dvd_right h c` | R17 |
| `a ∣ b` → `a ∣ b ^ 2` | `dvd_pow h two_ne_zero` | R18 |
| `k ∣ m`, `k ∣ m + n` → `k ∣ n` | `(Nat.dvd_add_right hm).mp hk` | R19 |
| `p ∣ 1` → `p = 1` | `Nat.dvd_one.mp hd` | R20 |
| `1 < p` and `p = 1` → `False` | `hlt.ne' h1` | R21 |
| `p = 2 ∨ p % 2 = 1` | `rcases hp.eq_two_or_odd with h \| h` | R22 |
| a fact and its negation | `absurd h hn` | R23 |
| see the state | infoview | |
