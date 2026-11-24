# H031 · Bézout and Euclid's lemma: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `intro`, `exact`, `have`, `rw`, `induction`,
`∃`/`∧`/`∨`/`¬`. **New here:** Mathlib's `Nat.gcd`, `Nat.Prime`, divisibility `∣`, the cast `ℕ → ℤ`
(`↑n`) and the tactic `exact_mod_cast`, induction along Euclid's algorithm (`Nat.gcd.induction`), `obtain` /
`rcases` patterns, `▸`, `absurd`, `by_cases`, `calc`.

**The maths.** For `m n : ℕ`, `n % m` and `n / m` are the remainder and the quotient of `n` by `m`
(`n = m * (n / m) + n % m`, with `n / 0 = 0`, `n % 0 = n`). Euclid's algorithm uses
`gcd m n = gcd (n % m) m` until the first argument is `0`, and `gcd 0 n = n`. *Bézout:* there are
integers `x, y` with `x * a + y * b = gcd a b`. Carry them along the algorithm: if
`x * (n % m) + y * m = g`, then, since `n % m = n - m * (n / m)` in ℤ,
`(y - x * (n / m)) * m + x * n = g`. *Euclid's lemma:* `p` prime, `p ∣ a * b`, `p ∤ a`. The gcd of `p` and `a`
divides `p`, so it is `1` or `p`, and `p` is excluded because `p ∤ a`. Bézout gives `x * p + y * a = 1`; multiply
by `b`: `b = x * p * b + y * (a * b) = p * (x * b + y * c)` where `a * b = p * c`. So `p ∣ b`.
All the algebra is done in ℤ (subtraction!), then brought back to ℕ.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal, and `g : … → G` is a hypothesis that only finishes the
  example once the step has put the right fact in the context.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddGroup G]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `↑n` (with `n : ℕ` in a goal about `ℤ`) | the cast of the natural number `n` into `ℤ`; written `(n : ℤ)` in source |
| `↑0`, `↑1` | the numerals `0`, `1 : ℕ` cast into `ℤ`; `simp` (R9) or `Nat.cast_one` (R22) turn them into `0`, `1 : ℤ` |
| `↑(n % m)`, `↑(n / m)` | the cast of the **ℕ** remainder / quotient. Different from `↑n % ↑m` (remainder in ℤ) |
| `m.gcd n`, `Nat.gcd 0 n` | `Nat.gcd m n`, the gcd of two naturals (a literal first argument prints as `Nat.gcd 0 n`) |
| `↑((n % m).gcd m)` | the gcd computed in ℕ, then cast to ℤ |
| `Nat.Prime p` | `p` is prime (`2 ≤ p`, only divisors `1` and `p`); written `p.Prime` in source |
| `d ∣ n` (typed `\mid`, not `\|`) | "`d` divides `n`": by definition `∃ c, n = d * c` |
| `¬p ∣ a` | `p` does not divide `a` (`¬` binds weaker than `∣`) |
| `case H0`, `case H1` | the two goals of `Nat.gcd.induction`: first argument `0`, and the Euclid step (R6) |
| `case inl`, `case inr` / `case pos`, `case neg` | the two goals after `rcases … with h \| h` (R13) / after `by_cases` (R20) |
| `n✝`, `a✝¹`, `inst✝` | names Lean invented; you cannot type them. Name them with `with` or `case … n =>` (R6) |

---

## Part 1 · `gcd_step` (milestone)

Statement: from `h : x * ↑(n % m) + y * ↑m = ↑((n % m).gcd m)` conclude
`(y - x * ↑(n / m)) * ↑m + x * ↑n = ↑(m.gcd n)`. Prove it first; it is the whole `H1` case of `bezout`.

**R1 · `rw [Nat.gcd_rec m n]`** changes the **goal**: one step of Euclid's algorithm. The lemma is
`Nat.gcd_rec : gcd m n = gcd (n % m) m`. Placeholders: `(m n : ℕ)`. Give the arguments: without them `rw`
rewrites the first gcd it finds. After it, `rw [← h]` replaces `↑((n % m).gcd m)` by the left side of `h`.

| Before | After |
|---|---|
| `⊢ P (m.gcd n)` | `⊢ P ((n % m).gcd m)` |

**R2 · `rw [eq_sub_iff_add_eq]`** changes the **goal**. The lemma is `a = b - c ↔ a + c = b`: an equation with a
subtraction becomes one with an addition, which has the shape of `Nat.mod_add_div`. Placeholders:
`{G : Type} [AddGroup G] (a b c : G)` (`G` has `+`, `-`, `0`: `ℤ` qualifies, `ℕ` does not).

| Before | After |
|---|---|
| `⊢ a = b - c` | `⊢ a + c = b` |

**R3 · `Nat.mod_add_div`** changes the **context** (used as `have h := Nat.mod_add_div m k`, or passed directly
to R4). The lemma is `m % k + k * (m / k) = m`, the division identity in ℕ. Placeholders: `(m k : ℕ)`.

| Before | After |
|---|---|
| `⊢ G` | `h : m % k + k * (m / k) = m ⊢ G` |

**R4 · `exact_mod_cast e`** **closes** the goal. `e` is a fact about naturals; the goal is the same fact with
casts `↑` into ℤ. It pushes `↑` through `+`, `*`, `∣` and numerals on both sides and then compares. Works for `=`
and for `∣`. Placeholders: `(m k : ℕ) (h : m % k + k * (m / k) = m)`; second example `(d u v : ℕ) (h : d ∣ u + v)`.

| Before | After |
|---|---|
| `h : m % k + k * (m / k) = m ⊢ ↑(m % k) + ↑k * ↑(m / k) = ↑m` | closed |
| `h : d ∣ u + v ⊢ ↑d ∣ ↑u + ↑v` | closed |

To get such a fact into the context instead, write `have h' : (d : ℤ) ∣ u + v := by exact_mod_cast h`.

**R5 · `ring`** **closes** an identity of commutative rings. Casts such as `↑(m / k)` and `↑m` are unknowns to
it: it never uses `m = k * (m / k) + m % k`. That is why `%` is first removed with a rewrite (step 2 of the
skeleton). Placeholders: `(m k : ℕ) (x : ℤ)`.

| Before | After |
|---|---|
| `⊢ x * (↑m - ↑k * ↑(m / k)) + x * ↑k * ↑(m / k) = x * ↑m` | closed |

**W1: restating `m / k` in ℤ.** With the sibling lemma `Nat.div_add_mod' : m / k * k + m % k = m`: R2 turns the
subtraction into an addition, R4 closes it.

```lean-goal
⊢ ↑(m / k) * ↑k = ↑m - ↑(m % k)
⊢ ↑(m / k) * ↑k + ↑(m % k) = ↑m
```

---

## Part 2 · `bezout`

Statement: `∃ x y : ℤ, x * ↑a + y * ↑b = ↑(a.gcd b)` for all `a b : ℕ`. Induct along Euclid's algorithm.

**R6 · `induction a, b using Nat.gcd.induction`** changes the **goal list**. `Nat.gcd.induction` says: to prove
`Q m n` for all `m n`, prove `Q 0 n` (case `H0`) and, for `0 < m`, `Q (n % m) m → Q m n` (case `H1`).
The IH is about the pair `(n % m, m)`: the next step of the algorithm. Placeholders:
`(Q : ℕ → ℕ → Prop) (a b : ℕ)`. Without names Lean invents them:

| Before | After |
|---|---|
| `a b : ℕ ⊢ Q a b` | `n✝ : ℕ ⊢ Q 0 n✝`, `m✝ n✝ : ℕ, a✝¹ : 0 < m✝, a✝ : Q (n✝ % m✝) m✝ ⊢ Q m✝ n✝` |

Name them by writing `induction a, b using Nat.gcd.induction with` and, on the following lines, indented,
`| H0 n => …` and `| H1 m n hm ih => …`. In `H1` you then have `hm : 0 < m` and
`ih : Q (n % m) m`. Each alternative must close its goal (W4 shows the shape).

**R7 · `refine ⟨u, v, ?_⟩`** changes the **goal**: you choose the witnesses of `∃ x y, Q x y` and are left with
`Q u v`. `exact ⟨u, v, proof⟩` does it in one step when the proof is at hand. Placeholders:
`{α : Type} (Q : α → α → Prop) (u v : α)`.

| Before | After |
|---|---|
| `⊢ ∃ x y, Q x y` | `⊢ Q u v` |

**R8 · `Nat.gcd_zero_left`** changes the **goal**. The lemma is `Nat.gcd 0 n = n`. `simp` uses it by itself.
Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Nat.gcd 0 n)` | `⊢ P n` |

**R9 · `simp`** changes the **goal** (or closes it): it removes `0 * _`, `1 * _`, `_ + 0`, the cast `↑0 = 0`
and `Nat.gcd 0 n` (R8) in one call. Placeholders: `(n : ℕ) (z : ℤ)`.

| Before | After |
|---|---|
| `⊢ 0 * ↑0 + 1 * z = ↑(Nat.gcd 0 n)` | `⊢ z = ↑n` |

**R10 · `obtain ⟨x, y, h⟩ := ih`** changes the **context**: an existential hypothesis is replaced by its witnesses
and the property. Placeholders: `{α : Type} (Q : α → α → Prop) (ih : ∃ x y, Q x y)`.

| Before | After |
|---|---|
| `ih : ∃ x y, Q x y` and `⊢ G` | `x y : α, h : Q x y ⊢ G` |

**W4: `Nat.gcd.induction` with names (R6), on another statement.** It proves `gcd a b ∣ a ∧ gcd a b ∣ b`
without R11. Case `H0` is `simp`. In case `H1`, `ih : (n % m).gcd m ∣ n % m ∧ (n % m).gcd m ∣ m`; `ih.1`,
`ih.2` are its two halves. R1 turns the goal into `(n % m).gcd m ∣ m ∧ (n % m).gcd m ∣ n`, and
`refine ⟨ih.2, ?_⟩` closes the first half with `ih.2`, leaving `(n % m).gcd m ∣ n`. It then uses two names that are not entries because the exercise does not need them:
`Nat.dvd_add : a ∣ b → a ∣ c → a ∣ b + c` and `Dvd.dvd.mul_right : a ∣ b → ∀ c, a ∣ b * c`, giving
`e : (n % m).gcd m ∣ n % m + m * (n / m)`. `rwa [Nat.mod_add_div n m] at e` is `rw … at e` (R22) followed by
`exact e`.

---

## Part 3 · `gcd_eq_one_of_not_dvd` (milestone)

Statement: `Nat.Prime p → ¬p ∣ a → p.gcd a = 1`. `euclid` uses it to turn the Bézout equation for `(p, a)`
into `x * ↑p + y * ↑a = 1`.

**R11 · `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`** change the **context**. They are `gcd m n ∣ m` and
`gcd m n ∣ n`. Placeholders: `(m n : ℕ)`.

| Before | After `have hl := Nat.gcd_dvd_left m n` | After `have hr := Nat.gcd_dvd_right m n` |
|---|---|---|
| `⊢ G` | `hl : m.gcd n ∣ m ⊢ G` | `hr : m.gcd n ∣ n ⊢ G` |

**R12 · `Nat.Prime.eq_one_or_self_of_dvd`** changes the **context**. The lemma is
`Nat.Prime p → ∀ d, d ∣ p → d = 1 ∨ d = p`. With `hp : p.Prime` write `hp.eq_one_or_self_of_dvd d hd`
(dot notation: `hp` fills the first explicit argument). Placeholders: `(p d : ℕ) (hp : p.Prime) (hd : d ∣ p)`.

| Before | After |
|---|---|
| `⊢ G` | `h : d = 1 ∨ d = p ⊢ G` |

**R13 · `rcases h with h1 | h1`** changes the **goal list**: `h : A ∨ B` becomes two goals, one with `h1 : A`
(`case inl`), one with `h1 : B` (`case inr`). You may write `rcases e with h1 | h1` for any term `e`, e.g. R12's.
Placeholders: `(A B G : Prop) (h : A ∨ B)`.

| Before | After |
|---|---|
| `h : A ∨ B ⊢ G` | `h1 : A ⊢ G`, `h1 : B ⊢ G` |

**R14 · `h ▸ e`** is a **term**: from `e : P a` and `h : a = b` it builds `P b` (it rewrites inside the type of
`e`). Give it an expected type, e.g. `have e' : b ∣ c := h ▸ e`; it then changes the **context**.
Placeholders: `(a b c : ℕ) (h : a = b) (e : a ∣ c)`.

| Before | After |
|---|---|
| `⊢ G` | `e' : b ∣ c ⊢ G` |

**R15 · `exact absurd ha hna`** **closes** any goal from contradictory hypotheses `ha : A`, `hna : ¬A`.
Placeholders: `(A G : Prop)`.

| Before | After |
|---|---|
| `ha : A, hna : ¬A ⊢ G` | closed |

**W3: a divisor of a prime other than 1 is the prime.** `rcases hp.eq_one_or_self_of_dvd d hd with h1 | h1`
(R12, R13), then `absurd h1 hd1` (R15) and `exact h1`. After `rcases` both goals read as below; the first has
`h1 : d = 1`, the second `h1 : d = p`:

```lean-goal
⊢ d = p
```

---

## Part 4 · `int_dvd_of_bezout` (milestone)

Statement: `x * ↑p + y * ↑a = 1 → ↑p ∣ ↑a * ↑b → ↑p ∣ ↑b`, all in ℤ. This is Euclid's lemma once
`gcd p a = 1`.

**R16 · `obtain ⟨c, hc⟩ := h`** changes the **context**: `h : d ∣ n` is by definition `∃ c, n = d * c`, so it
unpacks to the quotient `c` and `hc : n = d * c` (the divisor is on the **left** of the product).
Placeholders: `(d n : ℤ)`.

| Before | After |
|---|---|
| `h : d ∣ n ⊢ G` | `c : ℤ, hc : n = d * c ⊢ G` |

**R17 · `refine ⟨c, ?_⟩`** changes the **goal**: to prove `d ∣ n`, choose the quotient `c` and prove
`n = d * c`. (`Dvd.intro c (h : d * c = n)` is the same with the equation the other way round.) Placeholders:
`(d n c : ℤ)`.

| Before | After |
|---|---|
| `⊢ d ∣ n` | `⊢ n = d * c` |

**R18 · `calc`** **closes** `a = d` by a chain of equations. Write `calc a = b := proof₁`, then, indented, one
line `_ = c := proof₂` per step; `_` is the previous right side. Each proof is usually `by rw [...]` or
`by ring`. The first left side and the last right side must match the goal. Placeholders: `(a b c d : ℤ)`.

| Before | After |
|---|---|
| `⊢ a = d` | closed |

**R19 · `rw [one_mul]`** changes the **goal**. The lemma is `one_mul : 1 * a = a`. Placeholders:
`{M : Type} [MulOneClass M] (a : M)` (`M` has `*` and `1` with `1 * a = a`: `ℕ`, `ℤ` qualify).
`rw` closes a goal `b = b` by itself, so `by rw [hxy, one_mul]` proves `↑b = (x * ↑p + y * ↑a) * ↑b`.

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

**W2: a common divisor divides every integer combination.** R16 twice, R17, then R18 with `rw` and R5:

```lean-goal
⊢ d ∣ x * a + y * b
⊢ x * a + y * b = d * (x * s + y * t)
```

---

## Part 5 · `euclid`

Statement: `Nat.Prime p → p ∣ a * b → p ∣ a ∨ p ∣ b`, in ℕ. Uses `bezout` and the two milestones above.

**R20 · `by_cases hA : A`** changes the **goal list**: two goals, one with `hA : A` (`case pos`), one with
`hA : ¬A` (`case neg`). Placeholders: `(A G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hA : A ⊢ G`, `hA : ¬A ⊢ G` |

**R21 · `right`** changes the **goal**: `A ∨ B` becomes `B` (`left` gives `A`). `exact Or.inl ha` closes
`A ∨ B` from `ha : A` in one step. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∨ B` | `⊢ B` |

**R22 · `rw [hk] at hz`, `rw [Nat.cast_one] at hz`** change the **context**: `rw … at hz` rewrites the
hypothesis `hz`, not the goal. `Nat.cast_one : ((1 : ℕ) : ℤ) = 1` removes the cast of the numeral `1`
(`↑1` in the infoview). In one call: `rw [hk, Nat.cast_one] at hz`. Placeholders:
`(k : ℕ) (z : ℤ) (hk : k = 1)`.

| Before | After `rw [hk] at hz` | After `rw [Nat.cast_one] at hz` |
|---|---|---|
| `hz : z = ↑k ⊢ G` | `hz : z = ↑1 ⊢ G` | `hz : z = 1 ⊢ G` |

**R23 · `Int.natCast_dvd_natCast`** changes the **context**. The lemma is the iff `(↑m : ℤ) ∣ ↑n ↔ m ∣ n`; its
`.mp` direction brings divisibility from ℤ back to ℕ (`.mpr`, or R4, goes up). Placeholders: `(m n : ℕ)`.

| Before | After `have h' := Int.natCast_dvd_natCast.mp h` |
|---|---|
| `h : ↑m ∣ ↑n ⊢ G` | `h' : m ∣ n ⊢ G` |

---

## Traps

- **Banned:** library Bézout/Euclid (`Nat.gcd_eq_gcd_ab`, `Nat.Prime.dvd_mul`, …), `Nat.Coprime` and all its
  lemmas, factorizations and `ZMod`. The checker matches the *last* name component, so `dvd_mul_left`,
  `dvd_mul_right`, `gcd_mul`, `prime` (as in `hp.prime`) are banned under every prefix. You need none of them:
  build `d ∣ n` by hand (R17).
- Write the cast **outside** the ℕ operation: `((n % m : ℕ) : ℤ)` is `↑(n % m)`, but `(n % m : ℤ)` elaborates
  `%` in ℤ as `↑n % ↑m`, a different term. `rw [h']` then fails to find `↑(n % m)` in the goal.
- `ring` and `linarith` know nothing about `%` and `/` in ℕ (`↑(n % m)` is an unknown, R5). Remove `%` by
  rewriting with an equation proved from `Nat.mod_add_div` (R2–R4) before calling `ring`.
- ℕ subtraction truncates (`2 - 5 = 0`). Do the subtraction in ℤ: that is why Bézout's coefficients are integers.
- In `induction … with`, put the alternatives `| H0 n => …`, `| H1 m n hm ih => …` on their own lines; each must
  close its goal. The case names are `H0` and `H1` (R6).
- `rw [← h]` needs `h`'s right side literally: `↑((n % m).gcd m)`, which is what R1 produces from `↑(m.gcd n)`.
- `obtain ⟨c, hc⟩ := (h : d ∣ n)` gives `hc : n = d * c`, divisor first. Match that order in a `calc`.
- `h ▸ e` needs a known expected type (`have e' : T := h ▸ e` or `exact … (h ▸ e) …`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| one Euclid step on the gcd | `rw [Nat.gcd_rec m n]` | R1 |
| `a = b - c` → `a + c = b` | `rw [eq_sub_iff_add_eq]` | R2 |
| `m % k + k * (m / k) = m` | `Nat.mod_add_div m k` | R3 |
| ℕ fact → same fact in ℤ | `exact_mod_cast h` | R4 |
| ring identity with casts as unknowns | `ring` | R5 |
| induction along Euclid | `induction a, b using Nat.gcd.induction with` / `\| H0 n => …` / `\| H1 m n hm ih => …` | R6 |
| choose witnesses of `∃ x y` | `refine ⟨u, v, ?_⟩` / `exact ⟨u, v, pf⟩` | R7 |
| `gcd 0 n = n`, `0 *`, `1 *`, `↑0` | `simp` (`Nat.gcd_zero_left`) | R8, R9 |
| unpack `∃` | `obtain ⟨x, y, h⟩ := ih` | R10 |
| gcd divides its arguments | `Nat.gcd_dvd_left m n`, `Nat.gcd_dvd_right m n` | R11 |
| divisor of a prime is `1` or `p` | `hp.eq_one_or_self_of_dvd d hd` | R12 |
| split `A ∨ B` | `rcases h with h1 \| h1` | R13 |
| transport `e : P a` along `a = b` | `h ▸ e` | R14 |
| contradiction | `exact absurd ha hna` | R15 |
| unpack / build `d ∣ n` | `obtain ⟨c, hc⟩ := h` / `refine ⟨c, ?_⟩` | R16, R17 |
| chain of equations | `calc a = b := … ` / `_ = c := …` | R18 |
| `1 * a = a` | `rw [one_mul]` | R19 |
| case on a proposition | `by_cases hA : A` | R20 |
| pick a side of `∨` | `left` / `right` / `exact Or.inl ha` | R21 |
| rewrite a hypothesis, `↑1 = 1` | `rw [hk, Nat.cast_one] at hz` | R22 |
| `↑m ∣ ↑n` → `m ∣ n` | `Int.natCast_dvd_natCast.mp h` | R23 |
| see the state | infoview | |
