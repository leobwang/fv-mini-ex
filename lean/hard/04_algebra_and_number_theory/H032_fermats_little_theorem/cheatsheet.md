# H032 · Fermat's little theorem: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `intro`, `exact`, `apply`, `have`, `rw`,
`induction` on `ℕ`, `∃`/`∧`/`¬`, anonymous constructors `⟨_, _⟩`. **New here:** Mathlib's `Nat.Prime`,
divisibility `∣`, congruence `a ≡ b [MOD n]` (`Nat.ModEq`) and its lemmas, finite sums `∑ i ∈ Finset.range n`,
binomial coefficients `n.choose k` and the binomial theorem `add_pow`, the trivial cast `ℕ → ℕ`, `obtain` with
an `rfl` pattern, `omega`, `calc` with `≡`, and cancelling a factor coprime to the modulus.

**The maths.** `p` is prime, `a : ℕ`. `a ≡ b [MOD n]` means `a % n = b % n` (same remainder). `C(n, k)` is
the binomial coefficient, written `n.choose k`.

1. *Middle terms.* For `0 < k < p`, `p ∣ C(p, k)`: `p` divides `p! = C(p, k) · k! · (p - k)!` but no factor of
   `k! (p - k)!`, all of which are `< p`. Mathlib gives this as `Nat.Prime.dvd_choose_self` (R4).
2. *Freshman's dream.* Binomial theorem: `(a + 1) ^ p = ∑_{k=0}^{p} a^k · C(p, k)`. The `k = 0` term is `1`,
   the `k = p` term is `a ^ p`, and every other term is divisible by `p`. So `(a + 1) ^ p ≡ a ^ p + 1`.
3. *Fermat.* Induction on `a`: `0 ^ p = 0`, and `(a + 1) ^ p ≡ a ^ p + 1 ≡ a + 1` by step 2 and the IH.
4. *Cancelling.* If `p ∤ a`, then `gcd(p, a) = 1`, and `a · a^(p-1) = a^p ≡ a = a · 1`, so `a^(p-1) ≡ 1`. In ℕ,
   `p - 1` is truncated subtraction, so `p - 1 + 1 = p` needs `1 ≤ p`.

In Lean the sum is indexed by `m ∈ Finset.range (p + 1)`, i.e. `m = 0, …, p`. To peel off BOTH end terms the
upper bound must be `(q + 1) + 1` for a variable `q`, so the proof first writes `p = q + 1` (R8, R9). The middle
sum is then `∑ i ∈ Finset.range q, a ^ (i + 1) * (q + 1).choose (i + 1)`: the terms `k = i + 1 = 1, …, q`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`apply`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal, and `g : … → G` is a hypothesis that only finishes the
  example once the step has put the right fact in the context.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid M]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `a ≡ b [MOD n]` | `Nat.ModEq n a b`, by definition `a % n = b % n`. Not an `=`: you cannot `rw` with it |
| `Nat.Prime p` | `p` is prime (`2 ≤ p`, only divisors `1` and `p`); written `p.Prime` in source |
| `d ∣ n` (typed `\mid`, not `\|`) | "`d` divides `n`": by definition `∃ c, n = d * c` |
| `¬p ∣ a` | `p` does not divide `a` (`¬` binds weaker than `∣`) |
| `Finset.range n` | the finite set `{0, 1, …, n - 1}` (a `Finset ℕ`) |
| `∑ i ∈ s, f i` | the sum of `f i` over the finite set `s` (typed `\sum`) |
| `∀ i ∈ s, Q i` | `∀ i, i ∈ s → Q i`: two binders, so `intro i hi` (R2) |
| `n.choose k` | the binomial coefficient C(n, k) (`Nat.choose n k`) |
| `↑(n.choose m)` | C(n, m) cast into the ring of the sum. In ℕ it is the identity cast, removed by R19 |
| `p.Coprime n` | `Nat.Coprime p n`, by definition `p.gcd n = 1` |
| `m.gcd c` | `Nat.gcd m c` |
| `n - m` on `ℕ` | truncated subtraction: `0` when `m > n` |
| `this` | the name `have := e` gives (R8) |
| `n✝`, `a✝` | names Lean invented; you cannot type them. Name them with `with` or `case … =>` (R24) |
| `case hk`, `case hkp` | side goals left by `apply`, named after the lemma's hypotheses (R4) |
| `case zero`, `case succ` | the two goals of `induction` on `ℕ` (R24) |
| `∑ x ∈ …`, `∑ k ∈ …` | after a `rw` the bound variable may be renamed (R11, R12); it is only a name |

---

## Part 1 · `middle_terms` (milestone)

Statement: `q + 1 ∣ ∑ i ∈ Finset.range q, a ^ (i + 1) * (q + 1).choose (i + 1)` when `q + 1` is prime: the prime
divides the whole middle sum because it divides each `C(q + 1, i + 1)` with `1 ≤ i + 1 ≤ q`. Prove it first;
`freshman` uses it for the middle of the binomial sum.

**R1 · `apply Finset.dvd_sum`** changes the **goal**: to divide a sum it suffices to divide every term. The lemma
is `Finset.dvd_sum : (∀ i ∈ s, d ∣ f i) → d ∣ ∑ i ∈ s, f i`. Placeholders: `{ι : Type} (s : Finset ι)
(f : ι → ℕ) (d : ℕ)` (it holds in any semiring, ℕ and ℤ included).

| Before | After |
|---|---|
| `⊢ d ∣ ∑ i ∈ s, f i` | `⊢ ∀ i ∈ s, d ∣ f i` |

**R2 · `intro i hi`** changes the **context**: a bounded `∀ i ∈ s` gives two hypotheses, the index and its
membership. Placeholders: `{ι : Type} (s : Finset ι) (Q : ι → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ i ∈ s, Q i` | `hi : i ∈ s ⊢ Q i` |

**R3 · `rw [Finset.mem_range] at hi`** changes the **context**. The lemma is `m ∈ Finset.range n ↔ m < n`;
`rw` with an `↔` replaces one proposition by the other. Placeholders: `(n i : ℕ)`.

| Before | After |
|---|---|
| `hi : i ∈ Finset.range n ⊢ G` | `hi : i < n ⊢ G` |

**R4 · `Nat.Prime.dvd_choose_self`** changes the **goal list**: `apply hp.dvd_choose_self` turns `p ∣ p.choose k`
into the two side goals `k ≠ 0` and `k < p`. The lemma is `p.Prime → k ≠ 0 → k < p → p ∣ p.choose k`.
Placeholders: `(p k : ℕ) (hp : p.Prime)`. As a term, `hp.dvd_choose_self hk hkp`, with `hk`, `hkp` given by
R5 and `(by omega)` (R6).

| Before | After |
|---|---|
| `⊢ p ∣ p.choose k` | `⊢ k ≠ 0`, `⊢ k < p` |

**R5 · `Nat.succ_ne_zero`** **closes** `n + 1 ≠ 0`. The lemma is `Nat.succ_ne_zero n : n.succ ≠ 0`, and
`n.succ` is `n + 1` by definition, so it is accepted for the goal below. Placeholders: `(i : ℕ)`.

| Before | After |
|---|---|
| `⊢ i + 1 ≠ 0` | no goals |

**R6 · `omega`** **closes** a goal of linear arithmetic over `ℕ` or `ℤ` (`+`, `-`, `*` by numerals, `<`, `≤`, `=`)
using the hypotheses of that shape. It knows truncated subtraction. Placeholders: `(k n : ℕ) (hk : k < n)`.

| Before | After |
|---|---|
| `hk : k < n ⊢ k + 1 < n + 1` | no goals |

**R7 · `Dvd.dvd.mul_left`** changes the **goal**: a divisor of `b` divides every multiple `c * b`. The lemma is
`a ∣ b → ∀ c, a ∣ c * b`; for `h : d ∣ b` the term `h.mul_left c` (or `h.mul_left _`) proves `d ∣ c * b`.
Placeholders: `(d b c : ℕ)` (any commutative semigroup).

| Before | After `apply Dvd.dvd.mul_left` |
|---|---|
| `⊢ d ∣ c * b` | `⊢ d ∣ b` |

---

## Part 2 · `freshman` (milestone)

Statement: `(a + 1) ^ p ≡ a ^ p + 1 [MOD p]` for `p` prime. Write `p = q + 1` (R8, R9), expand (R10), peel the
last term (R11) and the first term (R12), clean up the two end terms (R13–R19), then show the middle sum is
`≡ 0` with `middle_terms` (R20) and finish with a `calc` (R21–R23).

### Writing `p` as `q + 1`

**R8 · `Nat.Prime.one_lt`** changes the **context**: `hp.one_lt : 1 < p`. `have := hp.one_lt` names it `this`;
`omega` in R9 needs this fact in the context. Placeholders: `(p : ℕ) (hp : p.Prime)`.

| Before | After `have h := hp.one_lt` |
|---|---|
| `hp : Nat.Prime p ⊢ G` | `h : 1 < p ⊢ G` |

**R9 · `obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩`** changes the **context and the goal**: it proves
`∃ q, p = q + 1` (witness `p - 1`, and `omega` shows `p = p - 1 + 1` from `1 < p`), then the pattern `rfl`
substitutes `p := q + 1` in every hypothesis and in the goal. Placeholders: `(p : ℕ) (hp1 : 1 < p)
(Q : ℕ → Prop)`.

| Before | After |
|---|---|
| `hp1 : 1 < p ⊢ Q p` | `q : ℕ, hp1 : 1 < q + 1 ⊢ Q (q + 1)` |

### The binomial theorem and its end terms

**R10 · `rw [add_pow]`** changes the **goal**. The lemma is
`add_pow : (x + y) ^ n = ∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * ↑(n.choose m)`.
Placeholders: `{R : Type} [CommSemiring R] (x y : R) (n : ℕ)` (`R` has commutative `+` and `*` with `0`, `1`:
`ℕ`, `ℤ`, `ℝ` qualify). The binomial coefficient is a natural number cast into `R` (`↑`); with `R = ℕ` that is
the identity cast (R19).

| Before | After |
|---|---|
| `⊢ P ((x + y) ^ n)` | `⊢ P (∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * ↑(n.choose m))` |

**R11 · `rw [Finset.sum_range_succ]`** changes the **goal**: the last term comes out. The lemma is
`∑ x ∈ range (n + 1), f x = ∑ x ∈ range n, f x + f n`. Placeholders: `{M : Type} [AddCommMonoid M] (f : ℕ → M)
(n : ℕ)` (`M` has a commutative `+` with `0`: ℕ, ℤ, ℝ qualify). The bound must have the form `n + 1`.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ Finset.range (n + 1), f i)` | `⊢ P (∑ x ∈ Finset.range n, f x + f n)` |

**R12 · `rw [Finset.sum_range_succ']`** changes the **goal**: the first term comes out and the rest is reindexed
by `k + 1`. The lemma is `∑ k ∈ range (n + 1), f k = ∑ k ∈ range n, f (k + 1) + f 0`. Same placeholders as R11.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ Finset.range (n + 1), f i)` | `⊢ P (∑ k ∈ Finset.range n, f (k + 1) + f 0)` |

R13–R19 are the clean-up lemmas for the end terms `a ^ 0 * 1 ^ (q + 1 - 0) * ↑((q + 1).choose 0)` and
`a ^ (q + 1) * 1 ^ (q + 1 - (q + 1)) * ↑((q + 1).choose (q + 1))`, and for the `1 ^ _` and `↑` inside the middle
sum. Give them all to one `simp only [...]` (W2); `simp only` also rewrites under the `∑` binder, where `rw` cannot.
`{M : Type} [Monoid M]` means `M` has an associative `*` with `1` (ℕ, ℤ, ℝ qualify).

| Entry | Lemma | Before | After |
|---|---|---|---|
| **R13 · `one_pow`** | `1 ^ n = 1` | `⊢ P (1 ^ n)` | `⊢ P 1` |
| **R14 · `mul_one`** | `a * 1 = a` | `⊢ P (a * 1)` | `⊢ P a` |
| **R15 · `Nat.choose_self`** | `n.choose n = 1` | `⊢ P (n.choose n)` | `⊢ P 1` |
| **R16 · `Nat.sub_self`** | `n - n = 0` | `⊢ P (n - n)` | `⊢ P 0` |
| **R17 · `pow_zero`** | `a ^ 0 = 1` | `⊢ P (a ^ 0)` | `⊢ P 1` |
| **R18 · `Nat.choose_zero_right`** | `n.choose 0 = 1` | `⊢ P (n.choose 0)` | `⊢ P 1` |
| **R19 · `Nat.cast_id`** | `(↑n : ℕ) = n` | `⊢ P ↑n` | `⊢ P n` |

Each changes the **goal**. Placeholders: `{M : Type} [Monoid M] (a : M) (n : ℕ)` for R13, R14, R17; `(n : ℕ)` for
the others. After the clean-up the goal of `freshman` has the shape `middle + 1 + a ^ (q + 1) ≡ a ^ (q + 1) + 1`,
with `middle` exactly the sum of `middle_terms`.

### From divisibility to a congruence

**R20 · `Nat.modEq_zero_iff_dvd`** changes the **context**: `.mpr` turns `n ∣ a` into `a ≡ 0 [MOD n]`. The lemma is
`a ≡ 0 [MOD n] ↔ n ∣ a`; `.mpr` is its right-to-left direction. Placeholders: `(n a : ℕ)`.

| Before | After `have h' := Nat.modEq_zero_iff_dvd.mpr h` |
|---|---|
| `h : n ∣ a ⊢ G` | `h' : a ≡ 0 [MOD n] ⊢ G` |

**R21 · `Nat.ModEq.add_right`** changes the **context**: add the same `c` on both sides of a congruence. The lemma
is `Nat.ModEq.add_right c : a ≡ b [MOD n] → a + c ≡ b + c [MOD n]`, used as `h.add_right c`. Chain it:
`(h.add_right 1).add_right _`. Placeholders: `(n a b c : ℕ)`.

| Before | After `have h' := h.add_right c` |
|---|---|
| `h : a ≡ b [MOD n] ⊢ G` | `h' : a + c ≡ b + c [MOD n] ⊢ G` |

**R22 · `calc`** **closes** `a ≡ c [MOD n]` from a chain of `≡ [MOD n]` and `=` steps, each with its own proof
(`:= term` or `:= by tac`). The first left side may be `_`, which Lean reads off the goal. Use it to finish with an
`=` step proved by `ring`. Placeholders: `(n a b c : ℕ) (h : a ≡ b [MOD n]) (e : b = c)`.

| Before | After |
|---|---|
| `h : a ≡ b [MOD n], e : b = c ⊢ a ≡ c [MOD n]` | no goals |

**R23 · `ring`** **closes** an equation that holds in every commutative semiring: reordering, `0 + s = s`,
distributing. Powers `a ^ (q + 1)` and sums are unknowns to it. Placeholders: `(s t : ℕ)`.

| Before | After |
|---|---|
| `⊢ 0 + s + t = t + s` | no goals |

**W1 · peel both ends** of `∑ i ∈ range (n + 1 + 1), f i` (R11, then R12 on the remaining `range (n + 1)`):

```lean-goal
⊢ ∑ i ∈ Finset.range (n + 1 + 1), f i = ∑ i ∈ Finset.range n, f (i + 1) + f 0 + f (n + 1)
⊢ ∑ x ∈ Finset.range (n + 1), f x + f (n + 1) = ∑ i ∈ Finset.range n, f (i + 1) + f 0 + f (n + 1)
```

The second `rw` turns both sides into the same text, and `rw` closes it with `rfl`.

**W2 · one binomial term with `y = 1`**, cleaned by `simp only [one_pow, mul_one, Nat.cast_id]`:

```lean-goal
⊢ x ^ m * 1 ^ (k - m) * ↑(k.choose m) = x ^ m * k.choose m
```

**W3 · a divisible summand is `≡ 0`**: R20, then a `calc` whose first step is R21 and whose last is `ring`:

```lean-goal
⊢ s + t ≡ t [MOD n]
```

---

## Part 3 · `fermat`

Statement: `a ^ p ≡ a [MOD p]` for `p` prime. Induction on `a` (R24). Zero case: `0 ^ p = 0` (R25, R26).
Successor case: `freshman` for `a` gives `(a + 1) ^ p ≡ a ^ p + 1`, the IH plus 1 (R21) gives
`a ^ p + 1 ≡ a + 1`; glue them with R27.

**R24 · `induction a`** changes the **goal list and the context**: one goal per constructor of `ℕ`, and the
successor goal has the induction hypothesis. Placeholders: `(Q : ℕ → Prop) (a : ℕ)`; in the exercise
`Q a` is `a ^ p ≡ a [MOD p]`. Lean's own names carry `✝`; write
`induction a with | zero => … | succ a ih => …` to call them `a`, `ih`.

| Before | After |
|---|---|
| `⊢ Q a` | `⊢ Q 0`, `n✝ : ℕ, a✝ : Q n✝ ⊢ Q (n✝ + 1)` |

**R25 · `Nat.Prime.pos`** changes the **context**: `hp.pos : 0 < p`. Placeholders: `(p : ℕ) (hp : p.Prime)`.

| Before | After `have h := hp.pos` |
|---|---|
| `hp : Nat.Prime p ⊢ G` | `h : 0 < p ⊢ G` |

**R26 · `rw [Nat.zero_pow hn]`** changes the **goal**. The lemma is `Nat.zero_pow : 0 < n → 0 ^ n = 0`.
Placeholders: `(n : ℕ) (hn : 0 < n)`. After any `rw`, Lean tries `rfl`, which closes `0 ≡ 0 [MOD m]` (W5), so the
zero case is the single `rw [Nat.zero_pow hp.pos]`.

| Before | After |
|---|---|
| `⊢ P (0 ^ n)` | `⊢ P 0` |

**R27 · `Nat.ModEq.trans`** changes the **goal**: `refine h1.trans ?_` keeps the right end and asks for the second
half. The lemma is `a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c [MOD n]`; with both halves at hand,
`exact h1.trans h2`. Placeholders: `(n a b c : ℕ)`.

| Before | After |
|---|---|
| `h1 : a ≡ b [MOD n] ⊢ a ≡ c [MOD n]` | `⊢ b ≡ c [MOD n]` |

**W4 · chain two congruences**: `(h1.add_right 2).trans h2` proves `a + 2 ≡ c` from `h1 : a ≡ b`, `h2 : b + 2 ≡ c`:

```lean-goal
⊢ a + 2 ≡ c [MOD n]
```

**W5 · the zero case of a power closes after one `rw`**:

```lean-goal
⊢ 0 ^ n ≡ 0 [MOD m]
```

---

## Part 4 · `fermat'`

Statement: `a ^ (p - 1) ≡ 1 [MOD p]` when `p` is prime and `¬p ∣ a`. Get `p.Coprime a` (R28) and cancel `a`
(R29): the goal becomes `a * a ^ (p - 1) ≡ a * 1 [MOD p]`. Fold the power (R30), cancel `p - 1 + 1` (R31, R32),
drop `* 1` (R14), and what is left is `fermat`.

**R28 · `Nat.Prime.coprime_iff_not_dvd`** changes the **context**: `(Nat.Prime.coprime_iff_not_dvd hp).mpr hn` turns
`¬p ∣ n` into `p.Coprime n`. The lemma is `p.Prime → (p.Coprime n ↔ ¬p ∣ n)`. Placeholders: `(p n : ℕ)
(hp : p.Prime)`.

| Before | After `have hc := (Nat.Prime.coprime_iff_not_dvd hp).mpr hn` |
|---|---|
| `hn : ¬p ∣ n ⊢ G` | `hc : p.Coprime n ⊢ G` |

**R29 · `apply Nat.ModEq.cancel_left_of_coprime hc`** changes the **goal**: to prove `a ≡ b`, prove `c * a ≡ c * b`
for some `c` coprime to the modulus. The lemma is `m.gcd c = 1 → c * a ≡ c * b [MOD m] → a ≡ b [MOD m]`;
`hc : m.Coprime c` is accepted for `m.gcd c = 1` (same by definition), and fixes `c`. Placeholders:
`(m a b c : ℕ)`.

| Before | After |
|---|---|
| `hc : m.Coprime c ⊢ a ≡ b [MOD m]` | `⊢ c * a ≡ c * b [MOD m]` |

**R30 · `rw [← pow_succ']`** changes the **goal**. The lemma is `pow_succ' : a ^ (n + 1) = a * a ^ n`; `←` folds
`a * a ^ n` into one power. Placeholders: `{M : Type} [Monoid M] (a : M) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (a * a ^ n)` | `⊢ P (a ^ (n + 1))` |

**R31 · `LT.lt.le`** changes the **context**: `h.le : a ≤ b` from `h : a < b`. So `hp.one_lt.le : 1 ≤ p` (R8).
Placeholders: `(a b : ℕ)` (any preorder).

| Before | After `have h' := h.le` |
|---|---|
| `h : a < b ⊢ G` | `h' : a ≤ b ⊢ G` |

**R32 · `rw [Nat.sub_add_cancel hm]`** changes the **goal**. The lemma is `Nat.sub_add_cancel : m ≤ n → n - m + m = n`
(false without `m ≤ n`: `0 - 1 + 1 = 1`). Placeholders: `(n m : ℕ) (hm : m ≤ n)`.

| Before | After |
|---|---|
| `⊢ P (n - m + m)` | `⊢ P n` |

**W6 · cancel `3` modulo `7`**: `apply Nat.ModEq.cancel_left_of_coprime (by norm_num : Nat.gcd 7 3 = 1)`:

```lean-goal
⊢ a ≡ b [MOD 7]
⊢ 3 * a ≡ 3 * b [MOD 7]
```

**W7 · a truncated exponent put back**, from `hn : 1 < n`: `rw [← pow_succ']`, then `rw [Nat.sub_add_cancel hn.le]`
(which closes the goal with `rfl`):

```lean-goal
⊢ a * a ^ (n - 1) = a ^ n
⊢ a ^ (n - 1 + 1) = a ^ n
```

---

## Traps

- **No shortcuts.** `ZMod`, `CharP`, the Frobenius map, Euler's totient theorem and the library's binomial-mod-`p`
  lemmas (`add_pow_prime_eq`, `add_pow_char`, …) are banned: the point is the binomial-theorem proof by hand.
  `exact?`, `apply?`, `rw?`, `hint`, `try?` are banned too.
- **`p` must be `q + 1` before you peel the sum.** `add_pow` gives `range (p + 1)`; R11 leaves `range p`, and R12
  needs `range (_ + 1)`. With a variable `p` it does not match. Do R8, R9 first.
- **`omega` in R9 needs `1 < p` in the context.** `p = p - 1 + 1` is false for `p = 0`.
- **`rw` cannot reach under `∑`.** The `1 ^ (q + 1 - (k + 1))` and `↑` inside the middle sum need `simp only`.
  Include `Nat.cast_id`, or the sum keeps a `↑` and no longer matches `middle_terms`.
- **`≡` is not `=`.** `rw [h]` with `h : a ≡ b [MOD n]` fails. Use `.add_right`, `.trans`, `.symm` and `calc`.
- **`p - 1` is truncated.** `Nat.sub_add_cancel` needs `1 ≤ p`: `hp.one_lt.le`.
- **`rw [← pow_succ']` needs the shape `a * a ^ k`** with `a` on the left; `a ^ k * a` is `pow_succ` instead.
- `have := e` names the fact `this`; `induction a` without `with` leaves `n✝`, `a✝`, which you cannot type.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `d ∣ ∑ i ∈ s, f i` | `apply Finset.dvd_sum; intro i hi` | R1, R2 |
| `i ∈ range n` → `i < n` | `rw [Finset.mem_range] at hi` | R3 |
| `p ∣ p.choose k` | `hp.dvd_choose_self (Nat.succ_ne_zero i) (by omega)` | R4–R6 |
| `d ∣ c * b` from `h : d ∣ b` | `h.mul_left _` | R7 |
| write `p` as `q + 1` | `have := hp.one_lt; obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩` | R8, R9 |
| binomial theorem | `rw [add_pow]` | R10 |
| peel last / first term | `rw [Finset.sum_range_succ, Finset.sum_range_succ']` | R11, R12 |
| clean end terms | `simp only [one_pow, mul_one, Nat.choose_self, Nat.sub_self, pow_zero, Nat.choose_zero_right, Nat.cast_id]` | R13–R19 |
| `n ∣ a` → `a ≡ 0 [MOD n]` | `Nat.modEq_zero_iff_dvd.mpr h` | R20 |
| add to both sides | `h.add_right c` | R21 |
| chain `≡` and `=` | `calc _ ≡ x [MOD n] := …`, next line `_ = y := by ring` | R22, R23 |
| induction on `a` | `induction a with \| zero => … \| succ a ih => …` | R24 |
| `0 ^ p` → `0` | `rw [Nat.zero_pow hp.pos]` | R25, R26 |
| glue congruences | `h1.trans h2` | R27 |
| `¬p ∣ a` → coprime | `(Nat.Prime.coprime_iff_not_dvd hp).mpr ha` | R28 |
| cancel a coprime factor | `apply Nat.ModEq.cancel_left_of_coprime hc` | R29 |
| `a * a ^ k` → `a ^ (k + 1)` | `rw [← pow_succ']` | R30 |
| `p - 1 + 1` → `p` | `rw [Nat.sub_add_cancel hp.one_lt.le]` | R31, R32 |
| see the state | infoview | |
