# H034 · When is −1 a square mod p?: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `rw`, `simp`, `omega`, `rcases`/`obtain`/`rintro`,
`decide`, `have`, `∀ x ∈ s`. **New here:** Mathlib's `ZMod n` (integers mod `n`), casts `ℕ → ZMod n`,
finite products `∏ i ∈ range n, f i`, `Nat.factorial` and `Nat.ascFactorial`, the class `Fact`, and
Mathlib's Fermat (`ZMod.pow_card_sub_one_eq_one`) and Wilson (`ZMod.wilsons_lemma`).

**The mathematics.** For a prime `p`: `-1` is a square in `ZMod p` iff `p % 4 ≠ 3`.

- (→) If `p % 4 = 3` and `x ^ 2 = -1`, then `x ≠ 0`, `p - 1 = 2(2k + 1)`, and Fermat gives
  `1 = x ^ (p - 1) = (x ^ 2) ^ (2k + 1) = (-1) ^ (2k + 1) = -1`. But `-1 ≠ 1` once `p > 2`.
- (←) `p = 2`: `1 ^ 2 = 1 = -1` in `ZMod 2`. Otherwise `p = 2·(2k) + 1`, and with `n = 2k`, in
  `ZMod (2n + 1)`: `(2n)! = n! · ∏_{i<n} (n + 1 + i) = n! · ∏_{i<n} (-(n - i)) = (-1)^n (n!)²`
  (`half_factorial`), because `(n + 1 + i) + (n - i) = 2n + 1 ≡ 0`. Wilson says `(2n)! = (p - 1)! = -1`,
  and `(-1)^(2k) = 1`, so `((2k)!)² = -1`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `Q` plays the same role inside a hypothesis.
- `G : Prop` is an arbitrary goal, and `g` is the fact that finishes it; such an entry changes only the context.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommMonoid M]` is a
  requirement on `M` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ZMod n` | the integers mod `n`, `{0, 1, …, n - 1}` with `+`, `*` mod `n`. A field when `n` is prime |
| `↑a` (with `a : ℕ`) | the natural number `a` cast into `ZMod n` (or another ring); `↑n = 0` in `ZMod n` |
| `-1` in `ZMod p` | the additive inverse of `1`, i.e. the class of `p - 1` |
| `n.factorial` | `n ! = 1 · 2 · … · n` (`Nat.factorial n`; with `open Nat` it prints `n !`) |
| `n.ascFactorial k` | the rising product `n (n + 1) ⋯ (n + k - 1)`, `k` factors (R1) |
| `range n` | `Finset.range n`, the finite set `{0, 1, …, n - 1}` (the file has `open Finset`) |
| `∏ i ∈ s, f i` | the product of `f i` over the finite set `s`; `s.prod f` is the same term (R14) |
| `#s` | `s.card`, the number of elements of the finite set `s` |
| `p.Prime`, `Nat.Prime p` | `p` is prime: `2 ≤ p` and its only divisors are `1` and `p` (`p.Prime` is dot notation for `Nat.Prime p`) |
| `Fact (Nat.Prime p)` | a class wrapping the proposition `p.Prime`, so lemmas can take it as an instance `[Fact p.Prime]` |
| `inst✝ : Fact …` | an anonymous instance in the context; `✝` marks a name you cannot type |
| `Odd n` | `∃ m, n = 2 * m + 1` |
| `a ∣ b` | `a` divides `b` (the symbol `∣`, typed `\mid`, not the ASCII bar) |
| `a % b`, `a / b` on `ℕ` | remainder and floor division; `omega` understands both when `b` is a numeral |
| `x ^ 2 ≠ -1` | `x ^ 2 = -1 → False` |
| `case mp`, `case mpr` | the two directions after `constructor` on `A ↔ B`: `A → B` (mp) and `B → A` (mpr) |
| `case mpr.inl`, `case mpr.inr` | inside `mpr`, the two goals after `rcases` on an `∨` (left: `p = 2`, right: `p` odd) |

---

## Part 1 · `half_factorial` (MILESTONE)

Statement: for every `n : ℕ`, in `ZMod (2n + 1)`, `↑(2n)! = (-1) ^ n * ↑(n!) ^ 2`. Three facts, then one
rewrite chain:

- `h1 : (2n)! = n! * ∏ i ∈ range n, (n + 1 + i)` in `ℕ` (R1, R2, R3);
- `h2 : ∀ i ∈ range n, ↑(n + 1 + i) = -↑(n - i)` in `ZMod (2n + 1)` (R4–R8);
- `h3 : ∏ i ∈ range n, (n - i) = n!` in `ℕ` (R9–R11, `omega`);
- the chain: `rw [h1]`, cast the product into `ZMod` (R12, R13), negate each factor with `h2` (R14),
  pull out the signs (R15, R16), fold the cast back (R13 `←`), `rw [h3]`, `ring`.

### `h1`: the double factorial split

**R1 · `rw [← Nat.ascFactorial_eq_prod_range]`** changes the **goal**. The lemma is
`Nat.ascFactorial_eq_prod_range : n.ascFactorial k = ∏ i ∈ range k, (n + i)`; right to left it folds the
product into a rising factorial. Placeholders: `(n k : ℕ)`. On `∏ i ∈ range n, (n + 1 + i)`, `rw` takes the
`n` of the lemma to be `n + 1`.

| Before | After |
|---|---|
| `⊢ P (∏ i ∈ range k, (n + i))` | `⊢ P (n.ascFactorial k)` |

**R2 · `rw [Nat.factorial_mul_ascFactorial]`** changes the **goal**. The lemma is
`n ! * (n + 1).ascFactorial k = (n + k)!`: multiplying `1 ⋯ n` by `(n + 1) ⋯ (n + k)`. Placeholders: `(n k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (n.factorial * (n + 1).ascFactorial k)` | `⊢ P (n + k).factorial` |

**R3 · `rw [two_mul]`** changes the **goal**. The lemma is `two_mul : 2 * a = a + a`. Placeholders:
`{α : Type} [NonAssocSemiring α] (a : α)` (`α` has `+`, `*`, `0`, `1`, `2`; `ℕ`, `ℤ`, `ZMod n` qualify). When
both sides become the same term, `rw` closes the goal by `rfl`.

| Before | After |
|---|---|
| `⊢ P (2 * a)` | `⊢ P (a + a)` |

### `h2`: complementary naturals are negatives in `ZMod`

Start with `intro i hi` (E025: `∀ i ∈ s, Q i` is `∀ i, i ∈ s → Q i`).

**R4 · `rw [Finset.mem_range] at hi`** changes the **context**. The lemma is `m ∈ range n ↔ m < n`; `rw` with
an `↔` replaces one proposition by the other. Placeholders: `(n i : ℕ)`.

| Before | After |
|---|---|
| `hi : i ∈ range n ⊢ G` | `hi : i < n ⊢ G` |

**R5 · `rw [eq_neg_iff_add_eq_zero]`** changes the **goal**. The lemma is `a = -b ↔ a + b = 0`.
Placeholders: `{A : Type} [AddGroup A] (a b : A)` (`A` has `+`, `0`, `-`; every ring, `ZMod n` included).

| Before | After |
|---|---|
| `⊢ a = -b` | `⊢ a + b = 0` |

**R6 · `rw [← Nat.cast_add]`** changes the **goal**. The lemma is `Nat.cast_add : ↑(m + n) = ↑m + ↑n`; right to
left it moves `+` inside the cast, so the sum is computed in `ℕ`. Placeholders:
`{R : Type} [AddMonoidWithOne R] (m n : ℕ)` (`R` has `+`, `0`, `1`; `ZMod n` qualifies).

| Before | After |
|---|---|
| `⊢ P (↑m + ↑n)` | `⊢ P ↑(m + n)` |

**R7 · `rw [ZMod.natCast_eq_zero_iff]`** changes the **goal**. The lemma is
`ZMod.natCast_eq_zero_iff (a b : ℕ) : (↑a : ZMod b) = 0 ↔ b ∣ a`: a natural is `0` mod `b` iff `b` divides it.
Placeholders: `(a b : ℕ)`.

| Before | After |
|---|---|
| `⊢ ↑a = 0` | `⊢ b ∣ a` |

**R8 · `rw [show e₁ = e₂ by omega]`** changes the **goal**: it rewrites with an arithmetic fact proved on the
spot. `omega` handles truncated subtraction (`b - a = 0` when `b < a`), so it needs the bound (`hab`, or
`hi : i < n` from R4) in the context. If the result is `x ∣ x` or `x = x`, `rw` closes it with `rfl`.
Placeholders: `(a b : ℕ) (hab : a ≤ b)`.

| Before | After |
|---|---|
| `⊢ P (a + (b - a))` | `⊢ P b` |

**W1** chains R5 → R6 → R7 → R8 on `↑(7 - m) = -↑m` in `ZMod 7`; the last `rw` leaves `7 ∣ 7` and closes it:

```lean-goal
⊢ ↑(7 - m) = -↑m
⊢ ↑(7 - m) + ↑m = 0
⊢ ↑(7 - m + m) = 0
⊢ 7 ∣ 7 - m + m
```

### `h3`: the reversed product is `n!`

**R9 · `rw [← Finset.prod_range_add_one_eq_factorial]`** changes the **goal**. The lemma is
`∏ i ∈ range n, (i + 1) = n !`; right to left it unfolds `n !` into a product. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P n.factorial` | `⊢ P (∏ i ∈ range n, (i + 1))` |

**R10 · `rw [← Finset.prod_range_reflect]`** changes the **goal**. The lemma is
`Finset.prod_range_reflect (f : ℕ → M) (n : ℕ) : ∏ j ∈ range n, f (n - 1 - j) = ∏ j ∈ range n, f j`: reading
the factors backwards. Placeholders: `{M : Type} [CommMonoid M] (f : ℕ → M) (n : ℕ)` (`M` has a commutative
`*` and `1`; `ℕ` and every commutative ring qualify). Right to left, `rw` rewrites the **first** product over
`range n` it meets, which in `∏ (n - i) = ∏ (i + 1)` is the left one.

| Before | After |
|---|---|
| `⊢ P (∏ j ∈ range n, f j)` | `⊢ P (∏ j ∈ range n, f (n - 1 - j))` |

**R11 · `refine Finset.prod_congr rfl ?_`** changes the **goal**. The lemma is
`Finset.prod_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.prod f = s₂.prod g`; with `rfl` for the sets, what is
left is equality of the factors, each with its membership hypothesis. `exact Finset.prod_congr rfl fun i hi => …`
does the same in one line. Placeholders: `{M : Type} [CommMonoid M] (s : Finset ℕ) (f g : ℕ → M)`.

| Before | After |
|---|---|
| `⊢ ∏ x ∈ s, f x = ∏ x ∈ s, g x` | `⊢ ∀ x ∈ s, f x = g x` |

The factor goal that remains in `h3` is pure `ℕ` arithmetic with `-`: turn `hi` into `i < n` (R4) and use `omega`.

### The chain

**R12 · `rw [Nat.cast_mul]`** changes the **goal**. The lemma is `↑(m * n) = ↑m * ↑n`. Placeholders:
`{R : Type} [NonAssocSemiring R] (m n : ℕ)` (`ZMod n` qualifies).

| Before | After |
|---|---|
| `⊢ P ↑(m * n)` | `⊢ P (↑m * ↑n)` |

**R13 · `rw [Nat.cast_prod]`** changes the **goal**: the cast of a product is the product of the casts. The
lemma is `↑(∏ i ∈ s, f i) = ∏ i ∈ s, ↑(f i)`. `rw [← Nat.cast_prod]` folds it back, which you need before
`rw [h3]`, since `h3` is a statement in `ℕ`. Placeholders: `{R : Type} [CommSemiring R] (s : Finset ℕ) (f : ℕ → ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑(∏ i ∈ s, f i)` | `⊢ P (∏ i ∈ s, ↑(f i))` |

**R14 · `rw [Finset.prod_congr rfl h]`** changes the **goal**: with `h : ∀ x ∈ s, f x = g x`,
`Finset.prod_congr rfl h : s.prod f = s.prod g` is an ordinary equation, so `rw` replaces every factor at once.
`rw [h]` alone fails: the `x` in `f x` is bound by `∏`, and `rw` cannot rewrite under a binder. Placeholders as
in R11. With `g` a variable Lean prints the result as `s.prod g`, the same product written without the binder.

| Before | After |
|---|---|
| `⊢ P (∏ x ∈ s, f x)` | `⊢ P (s.prod g)` |

**R15 · `rw [Finset.prod_neg]`** changes the **goal**. The lemma is `∏ x ∈ s, -f x = (-1) ^ #s * ∏ x ∈ s, f x`:
one `-1` per factor. Placeholders: `{M : Type} [CommRing M] (s : Finset ℕ) (f : ℕ → M)` (the lemma itself asks
only `[CommMonoid M] [HasDistribNeg M]`; every commutative ring, `ZMod n` included, qualifies).

| Before | After |
|---|---|
| `⊢ P (∏ x ∈ s, -f x)` | `⊢ P ((-1) ^ #s * ∏ x ∈ s, f x)` |

**R16 · `rw [Finset.card_range]`** changes the **goal**. The lemma is `#(range n) = n`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P #(range n)` | `⊢ P n` |

After R13 (`←`) and `rw [h3]` the goal is a ring identity of the shape `a * (s * a) = s * a ^ 2`: `ring` closes it.

---

## Part 2 · `not_sq_of_three_mod_four` (MILESTONE)

Statement: for a prime `p` with `p % 4 = 3` and any `x : ZMod p`, `x ^ 2 ≠ -1`. Start with `intro hx`; the goal
is `False`.

**R17 · `rintro rfl`** changes the **goal and the context**. On a goal `x ≠ 0` (that is, `x = 0 → False`) with
`x` a local variable, it introduces the equation and substitutes `0` for `x` everywhere. Placeholders:
`{α : Type} [Zero α] (Q : α → Prop) (x : α)`. Use it inside `have hx0 : x ≠ 0 := by …`.

| Before | After |
|---|---|
| `hx : Q x ⊢ x ≠ 0` | `hx : Q 0 ⊢ False` |

**R18 · `simp at hx`** **closes** the goal when `hx` simplifies to `False`. Here `(0 : ZMod p) ^ 2 = -1` becomes
`0 = -1` (`zero_pow`), then `1 = 0` (`zero_eq_neg`), which `simp` refutes with `one_ne_zero`: `1 ≠ 0` in
`ZMod p` because `p > 1`, which `simp` gets from the instance `[Fact p.Prime]`. Placeholders: `(p : ℕ) [Fact p.Prime]`.

| Before | After |
|---|---|
| `hx : 0 ^ 2 = -1 ⊢ G` | no goals |

**R19 · `(Fact.out : p.Prime).two_le`** changes the **context**. `Fact.out` extracts the proposition from the
instance `[Fact p.Prime]` (the type ascription says which `Fact`), and `Nat.Prime.two_le : p.Prime → 2 ≤ p`. The
dot notation `h.two_le` means `Nat.Prime.two_le h`. Placeholders: `(p : ℕ) [Fact p.Prime]`.

| Before | After |
|---|---|
| `⊢ G` | `h2 : 2 ≤ p ⊢ G` |

**R20 · `haveI : Fact (2 < n) := ⟨h⟩`** changes the **context**: it adds an instance, which later lemmas with
`[Fact (2 < n)]` find by themselves. `⟨h⟩` builds the `Fact` from `h : 2 < n`; you can write
`⟨by omega⟩` with R19's fact in context. (In tactic mode plain `have` also works.) Placeholders: `(n : ℕ) (h : 2 < n)`.

| Before | After |
|---|---|
| `h : 2 < n ⊢ G` | `this : Fact (2 < n) ⊢ G` |

**R21 · `have hf := ZMod.pow_card_sub_one_eq_one ha`** changes the **context**. This is Fermat's little theorem:
`ZMod.pow_card_sub_one_eq_one [Fact p.Prime] {a : ZMod p} : a ≠ 0 → a ^ (p - 1) = 1`. Placeholders:
`(p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0)`.

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ G` | `hf : a ^ (p - 1) = 1 ⊢ G` |

**R22 · `obtain ⟨k, hk⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩`** changes the **context**: it states an
existential, proves it with the witness `n / 3` (`omega` uses `h : n % 3 = 1`), and destructs it at once. Use the
same shape for `p - 1 = 2 * (2 * k + 1)` from `p % 4 = 3` (witness `p / 4`). Placeholders: `(n : ℕ) (h : n % 3 = 1)`.

| Before | After |
|---|---|
| `h : n % 3 = 1 ⊢ G` | `hk : n = 3 * k + 1 ⊢ G` |

**R23 · `rw [pow_mul] at h`** changes the **context**. The lemma is `pow_mul : a ^ (m * n) = (a ^ m) ^ n`.
Placeholders: `{M : Type} [Monoid M] (a : M) (m n : ℕ)` (`M` has `*` and `1`; every ring qualifies). After
`rw [hk] at hf`, R23 turns `x ^ (2 * (2k + 1))` into `(x ^ 2) ^ (2k + 1)`, where `rw [hx]` applies.

| Before | After |
|---|---|
| `h : Q (a ^ (m * n)) ⊢ G` | `h : Q ((a ^ m) ^ n) ⊢ G` |

**R24 · `rw [(odd_two_mul_add_one k).neg_one_pow]`** changes the **goal**. `odd_two_mul_add_one k : Odd (2 * k + 1)`
and `Odd.neg_one_pow : Odd n → (-1) ^ n = -1`; together they are the equation `(-1) ^ (2 * k + 1) = -1`.
Placeholders: `{R : Type} [Ring R] (k : ℕ)`. The exponent must be literally `2 * k + 1`.

| Before | After |
|---|---|
| `⊢ P ((-1) ^ (2 * k + 1))` | `⊢ P (-1)` |

**W2** chains R23 → `rw [hx]` → R24 on `x ^ (2 * (2 * 1 + 1)) = -1` in `ZMod 7`:

```lean-goal
⊢ x ^ (2 * (2 * 1 + 1)) = -1
⊢ (x ^ 2) ^ (2 * 1 + 1) = -1
⊢ (-1) ^ (2 * 1 + 1) = -1
```

**R25 · `exact ZMod.neg_one_ne_one h`** **closes** `False`. The lemma is
`ZMod.neg_one_ne_one [Fact (2 < n)] : (-1 : ZMod n) ≠ 1`, which needs the instance from R20. Placeholders:
`(n : ℕ) [Fact (2 < n)] (h : (-1 : ZMod n) = 1)`.

| Before | After |
|---|---|
| `h : -1 = 1 ⊢ False` | no goals |

---

## Part 3 · `neg_one_sq_iff` (the spec)

Statement: for a prime `p`, `(∃ x : ZMod p, x ^ 2 = -1) ↔ p % 4 ≠ 3`. Split with `constructor` (E005).

**R26 · `rintro ⟨x, hx⟩ hab`** changes the **goal and the context**: it introduces the `∃` (destructed into
`x` and `hx`) and, since `a ≠ b` is `a = b → False`, also `hab : a = b`. Placeholders:
`{α : Type} (Q : α → Prop) (a b : ℕ)`. Then Part 2 finishes the (→) direction.

| Before | After |
|---|---|
| `⊢ (∃ x, Q x) → a ≠ b` | `x : α, hx : Q x, hab : a = b ⊢ False` |

**R27 · `rcases hp.eq_two_or_odd' with rfl | ⟨m, hm⟩`** changes the **goal list**. The lemma is
`Nat.Prime.eq_two_or_odd' : p.Prime → p = 2 ∨ Odd p`. The pattern `rfl` substitutes `2` for `p` in the first
goal; `⟨m, hm⟩` unpacks `Odd p` in the second. In the exercise `hp` is `(Fact.out : p.Prime)` (R19).
Placeholders: `(p : ℕ) (hp : p.Prime)`.

| Before | After |
|---|---|
| `⊢ P p` | `⊢ P 2`, `hm : p = 2 * m + 1 ⊢ P p` |

**R28 · `decide +revert`** **closes** a goal about concrete elements of `ZMod 3` (or `ZMod 2`). Plain `decide`
fails with "Expected type must not contain free variables": the instance `inst✝ : Fact (Nat.Prime 3)` from the
context is inside the goal's `^`. `+revert` moves it into the goal first. Give the witness with `refine ⟨w, ?_⟩`.

| Before | After |
|---|---|
| `inst✝ : Fact (Nat.Prime 3) ⊢ 2 ^ 2 = 1` | no goals |

**R29 · `obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩`** changes the **goal and the context**:
as R22, but the pattern `rfl` substitutes `3 * k + 1` for `n` everywhere, instances included. Use it to make
`p` literally `2 * (2 * k) + 1`, so `half_factorial` (with `n := 2 * k`) matches. Placeholders: `(n : ℕ) (h : n % 3 = 1)`.

| Before | After |
|---|---|
| `h : n % 3 = 1 ⊢ P n` | `h : (3 * k + 1) % 3 = 1 ⊢ P (3 * k + 1)` |

Then give the witness: `refine ⟨((2 * k).factorial : ZMod (2 * (2 * k) + 1)), ?_⟩` (TACTIC_STATES).

**R30 · `have hw := ZMod.wilsons_lemma (p := q)`** changes the **context**. This is Wilson's theorem:
`ZMod.wilsons_lemma (p : ℕ) [Fact p.Prime] : (↑(p - 1)! : ZMod p) = -1`. `(p := q)` names the argument
explicitly; the instance is found in the context. Placeholders: `(q : ℕ) [Fact q.Prime]`.

| Before | After |
|---|---|
| `⊢ G` | `hw : ↑(q - 1).factorial = -1 ⊢ G` |

**R31 · `rw [Nat.add_sub_cancel]`** changes the **goal** (or, with `at hw`, the context). The lemma is
`n + m - m = n`; it turns `(2 * (2 * k) + 1 - 1)!` into `(2 * (2 * k))!`. Placeholders: `(n m : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (n + m - m)` | `⊢ P n` |

**W3** chains R20 → R30 → R31 `at hw` in `ZMod (2 * 2 + 1)` (Wilson for `5`), then `exact hw`:

| Before `rw [Nat.add_sub_cancel] at hw` | After |
|---|---|
| `hw : ↑(2 * 2 + 1 - 1).factorial = -1 ⊢ ↑(2 * 2).factorial = -1` | `hw : ↑(2 * 2).factorial = -1 ⊢ ↑(2 * 2).factorial = -1` |

After `rw [half_factorial] at hw`, `hw` reads `(-1) ^ (2 * k) * ↑(2 * k)! ^ 2 = -1`. Clean the sign with R23
(`(-1) ^ (2 * k)` → `((-1) ^ 2) ^ k`), then R32, R33, R34; `hw` is then the goal.

**R32 · `rw [neg_one_sq]`** changes the **goal**. The lemma is `(-1) ^ 2 = 1`. Placeholders: `{R : Type} [Ring R]`.

| Before | After |
|---|---|
| `⊢ P ((-1) ^ 2)` | `⊢ P 1` |

**R33 · `rw [one_pow]`** changes the **goal**. The lemma is `1 ^ n = 1`. Placeholders:
`{M : Type} [Monoid M] (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (1 ^ n)` | `⊢ P 1` |

**R34 · `rw [one_mul]`** changes the **goal**. The lemma is `1 * a = a`. Placeholders: `{M : Type} [Monoid M] (a : M)`.

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

---

## Traps

- `x ^ 2 = -1` lives in `ZMod p`, but `p % 4 = 3` lives in `ℕ`. A natural `k` written into `ZMod p` is a cast
  `↑k`, and `↑p = 0` there. Keep arithmetic about `p` in `ℕ` (`omega`) and move to `ZMod` only through casts.
- `ℕ` subtraction truncates: `n - i` and `p - 1` are only what you expect with a bound in context. Give `omega`
  that bound (`hi : i < n` via R4, `2 ≤ p` via R19).
- `rw [h]` with `h : ∀ x ∈ s, f x = g x` fails under `∏`: use `rw [Finset.prod_congr rfl h]` (R14).
- `h3` is an equation in `ℕ`; the goal has its cast. Fold the cast back (`rw [← Nat.cast_prod]`) before `rw [h3]`.
- `ZMod.neg_one_ne_one` needs the instance `Fact (2 < p)`, which nothing provides until you add it (R20).
- In the case `p = 2`, plain `decide` fails because the local `Fact` instance is a free variable: `decide +revert` (R28).
- `half_factorial` is stated for `ZMod (2 * n + 1)`. Make `p` literally `2 * (2 * k) + 1` with `obtain ⟨k, rfl⟩`
  (R29), not with a hypothesis `hk : p = …`, or `rw [half_factorial]` will not find its pattern.
- `IsSquare`, the Legendre symbol, Euler's criterion and Mathlib's own versions of this theorem are banned; use
  the explicit `∃ x, x ^ 2 = -1` and Fermat/Wilson.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| fold `∏ i ∈ range k, (n + i)` | `rw [← Nat.ascFactorial_eq_prod_range]` | R1 |
| `n ! * (n+1).ascFactorial k` → `(n + k)!` | `rw [Nat.factorial_mul_ascFactorial]` | R2 |
| `2 * a` → `a + a` | `rw [two_mul]` | R3 |
| `i ∈ range n` → `i < n` | `rw [Finset.mem_range] at hi` | R4 |
| `a = -b` → `a + b = 0` | `rw [eq_neg_iff_add_eq_zero]` | R5 |
| `↑m + ↑n` → `↑(m + n)` | `rw [← Nat.cast_add]` | R6 |
| `(↑a : ZMod b) = 0` → `b ∣ a` | `rw [ZMod.natCast_eq_zero_iff]` | R7 |
| replace an `ℕ` expression | `rw [show e₁ = e₂ by omega]` | R8 |
| `n !` → `∏ i ∈ range n, (i + 1)` | `rw [← Finset.prod_range_add_one_eq_factorial]` | R9 |
| reverse a product over `range n` | `rw [← Finset.prod_range_reflect]` | R10 |
| equal products from equal factors | `refine Finset.prod_congr rfl ?_` | R11 |
| cast of `*` / of `∏` | `rw [Nat.cast_mul]` / `rw [Nat.cast_prod]` (`←` folds) | R12, R13 |
| rewrite every factor with `h` | `rw [Finset.prod_congr rfl h]` | R14 |
| `∏ -f x` → `(-1) ^ #s * ∏ f x` | `rw [Finset.prod_neg]` | R15 |
| `#(range n)` → `n` | `rw [Finset.card_range]` | R16 |
| prove `x ≠ 0` by substituting | `rintro rfl` | R17 |
| a hypothesis that is `False` | `simp at hx` | R18 |
| `2 ≤ p` from `[Fact p.Prime]` | `(Fact.out : p.Prime).two_le` | R19 |
| add an instance | `haveI : Fact (2 < p) := ⟨by omega⟩` | R20 |
| Fermat: `a ^ (p - 1) = 1` | `ZMod.pow_card_sub_one_eq_one ha` | R21 |
| name a quotient | `obtain ⟨k, hk⟩ : ∃ k, … := ⟨p / 4, by omega⟩` | R22 |
| `a ^ (m * n)` → `(a ^ m) ^ n` | `rw [pow_mul] at h` | R23 |
| `(-1) ^ (2 * k + 1)` → `-1` | `rw [(odd_two_mul_add_one k).neg_one_pow]` | R24 |
| `(-1 : ZMod n) = 1` is false | `ZMod.neg_one_ne_one` (needs `Fact (2 < n)`) | R25 |
| intro `∃` and `≠` at once | `rintro ⟨x, hx⟩ h3` | R26 |
| `p = 2` or `p` odd | `rcases hp.eq_two_or_odd' with rfl \| ⟨m, hm⟩` | R27 |
| concrete `ZMod 2` goal | `decide +revert` | R28 |
| substitute `p = 2 * (2 * k) + 1` | `obtain ⟨k, rfl⟩ : ∃ k, … := ⟨p / 4, by omega⟩` | R29 |
| Wilson: `↑(p - 1)! = -1` | `have hw := ZMod.wilsons_lemma (p := …)` | R30 |
| `n + m - m` → `n` | `rw [Nat.add_sub_cancel]` | R31 |
| `(-1) ^ 2`, `1 ^ n`, `1 * a` | `rw [neg_one_sq, one_pow, one_mul]` | R32–R34 |
| see the state | infoview | |
