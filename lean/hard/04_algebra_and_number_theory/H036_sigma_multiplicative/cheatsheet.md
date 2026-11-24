# H036 · σ is multiplicative: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `intro`, `exact`, `have`, `rw`, `constructor`,
anonymous constructors `⟨_, _⟩`, `∃`/`∧`/`↔`/`¬`, `Nat`. **New here:** Mathlib's finite sets (`Finset`),
big sums `∑ x ∈ s, f x`, products of finsets `s ×ˢ t`, images `image f s`, the divisor finset
`Nat.divisors`, divisibility `∣`, `Nat.gcd`, `Nat.Coprime`, injectivity on a set `Set.InjOn`, the
finset-to-set coercion `↑s`, and the term-level tools `▸`, dot notation and `|>.`.

**The maths.** Write $\sigma(k) = \sum_{d \mid k} d$ (the sum of the positive divisors of $k \in ℕ$).
For coprime $m, n$ (that is, $\gcd(m, n) = 1$):

1. *Surjectivity* (`divisors_eq`). Every divisor $d$ of $mn$ is $d = \gcd(d, m) \cdot \gcd(d, n)$, a product of a
   divisor of $m$ and a divisor of $n$: coprimality gives $\gcd(d, mn) = \gcd(d, m)\gcd(d, n)$, and
   $\gcd(d, mn) = d$ because $d \mid mn$. Conversely $a \mid m$, $b \mid n$ give $ab \mid mn$.
2. *Injectivity* (`mul_inj`). If $ab = a'b'$ with $a, a' \mid m$ and $b, b' \mid n$, then $a$ is coprime to $b'$
   (a divisor of $m$ against a divisor of $n$), and $a \mid a'b'$, so $a \mid a'$. Symmetrically $a' \mid a$, so
   $a = a'$, and cancelling $a > 0$ gives $b = b'$. Without coprimality this fails: $m = n = 4$, $2 \cdot 2 = 4 \cdot 1$.
3. *Reindexing* (`sigma_mul`). By 1 and 2 the map $(a, b) \mapsto ab$ is a bijection from
   $\mathrm{Div}(m) \times \mathrm{Div}(n)$ onto $\mathrm{Div}(mn)$, so
   $\sigma(mn) = \sum_{(a,b)} ab = \left(\sum_a a\right)\left(\sum_b b\right) = \sigma(m)\sigma(n)$.

## How to read an entry

Each entry is one tactic, one lemma used with `rw`/`simp`/`exact`, or one term-building move. It says what
changes (**goal**, **context**, or **goal list**), gives the lemma's statement, lists the placeholders with
their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : ℕ → Prop`). The step changes only the part inside `P (…)`.
- An entry about a *hypothesis* has goal `False` and an `h : … → False`: that only makes the example
  finish; watch the hypothesis change.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommSemigroup α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Finset α` | a finite set of elements of `α` (a list without duplicates or order) |
| `∑ x ∈ s, f x` | $\sum_{x \in s} f(x)$, the sum over the finset `s` (`Finset.sum s f`) |
| `n.divisors` | `Nat.divisors n`, the finset of $d \ge 1$ with $d \mid n$; it is `∅` for `n = 0` |
| `a ∣ n` | "`a` divides `n`" (typed `\mid`, not the keyboard bar): `∃ c, n = a * c` |
| `a.gcd n` | `Nat.gcd a n`, the greatest common divisor |
| `m.Coprime n` | `Nat.Coprime m n`, defined as `m.gcd n = 1` |
| `s ×ˢ t` | the product finset $\{(a, b) \mid a \in s, b \in t\}$; for sets the same notation |
| `α × β`, `(a, b)` | the type of pairs with first component in `α` and second in `β`; `(a, b)` is the pair itself (`ℕ × ℕ` in `mul_inj`) |
| `p.1`, `p.2` | the first and second component of a pair `p : α × β`; `(a, b).1` reduces to `a` |
| `Set α` | a set of elements of `α` (Mathlib's `Set α` is `α → Prop`; `x ∈ S` means `S x`) |
| `image f s` | the finset $\{f(x) \mid x \in s\}$ (written `s.image f` in source; printed `image f s`) |
| `∃ a ∈ s, Q a` | `∃ a, a ∈ s ∧ Q a` |
| `∃ a b, Q a b` | `∃ a, ∃ b, Q a b` |
| `↑s` | the finset `s` viewed as a `Set α` (a coercion; `Set.InjOn` wants a set) |
| `Set.InjOn f S` | `f` is injective on `S`: `∀ ⦃x₁⦄, x₁ ∈ S → ∀ ⦃x₂⦄, x₂ ∈ S → f x₁ = f x₂ → x₁ = x₂` |
| `∀ ⦃x⦄, …` | a *strict-implicit* argument: when applying the statement Lean fills `x` in from the next explicit argument; `intro`/`rintro` introduce it like any `∀` variable |
| `h1 h2 : a ∣ a` | two hypotheses with the same type, printed on one line |
| `(fun p => p.1 * p.2) (a, b)` | the function applied but not yet evaluated; it is `a * b` by definition (R20) |
| `a ≠ 0` | `a = 0 → False` (R11) |
| `case mp`, `case mpr` | the `→` and `←` halves of an `↔` after `constructor` (R6) |
| `a✝` | an unnamed (inaccessible) hypothesis; name it in `intro`/`rintro` to use it |

---

## Part 1 · `divisors_eq` (milestone)

Statement: for coprime `m n`, `(m * n).divisors = image (fun p => p.1 * p.2) (m.divisors ×ˢ n.divisors)`:
the divisors of `mn` are exactly the products `a * b` of a divisor of `m` and a divisor of `n`.

### Equality of finsets → membership

**R1 · `ext d`** changes the **goal and the context**. It uses `Finset.ext`: two finsets are equal when they
have the same members. Placeholders: `{α : Type} (s t : Finset α)`.

| Before | After |
|---|---|
| `⊢ s = t` | `d : α ⊢ d ∈ s ↔ d ∈ t` |

**R2 · `Finset.mem_image`** changes the **goal**: `b ∈ image f s ↔ ∃ a ∈ s, f a = b`. Use it with
`simp only [mem_image]` (it is an `↔`, so `rw` works too). Placeholders:
`{α β : Type} [DecidableEq β] (f : α → β) (s : Finset α) (b : β)`; `[DecidableEq β]` means equality on `β` is
decidable, true for `ℕ`.

| Before | After |
|---|---|
| `⊢ b ∈ image f s` | `⊢ ∃ a ∈ s, f a = b` |

**R3 · `Finset.mem_product`** changes the **goal**: `p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t`. Placeholders:
`{α β : Type} (s : Finset α) (t : Finset β) (p : α × β)`.

| Before | After |
|---|---|
| `⊢ p ∈ s ×ˢ t` | `⊢ p.1 ∈ s ∧ p.2 ∈ t` |

**R4 · `Nat.mem_divisors`** changes the **goal**: `a ∈ n.divisors ↔ a ∣ n ∧ n ≠ 0`. Placeholders: `(a n : ℕ)`.

| Before | After |
|---|---|
| `⊢ a ∈ n.divisors` | `⊢ a ∣ n ∧ n ≠ 0` |

**R5 · `Prod.exists`** changes the **goal**: `(∃ x : α × β, Q x) ↔ ∃ a b, Q (a, b)`, an existential over a
pair becomes one over its two components (and `simp` then reduces `(a, b).1` to `a`). Placeholders:
`{α β : Type} (Q : α × β → Prop)`.

| Before | After |
|---|---|
| `⊢ ∃ x, Q x` | `⊢ ∃ a b, Q (a, b)` |

**W1 · R2–R5 together.** On a sum image (not the exercise's product),
`simp only [mem_image, mem_product, Nat.mem_divisors, Prod.exists]` gives:

```lean-goal
⊢ x ∈ image (fun p => p.1 + p.2) (k.divisors ×ˢ l.divisors)
⊢ ∃ a b, ((a ∣ k ∧ k ≠ 0) ∧ b ∣ l ∧ l ≠ 0) ∧ a + b = x
```

### The two directions

**R6 · `constructor` on `↔`** changes the **goal list**: `A ↔ B` becomes `A → B` (case `mp`) and `B → A`
(case `mpr`). Placeholders: `(A B : Prop)`. Prove each with `·`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R7 · `rintro ⟨h1, h2⟩`** changes the **goal and the context**: it introduces `A ∧ B` and splits it.
Placeholders: `(A B C : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B → C` | `h1 : A, h2 : B ⊢ C` |

**R8 · `rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩`** changes the **goal and the context**. The pattern follows the shape
`∃ a, ∃ b, (Q a ∧ Q' b) ∧ f a b = x`; the last component `rfl` does not name the equation but *uses* it to
replace `x` by `f a b` everywhere (`x` must be a variable). Placeholders:
`{α γ : Type} (Q Q' : α → Prop) (f : α → α → γ) (G : γ → Prop) (x : γ)`.

| Before | After |
|---|---|
| `⊢ (∃ a b, (Q a ∧ Q' b) ∧ f a b = x) → G x` | `ha : Q a, hb : Q' b ⊢ G (f a b)` |

**R9 · `refine ⟨x, y, ⟨hA, hB⟩, ?_⟩`** changes the **goal**: it supplies the two witnesses and the proofs you
already have, and leaves each `?_` as a goal. Nested `⟨…⟩` follow the nesting of `∧`. Placeholders:
`(A B : ℕ → Prop) (E : ℕ → ℕ → Prop) (x y : ℕ)`.

| Before | After |
|---|---|
| `⊢ ∃ a b, (A a ∧ B b) ∧ E a b` | `⊢ E x y` |

**R10 · `Nat.gcd_dvd_right`** **closes** the goal: `Nat.gcd_dvd_right a n : a.gcd n ∣ n`. (Also
`Nat.gcd_dvd_left a n : a.gcd n ∣ a`.) Placeholders: `(a n : ℕ)`.

| Before | After |
|---|---|
| `⊢ a.gcd n ∣ n` | no goals |

**R11 · `a ≠ 0` from `a * b ≠ 0`** changes the **goal and the context**: `a ≠ 0` is a function type, so
`intro ha` assumes `a = 0` and the goal is `False`; `hab (by simp [ha])` closes it, since `simp` proves
`a * b = 0` from `a = 0` (`0 * b = 0`). As a term: `fun ha => hab (by simp [ha])`. The same works for the
right factor: from `hb : b = 0`, `simp [hb]` proves `a * b = 0` (`a * 0 = 0`). Placeholders: `(a b : ℕ)`.

| Before | After `intro ha` |
|---|---|
| `hab : a * b ≠ 0 ⊢ a ≠ 0` | `hab : a * b ≠ 0, ha : a = 0 ⊢ False` |

**R12 · `rw [← Nat.Coprime.gcd_mul k hc]`** changes the **goal**. The lemma is
`Nat.Coprime.gcd_mul (k : ℕ) (hc : m.Coprime n) : k.gcd (m * n) = k.gcd m * k.gcd n`; `←` folds the product of
gcds back into one gcd. This is where coprimality is used in Part 1. Placeholders: `(k m n : ℕ) (hc : m.Coprime n)`.

| Before | After |
|---|---|
| `⊢ P (k.gcd m * k.gcd n)` | `⊢ P (k.gcd (m * n))` |

**R13 · `rw [Nat.gcd_eq_left hd]`** changes the **goal**. The lemma is `Nat.gcd_eq_left : a ∣ n → a.gcd n = a`.
Placeholders: `(a n : ℕ) (hd : a ∣ n)`. When the goal becomes `a = a`, `rw` closes it with `rfl` by itself.

| Before | After |
|---|---|
| `⊢ P (a.gcd n)` | `⊢ P a` |

**W2 · R12 then R13 on `4 * 9`:**

```lean-goal
⊢ d.gcd 4 * d.gcd 9 = d
⊢ d.gcd (4 * 9) = d
```

and `rw [Nat.gcd_eq_left hd]` closes it.

**R14 · `mul_dvd_mul`** **closes** the goal: `mul_dvd_mul : a ∣ b → c ∣ d → a * c ∣ b * d`. Placeholders:
`{α : Type} [CommSemigroup α] (a b c d : α)` (a commutative, associative `*`; `ℕ` qualifies).

| Before | After |
|---|---|
| `h1 : a ∣ b, h2 : c ∣ d ⊢ a * c ∣ b * d` | no goals |

**R15 · `mul_ne_zero`** **closes** the goal: `mul_ne_zero : a ≠ 0 → b ≠ 0 → a * b ≠ 0` (no zero divisors).
Placeholders: `(a b : ℕ)`.

| Before | After |
|---|---|
| `ha : a ≠ 0, hb : b ≠ 0 ⊢ a * b ≠ 0` | no goals |

---

## Part 2 · `mul_inj` (milestone)

Statement: for coprime `m n`, `Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ↑(m.divisors ×ˢ n.divisors)`: on pairs
(divisor of `m`, divisor of `n`), the product determines the pair.

### Opening `InjOn` and cleaning the hypotheses

**R16 · `rintro ⟨a, b⟩ hp ⟨a', b'⟩ hq heq`** changes the **goal and the context**. `Set.InjOn f s` is a `∀`
statement (see *Reading the goals*); `rintro` introduces both points, splitting each pair, their memberships and
the equation. Placeholders: `{α β γ : Type} (f : α × β → γ) (s : Set (α × β))`.

| Before | After |
|---|---|
| `⊢ Set.InjOn f s` | `⊢ (a, b) = (a', b')` |

The context gains `a : α`, `b : β`, `hp : (a, b) ∈ s`, `a' : α`, `b' : β`, `hq : (a', b') ∈ s` and
`heq : f (a, b) = f (a', b')`. With `f` a `fun`, as in the exercise, `heq` shows that `fun` applied to the
pairs (R20).

**R17 · `simp only [coe_product] at hp`** changes the **context**. The lemma `Finset.coe_product` is
`↑(s ×ˢ t) = ↑s ×ˢ ↑t`: the set of a product finset is the product of the sets. `at hp` rewrites the
hypothesis instead of the goal. Placeholders: `{α β : Type} (s : Finset α) (t : Finset β) (p : α × β)`.

| Before | After |
|---|---|
| `hp : p ∈ ↑(s ×ˢ t) ⊢ False` | `hp : p ∈ ↑s ×ˢ ↑t ⊢ False` |

**R18 · `simp only [Set.mem_prod] at hp`** changes the **context**: `p ∈ S ×ˢ T ↔ p.1 ∈ S ∧ p.2 ∈ T` for sets.
Placeholders: `{α β : Type} (S : Set α) (T : Set β) (p : α × β)`. On a pair `(a, b)`, `simp` also reduces
`(a, b).1` to `a`, giving `a ∈ S ∧ b ∈ T`.

| Before | After |
|---|---|
| `hp : p ∈ S ×ˢ T ⊢ False` | `hp : p.1 ∈ S ∧ p.2 ∈ T ⊢ False` |

**R19 · `simp only [mem_coe] at hp`** changes the **context**: `Finset.mem_coe : a ∈ ↑s ↔ a ∈ s`. After it,
`Nat.mem_divisors` (R4) applies. Placeholders: `{α : Type} (s : Finset α) (a : α)`.

| Before | After |
|---|---|
| `hp : a ∈ ↑s ⊢ False` | `hp : a ∈ s ⊢ False` |

R17, R18, R19 and R4 go in one `simp only […] at hab hab'`. Each hypothesis then reads
`(a ∣ m ∧ m ≠ 0) ∧ b ∣ n ∧ n ≠ 0`, so `hab.1.1 : a ∣ m`, `hab.1.2 : m ≠ 0`, `hab.2.1 : b ∣ n`.

**R20 · `change T at heq`** changes the **context**: it replaces the type of `heq` by `T`, which must be equal
to it by definition (Lean checks this). Here it evaluates the function at the pair. Placeholders: `(a b c d : ℕ)`.

| Before | After |
|---|---|
| `heq : (fun p => p.1 + p.2) (a, b) = (fun p => p.1 + p.2) (c, d)` | `heq : a + b = c + d ⊢ False` |

### Coprimality gives `a ∣ a'`

**R21 · `hc.coprime_dvd_left ha`** adds to the **context** (via `have`). The lemma is
`Nat.Coprime.coprime_dvd_left : a ∣ m → m.Coprime n → a.Coprime n`: a divisor of `m` is still coprime to `n`.
*Dot notation:* for `hc : m.Coprime n`, `hc.coprime_dvd_left ha` is `Nat.Coprime.coprime_dvd_left ha hc` (`hc`
goes to the first argument whose type is `Nat.Coprime …`). Placeholders: `(a m n : ℕ)`.

| Before | After `have h1 : a.Coprime n := hc.coprime_dvd_left ha` |
|---|---|
| `hc : m.Coprime n, ha : a ∣ m ⊢ False` | `h1 : a.Coprime n ⊢ False` |

**R22 · `hc.coprime_dvd_right hb`** adds to the **context**. The lemma is
`Nat.Coprime.coprime_dvd_right : b ∣ n → a.Coprime n → a.Coprime b`. Placeholders: `(a b n : ℕ)`.

| Before | After `have h1 : a.Coprime b := hc.coprime_dvd_right hb` |
|---|---|
| `hc : a.Coprime n, hb : b ∣ n ⊢ False` | `h1 : a.Coprime b ⊢ False` |

**R23 · `hc.dvd_of_dvd_mul_right hd`** adds to the **context**. The lemma is
`Nat.Coprime.dvd_of_dvd_mul_right : k.Coprime n → k ∣ m * n → k ∣ m` (Euclid's lemma: a factor coprime to `k`
can be dropped). Placeholders: `(k m n : ℕ)`.

| Before | After `have h1 : k ∣ m := hc.dvd_of_dvd_mul_right hd` |
|---|---|
| `hc : k.Coprime n, hd : k ∣ m * n ⊢ False` | `h1 : k ∣ m ⊢ False` |

**R24 · `dvd_mul_right`** **closes** the goal: `dvd_mul_right a b : a ∣ a * b`. Placeholders:
`{α : Type} [Semigroup α] (a b : α)` (an associative `*`; `ℕ` qualifies).

| Before | After |
|---|---|
| `⊢ a ∣ a * b` | no goals |

**R25 · `heq ▸ e`** adds to the **context** (via `have`): for `heq : x = y` and `e : P x` it is a term of type
`P y`, the type of `e` rewritten by `heq`. It needs the expected type (`have h1 : P y := …`) to know where to
rewrite; it tries `heq` in both directions. Placeholders: `{α : Type} (x y : α) (P : α → Prop)`.

| Before | After `have h1 : P y := heq ▸ e` |
|---|---|
| `heq : x = y, e : P x ⊢ False` | `h1 : P y ⊢ False` |

**W3 · the chain, written with `|>.`.** `e |>.f x` means `(e).f x`: it continues a dot chain on the result
of `e` and saves a pair of parentheses. With `a ∣ 4`, `b' ∣ 9`, `heq : a * b = a' * b'`:
`(hc.coprime_dvd_left ha).coprime_dvd_right hb' |>.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right a b)`
proves `a ∣ a'` (R21 → R22 → R23, the divisibility from R24 moved along `heq` by R25).

### From two divisibilities to equal pairs

**R26 · `Nat.dvd_antisymm`** adds to the **context**: `Nat.dvd_antisymm : a ∣ b → b ∣ a → a = b`.
Placeholders: `(a b : ℕ)`.

| Before | After `have h3 : a = b := Nat.dvd_antisymm h1 h2` |
|---|---|
| `h1 : a ∣ b, h2 : b ∣ a ⊢ False` | `h3 : a = b ⊢ False` |

**R27 · `obtain rfl := e`** changes the **context**: with `e : a = a'` (where `a'` is a local variable), it
replaces `a'` by `a` in every hypothesis and the goal, and `a'` disappears. Placeholders: `(a a' b b' : ℕ)`.

| Before | After |
|---|---|
| `e : a = a', heq : a * b = a' * b' ⊢ False` | `heq : a * b = a * b' ⊢ False` |

**R28 · `Nat.pos_of_ne_zero`** **closes** the goal: `n ≠ 0 → 0 < n`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `hn : n ≠ 0 ⊢ 0 < n` | no goals |

**R29 · `Nat.pos_of_dvd_of_pos`** **closes** the goal: `a ∣ n → 0 < n → 0 < a` (a divisor of a positive number
is positive). Placeholders: `(a n : ℕ)`.

| Before | After |
|---|---|
| `hd : a ∣ n, hn : 0 < n ⊢ 0 < a` | no goals |

**R30 · `Nat.eq_of_mul_eq_mul_left`** **closes** the goal: `0 < a → a * b = a * c → b = c` (cancel `a`).
Placeholders: `(a b c : ℕ)`.

| Before | After |
|---|---|
| `ha : 0 < a, heq : a * b = a * c ⊢ b = c` | no goals |

**R31 · `Prod.ext`** **closes** (or splits) the goal: `Prod.ext : p.1 = q.1 → p.2 = q.2 → p = q`. For
`(a, b) = (a, c)` the first component is `rfl`, since `(a, b).1` reduces to `a`. Placeholders:
`{α β : Type} (a : α) (b c : β)`.

| Before | After `exact Prod.ext rfl hbc` |
|---|---|
| `hbc : b = c ⊢ (a, b) = (a, c)` | no goals |

---

## Part 3 · `sigma_mul`

Statement: for coprime `m n`, `∑ d ∈ (m * n).divisors, d = (∑ d ∈ m.divisors, d) * (∑ d ∈ n.divisors, d)`.
With the two milestones it is one `rw` chain: replace `(m * n).divisors` by the image (`rw [divisors_eq m n h]`),
then R32, R33, R34; the two sides then agree by evaluation and `rw` closes the goal with `rfl`.

**R32 · `rw [sum_image hg]`** changes the **goal**. The lemma is
`Finset.sum_image : Set.InjOn g ↑s → ∑ x ∈ image g s, f x = ∑ x ∈ s, f (g x)`: summing over the image is summing
over `s`, provided `g` takes no value twice on `s`. Placeholders:
`{κ ι : Type} [DecidableEq ι] (s : Finset κ) (g : κ → ι) (f : ι → ℕ) (hg : Set.InjOn g ↑s)`
(`[DecidableEq ι]` as in R2; `ℕ` qualifies). In `sigma_mul`, `f` is `fun d => d` and `g` is
`fun p => p.1 * p.2`, so Lean prints `f (g x)` already evaluated, as `x.1 * x.2`. Without `hg`,
`rw [sum_image]` adds the goal `Set.InjOn g ↑s` (W4).

| Before | After |
|---|---|
| `⊢ P (∑ x ∈ image g s, f x)` | `⊢ P (∑ x ∈ s, f (g x))` |

**R33 · `rw [sum_mul_sum]`** changes the **goal**. The lemma is
`Finset.sum_mul_sum : (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j` (distributivity).
Placeholders: `{ι κ : Type} (s : Finset ι) (t : Finset κ) (f : ι → ℕ) (g : κ → ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((∑ i ∈ s, f i) * ∑ j ∈ t, g j)` | `⊢ P (∑ i ∈ s, ∑ j ∈ t, f i * g j)` |

**R34 · `rw [sum_product]`** changes the **goal**. The lemma is
`Finset.sum_product : ∑ x ∈ s ×ˢ t, f x = ∑ x ∈ s, ∑ y ∈ t, f (x, y)` (a sum over pairs is a double sum).
Placeholders: `{α β : Type} (s : Finset α) (t : Finset β) (f : α × β → ℕ)`.

| Before | After |
|---|---|
| `⊢ P (∑ x ∈ s ×ˢ t, f x)` | `⊢ P (∑ x ∈ s, ∑ y ∈ t, f (x, y))` |

**W4 · `rw [sum_image]` without its argument** on `∑ x ∈ image (fun k => 2 * k) (range 4), x`
(`range 4 = {0, 1, 2, 3}`): the sums now agree, and the injectivity is left as a goal:

```lean-goal
⊢ Set.InjOn (fun k => 2 * k) ↑(range 4)
```

**W5 · R33 on one side, R34 on the other.** For any `s t : Finset ℕ`:

```lean-goal
⊢ (∑ i ∈ s, (i + 1)) * ∑ j ∈ t, j = ∑ p ∈ s ×ˢ t, (p.1 + 1) * p.2
⊢ ∑ i ∈ s, ∑ j ∈ t, (i + 1) * j = ∑ p ∈ s ×ˢ t, (p.1 + 1) * p.2
```

then `rw [sum_product]` turns the right side into the same double sum and closes the goal.

---

## Traps

- The milestones are separate theorems: in `sigma_mul`, use them as `divisors_eq m n h` and `mul_inj m n h`.
- `rw [sum_image]` with no argument does not fail: it adds a `Set.InjOn` goal at the end of the goal list (W4).
  Pass the proof: `sum_image (mul_inj m n h)`.
- `Nat.divisors 0 = ∅`, so every membership carries an `n ≠ 0` (R4). In Part 1, `m ≠ 0` comes from
  `m * n ≠ 0` (R11), and in Part 2 the positivity of `a` comes from `a ∣ m` and `m ≠ 0` (R28, R29).
- After `rintro` on `Set.InjOn`, `heq` is stated with the unevaluated function; `Nat` lemmas will not match
  it until `change a * b = a' * b' at heq` (R20).
- `hab.1.1` follows the nesting `(a ∣ m ∧ m ≠ 0) ∧ b ∣ n ∧ n ≠ 0`: `.1` is the left part of `∧`, `.2` the
  right part, and `∧` nests to the right.
- Coprimality is needed exactly twice: the gcd split in Part 1 (R12) and Euclid's lemma in Part 2 (R23).
  Without it, `m = n = 4` and `2 * 2 = 4 * 1` break injectivity.
- `▸` needs an expected type: write it inside `have h : T := …` or as an argument whose type Lean knows (R25).
- `∣` is `\mid` (or `\|`), not the keyboard `|`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| finset equality → membership | `ext d` | R1 |
| unfold image / product / divisors / pair `∃` | `simp only [mem_image, mem_product, Nat.mem_divisors, Prod.exists]` | R2–R5 |
| split `↔` | `constructor` | R6 |
| destructure `∧`, `∃`, substitute an equation | `rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩` | R7, R8 |
| give witnesses | `refine ⟨x, y, ⟨_, _⟩, ?_⟩` | R9 |
| `a.gcd n ∣ n` | `Nat.gcd_dvd_right a n` | R10 |
| `a ≠ 0` from `a * b ≠ 0` | `fun ha => hab (by simp [ha])` | R11 |
| `k.gcd m * k.gcd n → k.gcd (m * n)` (coprime) | `rw [← Nat.Coprime.gcd_mul k hc]` | R12 |
| `a.gcd n → a` when `a ∣ n` | `rw [Nat.gcd_eq_left hd]` | R13 |
| `a * c ∣ b * d`, `a * b ≠ 0` | `mul_dvd_mul h1 h2`, `mul_ne_zero ha hb` | R14, R15 |
| open `Set.InjOn` on pairs | `rintro ⟨a, b⟩ hp ⟨a', b'⟩ hq heq` | R16 |
| clean `(a, b) ∈ ↑(s ×ˢ t)` | `simp only [coe_product, Set.mem_prod, mem_coe, Nat.mem_divisors] at hp` | R17–R19, R4 |
| evaluate `(fun p => …) (a, b)` in a hypothesis | `change a * b = a' * b' at heq` | R20 |
| divisor of `m` coprime to divisor of `n` | `(hc.coprime_dvd_left ha).coprime_dvd_right hb` | R21, R22 |
| Euclid: `k ∣ m * n`, `k ⊥ n` → `k ∣ m` | `hc.dvd_of_dvd_mul_right hd` | R23 |
| `a ∣ a * b`, moved along `heq` | `heq ▸ dvd_mul_right a b` | R24, R25 |
| continue a dot chain | `e \|>.f x` | W3 |
| `a ∣ b`, `b ∣ a` → `a = b` | `Nat.dvd_antisymm h1 h2` | R26 |
| substitute a variable | `obtain rfl := e` | R27 |
| positivity of a divisor | `Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn)` | R28, R29 |
| cancel a positive factor | `Nat.eq_of_mul_eq_mul_left ha heq` | R30 |
| equal pairs | `Prod.ext rfl hbc` | R31 |
| sum over an image | `rw [sum_image hg]` | R32 |
| product of sums → double sum | `rw [sum_mul_sum]` | R33 |
| sum over `s ×ˢ t` → double sum | `rw [sum_product]` | R34 |
| see the state | infoview | |
