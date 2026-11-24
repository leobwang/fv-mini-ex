# H033 · Wilson's theorem in a finite field: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). The `n.factorial + 1` idea of H029 (a number `m ≤ k`
with `0 < m` divides `k.factorial`, so it cannot divide `k.factorial + 1` unless `m = 1`) is reused in
Part 4, but H029 itself is not needed.
**New here:** Mathlib's fields and their inverse `⁻¹`, finite sets (`Finset`) and products over them
(`∏`), the pairing lemma `Finset.prod_involution`, and Mathlib's `Nat.Prime`, `∣`, `Nat.factorial`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`, or `P : Prop` when the step only changes a
  hypothesis). The step changes only the part inside `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Field K]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `{K : Type*} [Field K]` | `K` is any field (`ℚ`, `ℝ`, `ℂ`, `ZMod p` for a prime `p`, …). `Type*` is `Type` at any universe level; the infoview shows it as `K : Type u_1` (`u_1` is that level) |
| `[Fintype K]` | `K` has finitely many elements; this is what makes `Finset.univ : Finset K` exist |
| `[DecidableEq K]` | `a = b` can be decided for `a b : K`; Lean needs it to compute `s.erase a`, `s \ t`, `{a, b}` |
| `inst✝ : Field K` | an instance argument from a bracket; the `✝` marks a name you cannot type |
| `x⁻¹` | the field inverse. Mathlib sets `0⁻¹ = 0`, so `x * x⁻¹ = 1` needs `x ≠ 0` (R11) |
| `Finset α` | a finite set of elements of `α` |
| `Finset.univ` | the finite set of all elements of a `Fintype` |
| `s.erase a` | `s` with `a` removed (`Finset.erase s a`) |
| `s \ t` | set difference: elements of `s` not in `t` |
| `Finset.univ.erase 0 \ {1, -1}` | `(Finset.univ.erase 0) \ {1, -1}`: the dot call `.erase 0` binds tighter than `\`, so Lean prints it without parentheses. `0`, `1`, `-1` are elements of `K` here |
| `{a, b}` | `insert a {b}`: the set with elements `a`, `b`. When `a = b` it is `{a}` (R23) |
| `a ∉ t` | `¬(a ∈ t)` |
| `∏ x ∈ s, f x` | the product of `f x` over all `x ∈ s` (`Finset.prod s f`); the empty product is `1`. Order does not matter, so the codomain must be a commutative monoid `[CommMonoid M]` (any field, `ℕ`, …) |
| `∀ a ∈ s, Q a` | bounded quantifier: `∀ a, a ∈ s → Q a`; `intro a ha` gives `a` and `ha : a ∈ s` (R5's four goals look like this) |
| `(·⁻¹)` | the function `fun x => x⁻¹`; `·` marks the argument (R15) |
| `s ⊆ t` | every element of `s` is in `t`; unfolds to `∀ ⦃x⦄, x ∈ s → x ∈ t` (R18) |
| `a ≠ b` | `a = b → False`. After `simp` it may print as `¬a = b`: the same proposition |
| `m ∣ n` | `m` divides `n` (typed `\|`, not the bar `|`) |
| `Nat.Prime p` | `p` is prime (also written `p.Prime`); unfold it with R26 |
| `n.factorial` | `Nat.factorial n`, the factorial `n!`. The GOAL text writes it `n !` (Mathlib notation, available after `open Nat`); for a numeral Lean prints `Nat.factorial 4` |
| `h1 : 1 = -1` | after `by_cases h1 : (1 : K) = -1` the infoview drops the `: K`; it is still an equation in `K` |
| `a✝ : a ≠ 1`, `h✝`, `ha✝` | a hypothesis introduced as `_`, or one shadowed by a later hypothesis of the same name: it has no usable name |
| `case refine_1`, `case pos`, `case inl` | labels of goals produced by `refine`, `by_cases`, `rcases` |

---

## Part 1 · `sq_eq_one` (milestone)

Statement: in a field, `x * x = 1 → x = 1 ∨ x = -1`. Factor: `(x - 1) * (x + 1) = 0`, and a field has no
zero divisors.

**R1 · `linear_combination h`** **closes** an equation that follows from the equation `h` by `ring`: it
checks that `(goal.lhs - goal.rhs) - (h.lhs - h.rhs)` is `0` as a polynomial identity.
`linear_combination c * h` uses `c` times `h`. Placeholders: `{K : Type} [Field K] (a b c : K)`,
`h : a * b = c`. Use it inside `have h' : (…) * (…) = 0 := by linear_combination h`.

| Before | After |
|---|---|
| `h : a * b = c ⊢ a * b - c = 0` | `∅` |

**R2 · `rcases mul_eq_zero.mp h with ha | hb`** changes the **goal list and the context**. The lemma is
`mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0` (needs `[MulZeroClass M₀] [NoZeroDivisors M₀]`, which every field
and `ℤ` meet). `.mp` turns `h` into the disjunction, and `rcases … with ha | hb` makes one goal per side.
Placeholders: `{K : Type} [Field K] (a b : K) (P : Prop)`.

| Before | After |
|---|---|
| `h : a * b = 0 ⊢ P` | `ha : a = 0 ⊢ P`, `hb : b = 0 ⊢ P` |

**R3 · `sub_eq_zero`** changes the **context** (used with `rw … at h`, or as `sub_eq_zero.mp h`). The lemma
is `a - b = 0 ↔ a = b` (`[AddGroup G]`: every field, `ℤ`). Placeholders: `(a b : K)`.

| Before | After |
|---|---|
| `h : a - b = 0 ⊢ a = b` | `h : a = b ⊢ a = b` |

**R4 · `eq_neg_of_add_eq_zero_left`** changes the **context** with `have`. The lemma is
`a + b = 0 → a = -b`. Placeholders: `(a b : K)`.

| Before | After |
|---|---|
| `h : a + b = 0 ⊢ a = -b` | `h' : a = -b ⊢ a = -b` |

Then `exact Or.inl …` / `exact Or.inr …` closes `x = 1 ∨ x = -1` (Lean basics).

---

## Part 2 · `prod_rest` (milestone)

Statement: `∏ x ∈ (Finset.univ.erase 0) \ {1, -1}, x = 1`. On the nonzero elements other than `±1`, the
map `x ↦ x⁻¹` pairs each `x` with a *different* element, and each pair multiplies to `1`.

**R5 · `refine Finset.prod_involution (fun a _ => g a) ?_ ?_ ?_ ?_`** changes the **goal list**: one goal
becomes four. The lemma: given `g : (a : ι) → a ∈ s → ι` (it may use the membership proof; `fun a _ => …`
ignores it),

$$\Big(\forall a\in s,\ f a\cdot f(g a)=1\Big)\ \wedge\ \Big(\forall a\in s,\ f a\neq 1\to g a\neq a\Big)\ \wedge\ \Big(\forall a\in s,\ g a\in s\Big)\ \wedge\ \Big(\forall a\in s,\ g(g a)=a\Big)\ \Longrightarrow\ \prod_{x\in s} f x = 1 .$$

So `g` is an involution of `s` (`g ∘ g = id`) with no fixed point except where `f a = 1`. Placeholders:
`{ι M : Type} [CommMonoid M] (s : Finset ι) (f : ι → M) (g : ι → ι)`. In the problem `f` is `fun x => x`,
so `f a` prints as `a`, and the second goal reads `a ≠ 1 → a⁻¹ ≠ a` (see W1).

| Before | After |
|---|---|
| `⊢ ∏ x ∈ s, f x = 1` | `⊢ ∀ a ∈ s, f a * f (g a) = 1`, `⊢ ∀ a ∈ s, f a ≠ 1 → g a ≠ a`, `⊢ ∀ a ∈ s, g a ∈ s`, `⊢ ∀ a ∈ s, g (g a) = a` |

In each goal, `intro a ha` (and in the second, `intro a ha _ heq`: `a⁻¹ ≠ a` is `a⁻¹ = a → False`, so
`heq : a⁻¹ = a` and the goal becomes `False`).

### Unpacking membership (R6–R10, all in one `simp only [...] at ha`)

**R6 · `Finset.mem_sdiff`** changes the **context**: `a ∈ s \ t ↔ a ∈ s ∧ a ∉ t`. Placeholders:
`{α : Type} [DecidableEq α] (s t : Finset α) (a : α)`.

| Before | After |
|---|---|
| `ha : a ∈ s \ t ⊢ P` | `ha : a ∈ s ∧ a ∉ t ⊢ P` |

**R7 · `Finset.mem_erase`** changes the **context**: `a ∈ s.erase b ↔ a ≠ b ∧ a ∈ s`. Placeholders:
`(s : Finset α) (a b : α)`.

| Before | After |
|---|---|
| `ha : a ∈ s.erase b ⊢ P` | `ha : a ≠ b ∧ a ∈ s ⊢ P` |

**R8 · `Finset.mem_univ`, then `and_true`** change the **context**. `Finset.mem_univ a : a ∈ Finset.univ`
is a fact, not an `↔`, so `rw` rejects it; `simp only [Finset.mem_univ]` turns it into `True`. Then
`and_true : (p ∧ True) = p`. Placeholders: `{α : Type} [Fintype α] (a : α) (p : Prop)`.

| Before | After `simp only [Finset.mem_univ] at ha` | After `rw [and_true] at ha` |
|---|---|---|
| `ha : p ∧ a ∈ Finset.univ ⊢ p` | `ha : p ∧ True ⊢ p` | `ha : p ⊢ p` |

**R9 · `Finset.mem_insert`, then `Finset.mem_singleton`** change the **goal** (with `at ha`, the
**context**). `{b, c}` is `insert b {c}`; `a ∈ insert b s ↔ a = b ∨ a ∈ s` and `a ∈ {c} ↔ a = c`.
Placeholders: `(a b c : α) (P : Prop → Prop)`. In the problem it acts on `ha` and, in the third involution
goal, also on the goal (`at ha ⊢`).

| Before | After `rw [Finset.mem_insert]` | After `rw [Finset.mem_singleton]` |
|---|---|---|
| `⊢ P (a ∈ {b, c})` | `⊢ P (a = b ∨ a ∈ {c})` | `⊢ P (a = b ∨ a = c)` |

**R10 · `not_or`** changes the **context**: `¬(p ∨ q) ↔ ¬p ∧ ¬q`. Placeholders: `(p q : Prop)`.

| Before | After |
|---|---|
| `hn : ¬(p ∨ q) ⊢ ¬p ∧ ¬q` | `hn : ¬p ∧ ¬q ⊢ ¬p ∧ ¬q` |

In the problem the whole `simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, Finset.mem_insert,
Finset.mem_singleton, and_true, not_or] at ha` leaves `ha : a ≠ 0 ∧ ¬a = 1 ∧ ¬a = -1`. Its parts are
`ha.1 : a ≠ 0`, `ha.2.1 : ¬a = 1`, `ha.2.2 : ¬a = -1` (W2 shows the same on `ℕ`).

### The four involution goals

**R11 · `mul_inv_cancel₀`** changes the **goal**: `a ≠ 0 → a * a⁻¹ = 1` (`[GroupWithZero G₀]`: every
field). Use `exact mul_inv_cancel₀ ha.1` for the first goal. Placeholders: `{K : Type} [Field K] (a : K)`,
`ha : a ≠ 0`.

| Before | After |
|---|---|
| `⊢ P (a * a⁻¹)` | `⊢ P 1` |

**R12 · `calc`** **closes** `a = c` by a chain of steps `a = b`, `_ = c`, each with its own proof (`_` stands
for the previous right-hand side). In the second goal: `a * a = a * a⁻¹` by `rw [heq]` (rewrites `a⁻¹` to
`a`), then `_ = 1` by R11. Placeholders: `(a b c : K) (hab : a = b) (hbc : b = c)`.

| Before | After |
|---|---|
| `hab : a = b, hbc : b = c ⊢ a = c` | `∅` |

With `haa : a * a = 1`, `rcases sq_eq_one a haa with h | h` (R2's pattern) gives `a = 1` or `a = -1`, which
`ha.2.1` or `ha.2.2` refutes: `exact ha.2.1 h`.

**R13 · `refine fun h => hn ?_`** changes the **goal and the context**. A goal `¬B` is `B → False`; given
`hn : ¬A`, the term `fun h => hn ?_` leaves you to prove `A` from `h : B`. In the third goal, inside
`refine ⟨…, fun h => ha.2.1 ?_, fun h => ha.2.2 ?_⟩`. Placeholders: `(A B : Prop) (hn : ¬A)`.

| Before | After |
|---|---|
| `hn : ¬A ⊢ ¬B` | `h : B ⊢ A` |

**R14 · `inv_ne_zero`** **closes** `a⁻¹ ≠ 0` from `ha : a ≠ 0`: the lemma is `a ≠ 0 → a⁻¹ ≠ 0`.
Placeholders: `(a : K) (ha : a ≠ 0)`.

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ a⁻¹ ≠ 0` | `∅` |

**R15 · `congrArg f h`** changes the **context** with `have`: from `h : a = b` it gives `f a = f b`. Here
`f = (·⁻¹)`, the function `x ↦ x⁻¹`. Placeholders: `(a b : K) (h : a = b)`.

| Before | After |
|---|---|
| `h : a = b ⊢ a⁻¹ = b⁻¹` | `h' : a⁻¹ = b⁻¹ ⊢ a⁻¹ = b⁻¹` |

**R16 · `inv_inv`** changes the **goal**: `a⁻¹⁻¹ = a` (`[InvolutiveInv G]`: every field, every group).
`exact inv_inv a` closes the fourth involution goal. Placeholders: `(a : K)`.

| Before | After |
|---|---|
| `⊢ P a⁻¹⁻¹` | `⊢ P a` |

**R17 · `simpa using h`** **closes** the goal: it simplifies `h` and the goal with `simp`, then closes the
goal with the simplified `h`. Here `simp` uses R16, `inv_one : 1⁻¹ = 1` and `inv_neg : (-a)⁻¹ = -a⁻¹`.
Typical use: `simpa using congrArg (·⁻¹) h` with `h : a⁻¹ = 1` (R15 + R17). Placeholders: `(a : K)`.

| Before | After |
|---|---|
| `h : a⁻¹⁻¹ = 1⁻¹ ⊢ a = 1` | `∅` |

**W1** runs R5, R9, R19 on `∏ x ∈ ({2, 2⁻¹} : Finset ℚ), x = 1`. After R5 the four goals are:

```lean-goal
⊢ ∀ a ∈ {2, 2⁻¹}, a * a⁻¹ = 1
⊢ ∀ a ∈ {2, 2⁻¹}, a ≠ 1 → a⁻¹ ≠ a
⊢ ∀ a ∈ {2, 2⁻¹}, a⁻¹ ∈ {2, 2⁻¹}
⊢ ∀ a ∈ {2, 2⁻¹}, a⁻¹⁻¹ = a
```

---

## Part 3 · `wilson_field`

Statement: `∏ x ∈ (Finset.univ : Finset K).erase 0, x = -1`. Split the nonzero elements into `{1, -1}` and the
rest; the rest multiplies to `1` (`prod_rest`), and `{1, -1}` to `1 * -1 = -1`, unless `1 = -1`
(characteristic 2, as in `ZMod 2`), where `{1, -1} = {1}` multiplies to `1 = -1`.

**R18 · `intro x hx`** on a subset goal changes the **goal and the context**: `s ⊆ t` unfolds to
`∀ ⦃x⦄, x ∈ s → x ∈ t`. Placeholders: `{α : Type} (s t : Finset α)`.

| Before | After |
|---|---|
| `⊢ s ⊆ t` | `x : α, hx : x ∈ s ⊢ x ∈ t` |

**R19 · `rcases hx with rfl | rfl`** changes the **goal list and the context**: one goal per side of
`hx : x = 0 ∨ x = 1`, and the pattern `rfl` substitutes the equation, so `x` disappears. Placeholders:
`(x : ℕ) (P : ℕ → Prop)`. In the problem, after R9 at `hx` (`hx : x = 1 ∨ x = -1`), it leaves
`1 ∈ Finset.univ.erase 0` and `-1 ∈ Finset.univ.erase 0`, which `simp` closes (it knows `one_ne_zero`,
`neg_ne_zero`).

| Before | After |
|---|---|
| `hx : x = 0 ∨ x = 1 ⊢ P x` | `⊢ P 0`, `⊢ P 1` |

**R20 · `rw [← Finset.prod_sdiff hsub]`** changes the **goal**. The lemma is
`s₁ ⊆ s₂ → (∏ x ∈ s₂ \ s₁, f x) * ∏ x ∈ s₁, f x = ∏ x ∈ s₂, f x`; right to left it splits a product over
`s₂` into the part outside `s₁` and the part inside. Placeholders:
`{ι M : Type} [CommMonoid M] [DecidableEq ι] (s₁ s₂ : Finset ι) (f : ι → M) (hsub : s₁ ⊆ s₂)`.

| Before | After |
|---|---|
| `⊢ P (∏ x ∈ s₂, f x)` | `⊢ P ((∏ x ∈ s₂ \ s₁, f x) * ∏ x ∈ s₁, f x)` |

After it, `rw [prod_rest]` replaces the first factor by `1` (the left side of `prod_rest` must match
literally: same set, same order `(… .erase 0) \ {1, -1}`).

**R21 · `one_mul`** changes the **goal**: `1 * a = a` (`[MulOneClass M]`: every monoid). Placeholders:
`{M : Type} [CommMonoid M] (a : M)`.

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

**R22 · `by_cases h : p`** changes the **goal list**: the goal twice, with `h : p` (`case pos`) and with
`h : ¬p` (`case neg`). Placeholders: `(p G : Prop)`. Here `p` is `(1 : K) = -1`; write the type
ascription, or Lean reads `1 = -1` in `ℤ`.

| Before | After |
|---|---|
| `⊢ G` | `h : p ⊢ G`, `h : ¬p ⊢ G` |

**R23 · `Finset.insert_eq_of_mem`** changes the **goal**: `a ∈ s → insert a s = s`; with
`Finset.mem_singleton_self a : a ∈ {a}` it turns `{a, a}` into `{a}`. In `case pos`, `rw [← h1]` turns every
`-1` into `1`, giving `∏ x ∈ {1, 1}, x = 1`; plain `simp` then applies R23 and R24 by itself.
Placeholders: `{α : Type} [DecidableEq α] (a : α) (P : Finset α → Prop)`.

| Before | After |
|---|---|
| `⊢ P {a, a}` | `⊢ P {a}` |

**R24 · `Finset.prod_singleton`** changes the **goal**: `∏ x ∈ {a}, f x = f a`. Placeholders:
`{ι M : Type} [CommMonoid M] (f : ι → M) (a : ι)`.

| Before | After |
|---|---|
| `⊢ P (∏ x ∈ {a}, f x)` | `⊢ P (f a)` |

**R25 · `rw [Finset.prod_pair hab]`** changes the **goal**: `a ≠ b → ∏ x ∈ {a, b}, f x = f a * f b`. In
`case neg`, `hab` is `h1 : ¬(1 : K) = -1`; what is left, `1 * -1 = -1`, closes by `ring`. Placeholders:
`(f : ι → M) (a b : ι) (hab : a ≠ b)`.

| Before | After |
|---|---|
| `⊢ P (∏ x ∈ {a, b}, f x)` | `⊢ P (f a * f b)` |

**W3** splits `∏ x ∈ ({1, 2, 3} : Finset ℕ), x` along `{1, 2}` with R20 and R25:

```lean-goal
⊢ ∏ x ∈ {1, 2, 3}, x = 6
⊢ (∏ x ∈ {1, 2, 3} \ {1, 2}, x) * (1 * 2) = 6
```

---

## Part 4 · `wilson_converse`

Statement: `2 ≤ n → n ∣ (n - 1).factorial + 1 → n.Prime`. Suppose a divisor `m` of `n` is neither `1` nor
`n`. Then `0 < m < n`, so `m ≤ n - 1` and `m ∣ (n - 1).factorial`; with `m ∣ n ∣ (n - 1).factorial + 1` this
gives `m ∣ 1`, so `m = 1`: contradiction.

**R26 · `rw [Nat.prime_def]`** changes the **goal**: `p.Prime ↔ 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p`.
Placeholders: `(p : ℕ)`.

| Before | After |
|---|---|
| `⊢ Nat.Prime p` | `⊢ 2 ≤ p ∧ ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p` |

**R27 · `refine ⟨ha, fun m hm => ?_⟩`** changes the **goal and the context**: it proves the left conjunct
with `ha` and introduces the `∀ m, Q m →` of the right one. Placeholders: `(A : Prop) (Q R : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ ∀ (m : ℕ), Q m → R m` | `m : ℕ, hm : Q m ⊢ R m` |

**R28 · `by_contra hne`** changes the **goal and the context**: the goal becomes `False`, with the negated
goal as `hne`. Placeholders: `(G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hne : ¬G ⊢ False` |

**R29 · `push Not at h`** changes the **context**: it pushes `¬` inward (`¬(p ∨ q)` → `¬p ∧ ¬q`,
`¬a = b` → `a ≠ b`, `¬∀` → `∃ ¬`). Placeholders: `(a b c : ℕ)`. In the problem it turns
`hne : ¬(m = 1 ∨ m = n)` into `hne : m ≠ 1 ∧ m ≠ n`.

| Before | After |
|---|---|
| `h : ¬(a = b ∨ a = c) ⊢ a ≠ b ∧ a ≠ c` | `h : a ≠ b ∧ a ≠ c ⊢ a ≠ b ∧ a ≠ c` |

**R30 · `Nat.pos_of_dvd_of_pos`** **closes** `0 < m`: `m ∣ n → 0 < n → 0 < m`. Placeholders: `(m n : ℕ)`.

| Before | After |
|---|---|
| `hm : m ∣ n, hn : 0 < n ⊢ 0 < m` | `∅` |

**R31 · `omega`** **closes** a goal of linear arithmetic over `ℕ`/`ℤ` (`+`, `-`, `*` by numerals, `<`, `≤`,
`=`, `∧`, `∨`, `¬`) using the hypotheses of that kind. It knows that `ℕ` subtraction truncates at `0`. Use
it for the side conditions `0 < n`, `m ≤ n - 1`. Placeholders: `(n : ℕ) (h : 2 ≤ n)`.

| Before | After |
|---|---|
| `h : 2 ≤ n ⊢ 0 < n ∧ 1 ≤ n - 1` | `∅` |

**R32 · `Nat.le_of_dvd`** **closes** `m ≤ n`: `0 < n → m ∣ n → m ≤ n`. Placeholders: `(m n : ℕ)`.

| Before | After |
|---|---|
| `hn : 0 < n, hm : m ∣ n ⊢ m ≤ n` | `∅` |

**R33 · `lt_of_le_of_ne`** **closes** `a < b`: `a ≤ b → a ≠ b → a < b` (`[PartialOrder α]`: `ℕ`, `ℤ`, `ℝ`).
Placeholders: `(a b : ℕ)`.

| Before | After |
|---|---|
| `hle : a ≤ b, hne : a ≠ b ⊢ a < b` | `∅` |

**R34 · `Nat.dvd_factorial`** **closes** `m ∣ n.factorial`: `0 < m → m ≤ n → m ∣ n.factorial`.
Placeholders: `(m n : ℕ)`. In the problem `n` is `n - 1`; get `m ≤ n - 1` from `m < n` by `omega`.

| Before | After |
|---|---|
| `h0 : 0 < m, hle : m ≤ n ⊢ m ∣ n.factorial` | `∅` |

**R35 · `Dvd.dvd.trans`** **closes** `a ∣ c`: `a ∣ b → b ∣ c → a ∣ c`, written with dot notation
`hab.trans hbc`. Placeholders: `(a b c : ℕ)`.

| Before | After |
|---|---|
| `hab : a ∣ b, hbc : b ∣ c ⊢ a ∣ c` | `∅` |

**R36 · `Nat.dvd_add_right`** changes the **context** with `have`: `a ∣ b → (a ∣ b + c ↔ a ∣ c)`, and `.mp`
goes left to right. Placeholders: `(a b c : ℕ) (hab : a ∣ b)`.

| Before | After |
|---|---|
| `h : a ∣ b + c ⊢ a ∣ c` | `h' : a ∣ c ⊢ a ∣ c` |

**R37 · `Nat.dvd_one`** changes the **context**: `n ∣ 1 ↔ n = 1`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `h : n ∣ 1 ⊢ n = 1` | `h : n = 1 ⊢ n = 1` |

**W4** chains R34, R36, R37 on `4.factorial`:

```lean-goal
⊢ m = 1
```

with, in turn, `h1 : m ∣ Nat.factorial 4` and `h2 : m ∣ 1` added to the context.

---

## Traps

- Characteristic 2: in a field where `1 + 1 = 0` (`ZMod 2`), `1 = -1`, so `{1, -1}` has **one** element
  and `Finset.prod_pair` (which needs `1 ≠ -1`) does not apply. Split with `by_cases h1 : (1 : K) = -1`
  (R22) and handle `{1, 1}` with `simp` (R23, R24).
- `Finset.mem_univ` is not an `↔`: `rw [Finset.mem_univ]` fails. Use it inside `simp only [...]` (R8).
- `rw [prod_rest]` needs the set to appear literally as `Finset.univ.erase 0 \ {1, -1}`. Build `hsub` with
  exactly `({1, -1} : Finset K) ⊆ Finset.univ.erase 0`, so `Finset.prod_sdiff` produces that set.
- `x⁻¹` is defined at `0` (`0⁻¹ = 0`), so `x * x⁻¹ = 1` needs `x ≠ 0` (R11): keep `ha.1 : a ≠ 0`.
- `a⁻¹ ≠ a` is a function type: `intro heq` gives `heq : a⁻¹ = a` and goal `False`.
- `(n - 1)` in `ℕ` truncates: `n - 1 = 0` when `n = 0`. `omega` knows this; `ring` and `linarith` do not.
- `m ∣ n` is typed `\|` (U+2223). The ASCII bar `|` is a syntax error there.
- `t1 ; t2` runs `t2` on the first goal only. After `rcases … with rfl | rfl` use `<;>`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `(x - 1) * (x + 1) = 0` from `x * x = 1` | `have h' : … := by linear_combination h` | R1 |
| a product is zero → one factor is | `rcases mul_eq_zero.mp h' with h \| h` | R2 |
| `x - 1 = 0 → x = 1` / `x + 1 = 0 → x = -1` | `sub_eq_zero.mp h` / `eq_neg_of_add_eq_zero_left h` | R3, R4 |
| `∏ x ∈ s, f x = 1` by pairing | `refine Finset.prod_involution (fun x _ => x⁻¹) ?_ ?_ ?_ ?_` | R5 |
| unpack `a ∈ (univ.erase 0) \ {1, -1}` | `simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, and_true, not_or] at ha` | R6–R10 |
| `a * a⁻¹ = 1` | `mul_inv_cancel₀ ha.1` | R11 |
| `a * a = 1` from `a⁻¹ = a` | `calc a * a = a * a⁻¹ := by rw [heq]` `_ = 1 := …` | R12 |
| prove `¬B` from `hn : ¬A` | `fun h => hn ?_` | R13 |
| `a⁻¹ ≠ 0` | `inv_ne_zero ha.1` | R14 |
| `a = 1` from `a⁻¹ = 1` | `simpa using congrArg (·⁻¹) h` | R15, R17 |
| `a⁻¹⁻¹ = a` | `inv_inv a` | R16 |
| prove `s ⊆ t` | `intro x hx`, then R9 at `hx`, `rcases hx with rfl \| rfl <;> simp` | R18, R19 |
| split a product along `s₁ ⊆ s₂` | `rw [← Finset.prod_sdiff hsub]` | R20 |
| `1 * a → a` | `rw [one_mul]` | R21 |
| case on `1 = -1` | `by_cases h1 : (1 : K) = -1` | R22 |
| `∏ x ∈ {a, a}, f x` | `simp` | R23, R24 |
| `∏ x ∈ {a, b}, f x` with `a ≠ b` | `rw [Finset.prod_pair hab]` | R25 |
| unfold `n.Prime` | `rw [Nat.prime_def]` | R26 |
| prove `2 ≤ n ∧ ∀ m, …` | `refine ⟨h2, fun m hm => ?_⟩` | R27 |
| argue by contradiction | `by_contra hne; push Not at hne` | R28, R29 |
| `0 < m`, `m ≤ n`, `m < n` from `m ∣ n` | `Nat.pos_of_dvd_of_pos`, `Nat.le_of_dvd`, `lt_of_le_of_ne` | R30, R32, R33 |
| linear side goals in `ℕ` | `omega` | R31 |
| `m ∣ k.factorial` | `Nat.dvd_factorial hm0 hle` | R34 |
| `m ∣ n → n ∣ c → m ∣ c` | `hm.trans h` | R35 |
| `m ∣ b + c`, `m ∣ b` → `m ∣ c` | `(Nat.dvd_add_right hb).mp h` | R36 |
| `m ∣ 1 → m = 1` | `Nat.dvd_one.mp` | R37 |
| see the state | infoview | |
