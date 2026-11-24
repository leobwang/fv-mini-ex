# H035 · Euler's theorem: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `apply`, `refine`, `rw … at h`, `simp`,
`have`, `obtain`/`rcases` patterns, `∧`/`∃`/`↔` and `.1`, `.2`, `.mp`, `.mpr`, `calc`. **New here:** Mathlib's
finite sets (`Finset`, `range`, `filter`, `image`, `#s`), big products `∏ x ∈ s, f x`, `Nat.gcd` and
`Nat.Coprime`, Euler's totient `Nat.totient`, congruences `a ≡ b [MOD n]` (`Nat.ModEq`), sets `Set α` and
injectivity on a set `Set.InjOn`, and the tactics `set` and `conv_lhs`.

The problem in one paragraph. For `n > 0` let `R = {k < n | gcd(n, k) = 1}`, the reduced residues mod `n`;
by definition `φ(n) = #R` (the totient, `Nat.totient n`). For `a` coprime to `n`, the map
`g(k) = a·k mod n` sends `R` into `R` (MILESTONE 1), is injective on `R` (MILESTONE 2), hence is onto `R`
(MILESTONE 3: an injective self-map of a finite set). So the product `P = ∏_{k∈R} k` equals
`∏_{k∈R} g(k)`, and reducing mod `n`, `P ≡ ∏_{k∈R} a·k = a^{φ(n)}·P`. Since `P` is coprime to `n` it
cancels, leaving `a^{φ(n)} ≡ 1 (mod n)`. The case `n = 0` is separate: `φ(0) = 0` and `[MOD 0]` is plain
equality.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`exact`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℕ → Prop` and similar). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal. `G : Prop` is a goal the step leaves alone (the step works on a
  hypothesis). A hypothesis `h` or `k` in an example is there only to finish it.
- Placeholders are written as Lean binders. `{α : Type}` is any type (in the exercise, always `ℕ`).
  `[DecidablePred p]` says membership `p x` can be decided by a program, which `filter p` needs; true of
  `Nat.Coprime n`. `[DecidableEq β]` says `=` on `β` is decidable, which `image` needs (to drop duplicates);
  true of `ℕ`. Lean shows such an argument as `inst✝ : …` in the context.
- `∅` means the goal is closed.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Finset ℕ` | a finite set of natural numbers (a list with no duplicates, order forgotten) |
| `range n` | `Finset.range n = {0, 1, …, n - 1}` (the file has `open Finset`, so `range` is the finset one) |
| `filter p s`, `s.filter p` | the elements `x ∈ s` with `p x`. Lean prints `{x ∈ s \| p x}` when `p` is written as a `fun` (R31) |
| `filter n.Coprime (range n)` | the exercise's `R`: the `k < n` with `gcd n k = 1` |
| `image f s`, `s.image f` | `{f x \| x ∈ s}` as a finset |
| `s ⊆ t` (finsets) | every element of `s` is in `t`: `∀ ⦃x⦄, x ∈ s → x ∈ t`, so `intro x hx` works (R18). `⦃x⦄` is a binder Lean fills in by itself once the argument after it is given; `intro` still names it |
| `#s` | `Finset.card s`, the number of elements of `s` |
| `∏ x ∈ s, f x` | `Finset.prod s f`, the product of `f x` over `x ∈ s`; `∏ _i ∈ s, b` has a constant factor |
| `m.gcd n` | `Nat.gcd m n`; `Nat.gcd 0 n = n` |
| `m.Coprime n` | `Nat.Coprime m n`, **defined** as `m.gcd n = 1` (R4). `ha : a.Coprime n` is the problem's hypothesis |
| `n.totient`, `Nat.totient n` | Euler's `φ(n)`, by definition `#(filter n.Coprime (range n))` (R31) |
| `a ≡ b [MOD n]` | `Nat.ModEq n a b`, **defined** as `a % n = b % n` (R12, R14). `[MOD 0]` is `a = b` |
| `↑s` (with `s : Finset α`) | `s` seen as a `Set α` (a predicate `α → Prop`), so set notions apply |
| `{x \| q x}` | the set of all `x` with `q x`; `a ∈ {x \| q x}` is `q a` (R11) |
| `Set.InjOn f ↑s` | `f` is injective on `s`: `∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y` (R9) |
| `(fun k => a * k % n) k` | a `fun` applied but not yet reduced: it is `a * k % n` (`simp only at h` reduces it) |
| `R : Finset ℕ := …` | a local definition made by `set` (R25): `R` is a name for the expression after `:=` |
| `hn : n > 0` | the same as `0 < n` (`>` is notation for the flipped `<`) |
| `case h`, `case h₂` | the two goals of `apply Finset.eq_of_subset_of_card_le` (R17) |
| `case inl`, `case inr` | the left and right side of an `∨` after `rcases` (R22) |

---

## Part 1 · `mul_mod_mem` (MILESTONE 1)

Statement: if `0 < n`, `a` is coprime to `n`, and `k ∈ R`, then `a * k % n ∈ R`. Membership in
`filter … (range n)` is a pair (R1, R2): `a * k % n < n` (R3) and `n.Coprime (a * k % n)`. For the second,
unfold `Coprime` (R4), then `gcd n (a·k mod n) = gcd (a·k mod n) n = gcd n (a·k)` (R5, then R6 right to
left), and `n` is coprime to a product of two numbers it is coprime to (R7, R8).

**R1 · `rw [Finset.mem_filter] at h ⊢`** changes the **context and the goal**. The lemma is
`a ∈ s.filter p ↔ a ∈ s ∧ p a`; `rw` can rewrite with an `↔` between propositions, and `at h ⊢` rewrites
`h` and the goal in one step. Term form: `Finset.mem_filter.mp h : a ∈ s ∧ p a`. Placeholders:
`{α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] (a b : α)`.

| Before | After |
|---|---|
| `h : a ∈ filter p s ⊢ b ∈ filter p s` | `h : a ∈ s ∧ p a ⊢ b ∈ s ∧ p b` |

**R2 · `rw [Finset.mem_range]`** changes the **goal** (or a hypothesis, with `at`). The lemma is
`m ∈ range n ↔ m < n`. Placeholders: `(m n : ℕ)`. Put it in the same `rw [...]` as R1.

| Before | After |
|---|---|
| `⊢ P (m ∈ range n)` | `⊢ P (m < n)` |

**R3 · `refine ⟨Nat.mod_lt _ hn, ?_⟩`** changes the **goal list**: the first half of an `∧` is proved on
the spot, the second stays. The lemma is `Nat.mod_lt (m : ℕ) {n : ℕ} : 0 < n → m % n < n` (`m` explicit, so write `_` for it). Placeholders:
`(m n : ℕ) (hn : 0 < n) (Q : Prop)`.

| Before | After |
|---|---|
| `hn : 0 < n ⊢ m % n < n ∧ Q` | `⊢ Q` |

**R4 · `rw [Nat.Coprime]`** changes the **goal**: it unfolds the definition `Nat.Coprime m n := m.gcd n = 1`.
Because it is a definition, a proof of `m.Coprime n` also proves `m.gcd n = 1` and back, with no rewrite
(R8, R13 use this). Placeholders: `(m n : ℕ)`.

| Before | After |
|---|---|
| `⊢ m.Coprime n` | `⊢ m.gcd n = 1` |

**R5 · `rw [Nat.gcd_comm]`** changes the **goal**. The lemma is `gcd m n = gcd n m`; bare, it rewrites the
first `gcd` it meets. Placeholders: `(m n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (m.gcd n)` | `⊢ P (n.gcd m)` |

**R6 · `rw [← Nat.gcd_rec]`** changes the **goal**. The lemma is `Nat.gcd_rec m n : gcd m n = gcd (n % m) m`
(one step of Euclid's algorithm). Right to left it turns `gcd (n % m) m` back into `gcd m n`, removing a `%`.
Placeholders: `(m n : ℕ)`. Euclid's step only fits after R5 has put the `%`-term first.

| Before | After |
|---|---|
| `⊢ P ((n % m).gcd m)` | `⊢ P (m.gcd n)` |

**R7 · `h.symm`** changes the **context** (with `have`). `Nat.Coprime.symm : m.Coprime n → n.Coprime m`;
dot notation `h.symm` finds it from `h`'s type. Placeholders: `(m n : ℕ) (h : m.Coprime n)`.

| Before | After |
|---|---|
| `h : m.Coprime n ⊢ G` | `h' : n.Coprime m ⊢ G` |

**R8 · `exact Nat.Coprime.mul_right hm hn`** **closes** the goal. The lemma is
`k.Coprime m → k.Coprime n → k.Coprime (m * n)`. The goal here is the unfolded `k.gcd (m * n) = 1`, which is
the same proposition (R4). Placeholders: `(k m n : ℕ) (hm : k.Coprime m) (hn : k.Coprime n)`.

| Before | After |
|---|---|
| `hm : k.Coprime m, hn : k.Coprime n ⊢ k.gcd (m * n) = 1` | ∅ |

In the problem, after R1–R6 the goal is `n.gcd (a * k) = 1`; the two facts are `ha.symm` (R7) and the second
half of `hk`.

**W1, W2** (guide) run pieces of this chain on other objects: W1 on the shift `k ↦ (k + 1) % n`, W2 on
`m.Coprime (c % m)` (R4–R7, no product) and on a product of three factors `b * c * d` (R8 twice).

---

## Part 2 · `mul_mod_inj` (MILESTONE 2)

Statement: `Set.InjOn (fun k => a * k % n) ↑R`. Introduce two elements of `R` and the equation between
their images (R9), turn the membership hypotheses into `k < n ∧ …` (R10, R11, R2; one `simp only [...] at hk
hj` does all three). The image equation `a * k % n = a * j % n` **is** `a * k ≡ a * j [MOD n]` (R12); cancel
`a` (R13 with `ha.symm`), unfold the result (R14), and remove `% n` on both sides because `k, j < n` (R15,
R16).

**R9 · `intro x hx y hy hxy`** changes the **goal and the context**: `Set.InjOn f ↑s` is defined as
`∀ ⦃x⦄, x ∈ ↑s → ∀ ⦃y⦄, y ∈ ↑s → f x = f y → x = y`, so `intro` sees five binders.
Placeholders: `{α β : Type} (f : α → β) (s : Finset α)`.

| Before | After |
|---|---|
| `⊢ Set.InjOn f ↑s` | `hx : x ∈ ↑s, hy : y ∈ ↑s, hxy : f x = f y ⊢ x = y` |

In the problem `f` is a `fun`, so `hxy` reads `(fun k => a * k % n) k = (fun k => a * k % n) j`: unreduced, but
it is `a * k % n = a * j % n`.

**R10 · `rw [Finset.coe_filter]`** changes the **goal**, or with `at hx` the **context** (the problem's use).
The lemma is `↑(s.filter p) = {x | x ∈ s ∧ p x}`: the set of a filtered finset is a set-builder set.
Placeholders: `{α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] (x : α)`. Before, then after:

```lean-goal
⊢ P (x ∈ ↑(filter p s))
⊢ P (x ∈ {x | x ∈ s ∧ p x})
```

**R11 · `rw [Set.mem_setOf_eq]`** changes the **goal**, or with `at hx` the **context**. The lemma is
`(a ∈ {x | q x}) = q a`. Placeholders: `{α : Type} (q : α → Prop) (a : α)`. Before, then after:

```lean-goal
⊢ P (a ∈ {x | q x})
⊢ P (q a)
```

After R10, R11, R2 (in the problem: `simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk
hj`), `hk` reads `k < n ∧ n.Coprime k`.

**R12 · `have h' : a ≡ b [MOD n] := h`** changes the **context**. `Nat.ModEq n a b` is *defined* as
`a % n = b % n`, so a proof of the `%`-equation proves the congruence as it stands; only the label changes.
Inside a term write the ascription `(h : a ≡ b [MOD n])`, e.g. as an argument of R13. Placeholders:
`(a b n : ℕ)`.

| Before | After |
|---|---|
| `h : a % n = b % n ⊢ G` | `h' : a ≡ b [MOD n] ⊢ G` |

**R13 · `have h' := Nat.ModEq.cancel_left_of_coprime hc h`** changes the **context**. The lemma is
`(hmc : m.gcd c = 1) (h : c * a ≡ c * b [MOD m]) : a ≡ b [MOD m]`: a factor coprime to the modulus cancels.
The modulus comes first in `hmc`, so in the problem pass `ha.symm : n.Coprime a` (R7), which is
`n.gcd a = 1` (R4). Placeholders: `(m c a b : ℕ) (hc : m.Coprime c)`.

| Before | After |
|---|---|
| `hc : m.Coprime c, h : c * a ≡ c * b [MOD m] ⊢ G` | `h' : a ≡ b [MOD m] ⊢ G` |

**R14 · `unfold Nat.ModEq at h`** changes the **context**: the congruence is shown as its definition, so `rw`
can see the `%`. Placeholders: `(a b n : ℕ)`.

| Before | After |
|---|---|
| `h : a ≡ b [MOD n] ⊢ G` | `h : a % n = b % n ⊢ G` |

**R15 · `rw [Nat.mod_eq_of_lt hab] at h`** changes the **context** (or the goal, without `at`). The lemma is
`a < b → a % b = a`. Placeholders: `(a b : ℕ) (hab : a < b)`; in the problem `hab` is `hk.1` or `hj.1`.

| Before | After |
|---|---|
| `h : P (a % b) ⊢ False` | `h : P a ⊢ False` |

**R16 · `rwa [e] at h`** **closes** the goal: `rw [e] at h` and then `assumption` (some hypothesis now has
exactly the goal's type). Placeholders: `(a b x : ℕ) (e : a = b) (h : x = a)`.

| Before | After |
|---|---|
| `e : a = b, h : x = a ⊢ x = b` | ∅ |

---

## Part 3 · `image_mul_mod` (MILESTONE 3)

Statement: `R.image (fun k => a * k % n) = R`. Two finsets are equal when one is inside the other and is at
least as big (R17). Inclusion: take `x` in the image (R18), unpack it as `x = a * k % n` with `k ∈ R` (R19,
R20), and MILESTONE 1 finishes. Size: `#(image f R) = #R` because `f` is injective on `R` (R21 with
MILESTONE 2); `rw` then closes `#R ≤ #R` by itself.

**R17 · `apply Finset.eq_of_subset_of_card_le`** changes the **goal list**. The lemma is
`s ⊆ t → #t ≤ #s → s = t`. Placeholders: `{α : Type} (s t : Finset α)`. In the problem `s` is the image and
`t` is `R`, so the second goal is `#R ≤ #(image … R)`.

| Before | After |
|---|---|
| `⊢ s = t` | `⊢ s ⊆ t`, `⊢ #t ≤ #s` |

**R18 · `intro x hx`** changes the **goal and the context**: `s ⊆ t` on finsets is defined as
`∀ ⦃x⦄, x ∈ s → x ∈ t`. Placeholders: `{α : Type} (s t : Finset α)`.

| Before | After |
|---|---|
| `⊢ s ⊆ t` | `hx : x ∈ s ⊢ x ∈ t` |

**R19 · `rw [Finset.mem_image]`** changes the **goal**, or with `at hb` the **context** (the problem's
use; term form `Finset.mem_image.mp hb`). The lemma is `b ∈ s.image f ↔ ∃ a ∈ s, f a = b`. Placeholders:
`{α β : Type} [DecidableEq β] (s : Finset α) (f : α → β) (b : β)`.

| Before | After |
|---|---|
| `⊢ P (b ∈ image f s)` | `⊢ P (∃ a ∈ s, f a = b)` |

**R20 · `obtain ⟨a, ha, rfl⟩ := h`** changes the **context and the goal**: it unpacks the `∃` and the `∧`,
and the pattern `rfl` uses the equation `f a = b` to replace `b` by `f a` everywhere (`b` and `h`
disappear). Combine with R19: `obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb`. Placeholders:
`{α β : Type} (s : Finset α) (f : α → β) (b : β) (P : β → Prop)`. Before, the context has
`h : ∃ a ∈ s, f a = b`; after, it has `a : α` and:

| Before | After |
|---|---|
| `⊢ P b` | `ha : a ∈ s ⊢ P (f a)` |

**R21 · `rw [Finset.card_image_of_injOn hf]`** changes the **goal**. The lemma is
`Set.InjOn f ↑s → #(s.image f) = #s`: an injective map does not merge elements. After a `rw`, Lean tries
`rfl`, so a goal that becomes `#s ≤ #s` is closed. Placeholders:
`{α β : Type} [DecidableEq β] (s : Finset α) (f : α → β) (hf : Set.InjOn f ↑s)`.

| Before | After |
|---|---|
| `⊢ P #(image f s)` | `⊢ P #s` |

**W3** (guide) runs R17–R21 on `(range n).image (fun k => (k + 1) % n) = range n`:

```lean-goal
⊢ image (fun k => (k + 1) % n) (range n) = range n
⊢ image (fun k => (k + 1) % n) (range n) ⊆ range n
⊢ #(range n) ≤ #(image (fun k => (k + 1) % n) (range n))
```

---

## Part 4 · `euler`

Statement: `Nat.Coprime a n → a ^ Nat.totient n ≡ 1 [MOD n]`. Split off `n = 0` (R22; then `simp` with R23,
R24). For `n > 0`: get `himg` from MILESTONE 3, **then** name `R` (R25). Reindex the product (R26, R27 with
MILESTONE 2) to get `hprod`. Show the product is coprime to `n` (R28 with R1). Prove
`P * a ^ φ n ≡ P * 1 [MOD n]` by a `calc` on `% n` (R34) whose steps use R29, R30, R31, R32, R33 and
`hprod`; cancel `P` (R13).

**R22 · `rcases Nat.eq_zero_or_pos n with rfl | hn`** changes the **goal list**. The lemma is
`Nat.eq_zero_or_pos (n : ℕ) : n = 0 ∨ 0 < n`. The pattern `rfl | hn` makes one goal per side; on the left
the equation `n = 0` is used to replace `n` by `0`. Placeholders: `(P : ℕ → Prop) (n : ℕ)`.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `hn : n > 0 ⊢ P n` |

**R23 · `Nat.totient_zero`, `pow_zero`** change the **goal**: `Nat.totient 0 = 0` and `a ^ 0 = 1`. Plain
`simp` uses both by itself. Placeholders: `(a : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (a ^ Nat.totient 0)` | `⊢ P 1` |

**R24 · `Nat.ModEq.refl`** **closes** `a ≡ a [MOD n]` (`Nat.ModEq.refl a`); `simp` also knows it, so after R23
`simp` finishes the `n = 0` case. Placeholders: `(a n : ℕ)`.

| Before | After |
|---|---|
| `⊢ a ≡ a [MOD n]` | ∅ |

**R25 · `set x := e with hx`** changes the **context and the goal**: every occurrence of `e`, in the goal and
in every hypothesis already present, is replaced by the new local definition `x`, and `hx : x = e` is added.
Hypotheses created *later* mention `e`, not `x` (Traps). Placeholders: `(n : ℕ) (P : Finset ℕ → Prop)`, with
`e := range (n + 1)`.

| Before | After |
|---|---|
| `h : P (range (n + 1)) ⊢ P (range (n + 1))` | `s : Finset ℕ := range (n + 1), h : P s, hs : s = range (n + 1) ⊢ P s` |

**R26 · `conv_lhs => rw [← h]`** changes the **goal**: it rewrites inside the left-hand side of an equation
only. A plain `rw [← h]` would rewrite both sides. In the problem, `← himg` turns the `R` of the left side
into `image (fun k => a * k % n) R`, while the right side keeps `R`. Placeholders:
`{α β : Type} (f : α → β) (x y : α) (h : y = x)`.

| Before | After |
|---|---|
| `⊢ f x = f x` | `⊢ f y = f x` |

**R27 · `rw [Finset.prod_image hg]`** changes the **goal**. The lemma is
`Set.InjOn g ↑s → ∏ x ∈ s.image g, f x = ∏ x ∈ s, f (g x)`: a product over an injective image is a product
over the source. Placeholders: `{α β : Type} [DecidableEq α] (s : Finset β) (g : β → α) (f : α → ℕ)
(hg : Set.InjOn g ↑s)`. In the problem `f` is the identity `fun k => k`, so the result is
`∏ x ∈ R, a * x % n`, and `rw`'s closing `rfl` finishes `hprod`.

| Before | After |
|---|---|
| `⊢ P (∏ x ∈ image g s, f x)` | `⊢ P (∏ x ∈ s, f (g x))` |

**W4** (guide) is the same reindexing for the shift on `range n`:

```lean-goal
⊢ ∏ k ∈ range n, (k + 1) = ∏ k ∈ range n, ((k + 1) % n + 1)
⊢ ∏ k ∈ image (fun k => (k + 1) % n) (range n), (k + 1) = ∏ k ∈ range n, ((k + 1) % n + 1)
```

**R28 · `apply Nat.coprime_prod_right_iff.mpr`** changes the **goal**. The lemma is
`x.Coprime (∏ i ∈ t, s i) ↔ ∀ i ∈ t, x.Coprime (s i)`. Term form:
`Nat.coprime_prod_right_iff.mpr fun i hi => …`; for `i ∈ R` the fact is the second half of
`Finset.mem_filter.mp hi` (R1). Placeholders: `{ι : Type} (x : ℕ) (t : Finset ι) (s : ι → ℕ)`.

| Before | After |
|---|---|
| `⊢ x.Coprime (∏ i ∈ t, s i)` | `⊢ ∀ i ∈ t, x.Coprime (s i)` |

**R29 · `rw [Finset.prod_mul_distrib]`** changes the **goal**. The lemma is
`∏ i ∈ s, f i * g i = (∏ i ∈ s, f i) * ∏ i ∈ s, g i`. Placeholders: `{ι : Type} (s : Finset ι)
(f g : ι → ℕ)`. Lean renames the bound variable to `x`; that is only a name.

| Before | After |
|---|---|
| `⊢ P (∏ i ∈ s, f i * g i)` | `⊢ P ((∏ x ∈ s, f x) * ∏ x ∈ s, g x)` |

**R30 · `rw [Finset.prod_const]`** changes the **goal**. The lemma is `∏ _x ∈ s, b = b ^ #s`. Placeholders:
`{ι : Type} (s : Finset ι) (b : ℕ)`. In the problem it leaves `a ^ #R`, not `a ^ n.totient` (R31 bridges).

| Before | After |
|---|---|
| `⊢ P (∏ _i ∈ s, b)` | `⊢ P (b ^ #s)` |

**R31 · `rw [Nat.totient_eq_card_coprime]`** changes the **goal**. The lemma is
`n.totient = #{a ∈ range n | n.Coprime a}`, i.e. the definition of `φ`. `{a ∈ range n | n.Coprime a}` and
`filter n.Coprime (range n)` are the same finset, and `R` is a name for it, so after this rewrite `rw`'s
closing `rfl` sees `a ^ #R` and `a ^ #{…}` as equal. Placeholders: `(n : ℕ)`.

```lean-goal
⊢ P n.totient
⊢ P #({a ∈ range n | n.Coprime a})
```

**R32 · `rw [mul_one]`, `rw [mul_comm]`** change the **goal**: `a * 1 = a` and `a * b = b * a`. A bare
`mul_comm` rewrites the first product `rw` finds (here the outermost); `mul_comm a b` names one.
Placeholders: `(a b : ℕ)`.

| Before | After `rw [mul_one]` | After `rw [mul_comm]` |
|---|---|---|
| `⊢ P (a * b * 1)` | `⊢ P (a * b)` | `⊢ P (b * a)` |

**R33 · `Finset.prod_nat_mod`** **closes** the goal, used as a term `Finset.prod_nat_mod s n f`. The lemma
is `(∏ i ∈ s, f i) % n = (∏ i ∈ s, f i % n) % n`: reduce each factor mod `n` before multiplying. With `_ _ _`
Lean finds `s n f` from the goal. Placeholders: `{ι : Type} (s : Finset ι) (n : ℕ) (f : ι → ℕ)`.

| Before | After |
|---|---|
| `⊢ (∏ i ∈ s, f i) % n = (∏ i ∈ s, f i % n) % n` | ∅ |

**R34 · `calc` on `% n`** **closes** a congruence goal. Since `a ≡ b [MOD n]` *is* `a % n = b % n` (R12), a
`calc` chain of equations that starts at `a % n` and ends at `b % n` proves it. Each step is
`_ = e := proof`, the `_` standing for the previous right-hand side. Placeholders: `(a b c n : ℕ)
(h1 : a % n = c % n) (h2 : c % n = b % n)`.

| Before | After |
|---|---|
| `⊢ a ≡ b [MOD n]` | ∅ |

**W5** (guide) runs R29, R30, R33, R34 on `2 ^ #s * ∏ k ∈ s, k ≡ ∏ k ∈ s, 2 * k % n [MOD n]`: first
`hpow : ∏ k ∈ s, 2 * k = 2 ^ #s * ∏ k ∈ s, k` by R29, R30, then a two-step `calc`. In the problem the same
`calc` has one more step, `… = (∏ k ∈ R, k) * 1 % n`, by `rw [← hprod, mul_one]`, and the first step needs
`mul_comm` (R32) because the spec order is `P * a ^ φ n`, not `a ^ φ n * P`.

---

## Traps

- **Banned** (the checker enforces it): `ZMod`, `Units`, `ArithmeticFunction` (Carmichael's `λ(n) ∣ φ(n)`),
  `Nat.ModEq.pow_totient` and its relatives, `pow_card_eq_one`, `orderOf_dvd_card`, and the search tactics
  `exact?`, `apply?`, `rw?`, `try?`, `hint`. The point is the residue-permutation argument in plain `ℕ`.
- Get `himg := image_mul_mod n a hn ha` **before** `set R := …`. `set` replaces the expression in hypotheses
  that exist when it runs; one stated afterwards still mentions `filter n.Coprime (range n)`, and
  `conv_lhs => rw [← himg]` fails with "did not find an occurrence of the pattern" because the goal shows `R`.
- The cancellation lemma wants the modulus first: `n.gcd a = 1`, i.e. `ha.symm`, not `ha` (R7, R13).
- `prod_const` gives `a ^ #R`, not `a ^ n.totient`: rewrite `Nat.totient_eq_card_coprime` (R31) in the same
  `rw`.
- `hkj` from `intro` is `(fun k => a * k % n) k = (fun k => a * k % n) j`, unreduced. Ascribe it,
  `(hkj : a * k ≡ a * j [MOD n])`, or reduce it with `simp only at hkj` before `rw`.
- `rw` needs the left side of the lemma literally in the goal: `Nat.gcd_rec` matches only `gcd (x % m) m`,
  so swap with `Nat.gcd_comm` first (R5, R6).
- `rw [mul_comm]` with no arguments rewrites the first product it finds, which may not be the one you want.
- `n = 0` is a real case: `range 0 = ∅`, `φ 0 = 0`, and `a ≡ b [MOD 0]` is `a = b`. Handle it first (R22);
  everything else needs `hn : 0 < n` (for `Nat.mod_lt`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unpack `x ∈ filter p (range n)` | `rw [Finset.mem_filter, Finset.mem_range] at h` (R1: also the goal) | R1, R2 |
| `m % n < n` | `Nat.mod_lt _ hn` | R3 |
| `Coprime` → `gcd … = 1` | `rw [Nat.Coprime]` (or use it as is: same proposition) | R4 |
| drop a `%` inside `gcd` | `rw [Nat.gcd_comm, ← Nat.gcd_rec]` | R5, R6 |
| swap a coprimality | `h.symm` | R7 |
| coprime to a product | `Nat.Coprime.mul_right h₁ h₂`; many factors: `Nat.coprime_prod_right_iff.mpr` | R8, R28 |
| prove `Set.InjOn f ↑s` | `intro x hx y hy hxy` | R9 |
| unpack `x ∈ ↑(filter p s)` | `simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx` | R10, R11, R2 |
| `%`-equation ↔ congruence | `(h : a ≡ b [MOD n])` / `unfold Nat.ModEq at h` | R12, R14 |
| cancel a coprime factor | `Nat.ModEq.cancel_left_of_coprime hmc h` (`hmc : n.gcd c = 1`) | R13 |
| `k % n = k` for `k < n` | `rw [Nat.mod_eq_of_lt hk]` | R15 |
| rewrite then close by a hypothesis | `rwa [e] at h` | R16 |
| finset equality by size | `apply Finset.eq_of_subset_of_card_le` | R17 |
| prove `s ⊆ t` | `intro x hx` | R18 |
| unpack `x ∈ image f s` | `obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx` | R19, R20 |
| `#(image f s) = #s` | `rw [Finset.card_image_of_injOn hf]` | R21 |
| split `n = 0` | `rcases Nat.eq_zero_or_pos n with rfl \| hn` | R22 |
| `n = 0` case | `simp` | R23, R24 |
| name a subterm | `set R := e with hR` | R25 |
| rewrite the left side only | `conv_lhs => rw [← h]` | R26 |
| product over an image | `rw [Finset.prod_image hg]` | R27 |
| split a product / constant product | `rw [Finset.prod_mul_distrib, Finset.prod_const]` | R29, R30 |
| `φ n` as a card | `rw [Nat.totient_eq_card_coprime]` | R31 |
| reorder / drop `* 1` | `rw [mul_comm]`, `rw [mul_one]` | R32 |
| reduce factors mod `n` | `Finset.prod_nat_mod _ _ _` | R33 |
| prove `a ≡ b [MOD n]` by equations | `calc a % n = … := … _ = b % n := …` | R34 |
| see the state | infoview | |
