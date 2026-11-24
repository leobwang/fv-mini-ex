# M163 · Einstein solids in thermal contact: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's three notions of size
(`Nat.card`, `Fintype.card`, `Finset.card`), equivalences `α ≃ β`, multisets `Sym α n`, Finsets and their
coercions to types and sets, `Finset.Nat.antidiagonalTuple`, splitting `Fin (a + b)` with `Fin.castAdd`,
`Fin.natAdd`, `Fin.append`, bijective and fiberwise counting.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℕ → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Fintype α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. States
  that contain `|` (Finset filters) are in `lean-goal` blocks, because `|` would break a table. A
  hypothesis whose text contains a comma (`∀ (x : α), …`, `∑ i, …`) is written next to the cell.

## Reading the goals

| You see | It means |
|---|---|
| `Fin n → ℕ` | a microstate: site `i : Fin n = {0, …, n-1}` holds `f i` quanta |
| `∑ i, f i` | the sum of `f i` over all `i : Fin n` (the total number of quanta) |
| `{ f // ∑ i, f i = q }` | the *subtype*: elements are pairs `⟨f, proof that ∑ i, f i = q⟩`. Lean prints it without the type of `f` |
| `Nat.card α` | the number of elements of the type `α`, as a natural number (`0` if `α` is infinite) |
| `Fintype.card α` | the number of elements of `α`, for a type with a `[Fintype α]` instance (a computed finite list of all elements) |
| `Finset α`, `s.card` | a finite set of elements of `α`, and its number of elements |
| `Finset.range n` | the Finset `{0, 1, …, n - 1}` of naturals |
| `∑ k ∈ s, g k` | the sum of `g k` over `k` in the Finset `s` |
| `↥s` | the Finset `s` used as a type: `{ x // x ∈ s }` |
| `↑s` | the Finset `s` seen as a `Set α` (needed by `Set.MapsTo` etc.); `x ∈ ↑s` means `x ∈ s` |
| `Set α`, `{x \| p x}` | a set of elements of `α` (not necessarily finite), and the set of all `x` with `p x` (R12) |
| `{x ∈ s \| p x}` | `Finset.filter p s`: the elements of `s` that satisfy `p` |
| `s ×ˢ t` | the product: all pairs `(x, y)` with `x ∈ s`, `y ∈ t` (for Finsets and for Sets) |
| `p.1`, `p.2` | the first and second component of a pair `p : α × β` |
| `Finset.Nat.antidiagonalTuple k n` | the Finset of all `x : Fin k → ℕ` with `∑ i, x i = n` (R7) |
| `Sym α n` | multisets of size `n` with elements in `α` (unordered, repetition allowed) |
| `n.choose k` | the binomial coefficient `C(n, k)` |
| `α ≃ β` | an equivalence: a bijection `α → β` packaged with its inverse |
| `Fin.castAdd b i` | `i : Fin a` seen as an element of `Fin (a + b)` (the same number) |
| `Fin.natAdd a j` | `a + j : Fin (a + b)` for `j : Fin b` (the last `b` indices) |
| `Fin.append u v` | the tuple `Fin (m + n) → α` that is `u` on the first `m` indices and `v` on the last `n` |
| `Set.MapsTo f A B` | `∀ x, x ∈ A → f x ∈ B` |
| `Set.LeftInvOn j i A` | `∀ x, x ∈ A → j (i x) = x` |
| `Set.RightInvOn j i B` | `∀ y, y ∈ B → i (j y) = y` |
| `∀ ⦃x⦄, …` | a *strict-implicit* `∀`: `x` is filled in only once a later explicit argument is given; `intro x` works as for `∀ x` |
| `∀ x ∈ s, P x` | `∀ x, x ∈ s → P x` (R24) |
| `(fun x => e) x` | a function applied to `x`, not yet simplified; it means `e` with `x` substituted. `simp only` performs the substitution |
| `q - k` on `ℕ` | truncated subtraction: `0` when `k > q` (R17) |
| `inst✝ : Fintype α` | an unnamed instance hypothesis, from a `[…]` binder |
| `a✝ : x ∈ ↑s` | a hypothesis you did not name (introduced with `_`) |
| `case refine_1` | the first goal `?_` left by `refine`; `refine_4.refine_1` is the first `?_` of a `refine` made inside goal `refine_4` |
| `b_1`, `a_1` | bound variables Lean renamed because `a`, `b` are already taken |

---

## Part 1 · `einstein_solid`

Statement: `Nat.card {f : Fin N → ℕ // ∑ i, f i = q} = (N + q - 1).choose q`. The number of ways to put `q`
quanta on `N` oscillators is `C(N + q - 1, q)`. A microstate is the same as a multiset of `q` sites (each
quantum names the site it sits on), and multisets are counted by stars and bars.

**R1 · `Nat.card_congr`** changes the **goal**. The lemma is `Nat.card_congr (e : α ≃ β) : Nat.card α = Nat.card β`.
Right to left, `rw [← Nat.card_congr e]` replaces `Nat.card β` by `Nat.card α`. With `exact` it closes an
equation `Nat.card α = Nat.card β` (R8). Placeholders: `{α β : Type} (e : α ≃ β)`.

| Before | After |
|---|---|
| `⊢ P (Nat.card β)` | `⊢ P (Nat.card α)` |

**R2 · `Sym.equivNatSumOfFintype α n`** is an equivalence `Sym α n ≃ { P // ∑ i, P i = n }` (`P : α → ℕ`): a
multiset of size `n` corresponds to its multiplicity function, whose values add up to `n`. Fed to R1 it
changes the **goal**. Placeholders: `{α : Type} [Fintype α] [DecidableEq α] (n : ℕ)`. `Fin N` meets both
brackets (`DecidableEq`: equality of elements can be decided).

| Before | After `rw [← Nat.card_congr (Sym.equivNatSumOfFintype α n)]` |
|---|---|
| `⊢ P (Nat.card { f // ∑ i, f i = n })` | `⊢ P (Nat.card (Sym α n))` |

**R3 · `rw [Nat.card_eq_fintype_card]`** changes the **goal**. The lemma is `Nat.card α = Fintype.card α`:
for a type with a `Fintype` instance the two sizes agree. Placeholders: `{α : Type} [Fintype α]`;
`Fin n`, `Bool`, `Sym (Fin n) k` qualify.

| Before | After |
|---|---|
| `⊢ P (Nat.card α)` | `⊢ P (Fintype.card α)` |

**R4 · `rw [Sym.card_sym_eq_choose]`** changes the **goal**. The lemma is stars and bars,
`Fintype.card (Sym α k) = (Fintype.card α + k - 1).choose k`. Placeholders:
`{α : Type} [Fintype α] [DecidableEq α] (k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Fintype.card (Sym α k))` | `⊢ P ((Fintype.card α + k - 1).choose k)` |

**R5 · `rw [Fintype.card_fin]`** changes the **goal**: `Fintype.card (Fin n) = n`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Fintype.card (Fin n))` | `⊢ P n` |

**W1 · multisets of size 3 over `Bool`** (`C(2 + 3 - 1, 3) = 4`): R3, R4, then `Fintype.card_bool`
(`Fintype.card Bool = 2`), then `rfl` evaluates the binomial.

```lean-goal
⊢ Nat.card (Sym Bool 3) = 4
⊢ Fintype.card (Sym Bool 3) = 4
⊢ (Fintype.card Bool + 3 - 1).choose 3 = 4
⊢ (2 + 3 - 1).choose 3 = 4
```

---

## Part 2 · `card_eq` (MILESTONE)

Statement: `Nat.card {f : Fin n → ℕ // ∑ i, f i = k} = (Finset.Nat.antidiagonalTuple n k).card`. The same count
as the size of a Finset, so that Finset lemmas (products, filters, sums over fibres) apply in Parts 3–4.

**R6 · `rw [← Nat.card_eq_finsetCard]`** changes the **goal**. The lemma is `Nat.card ↥s = s.card`; right to
left it turns a Finset's size into the size of the type `↥s = { x // x ∈ s }`. Placeholders:
`{α : Type} (s : Finset α)`.

| Before | After |
|---|---|
| `⊢ P s.card` | `⊢ P (Nat.card ↥s)` |

**R7 · `Finset.Nat.mem_antidiagonalTuple`** changes the **goal** (or a hypothesis, with `at h` or in a
`simp only […] at h`). The lemma is `x ∈ Finset.Nat.antidiagonalTuple k n ↔ ∑ i, x i = n`.
Placeholders: `(k n : ℕ) (x : Fin k → ℕ)`.

| Before | After |
|---|---|
| `⊢ x ∈ Finset.Nat.antidiagonalTuple k n` | `⊢ ∑ i, x i = n` |

**R8 · `Equiv.subtypeEquivRight`** builds an equivalence between two subtypes of the same type from a
pointwise `↔`: `(∀ x, p x ↔ q x) → { x // p x } ≃ { x // q x }`. Passed to R1 with `exact`, it **closes** the
goal. `(h x).symm` turns `q x ↔ p x` into `p x ↔ q x`. Placeholders: `{α : Type} (p q : α → Prop)`.

| Before | After `exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (h x).symm)` |
|---|---|
| `⊢ Nat.card { x // p x } = Nat.card { x // q x }` (with `h : ∀ (x : α), q x ↔ p x`) | no goals |

---

## Part 3 · `fibre_card` (MILESTONE)

Statement: for `k ≤ q`, the joint states of `A ⊔ B` with `q` quanta in which `A` holds exactly `k` are as many
as (states of `A` with `k`) × (states of `B` with `q - k`). The bijection cuts a tuple on `a + b` sites into its
first `a` and last `b` entries; `Fin.append` glues them back.

**R9 · `rw [← Finset.card_product]`** changes the **goal**. The lemma is `(s ×ˢ t).card = s.card * t.card`.
Placeholders: `{α β : Type} (s : Finset α) (t : Finset β)`.

| Before | After |
|---|---|
| `⊢ P (s.card * t.card)` | `⊢ P (s ×ˢ t).card` |

**R10 · `refine Finset.card_nbij' i j ?_ ?_ ?_ ?_`** changes the **goal list**: `s.card = t.card` becomes the
four facts that make `i : α → β` a bijection `s → t` with inverse `j : β → α`. Placeholders:
`{α β : Type} (s : Finset α) (t : Finset β) (i : α → β) (j : β → α)`.

| Before | After |
|---|---|
| `⊢ s.card = t.card` | `⊢ Set.MapsTo i ↑s ↑t`, `⊢ Set.MapsTo j ↑t ↑s`, `⊢ Set.LeftInvOn j i ↑s`, `⊢ Set.RightInvOn j i ↑t` |

**R11 · `intro x hx` on `Set.MapsTo`** changes the **context and the goal**. `Set.MapsTo f A B` is by definition
`∀ ⦃x⦄, x ∈ A → f x ∈ B`, so `intro` works on it directly. When `f` is a `fun`, the new goal reads
`(fun x => …) x ∈ …`; the next `simp only` beta-reduces it. Placeholders:
`{α β : Type} (f : α → β) (s : Finset α) (t : Finset β)`.

| Before | After |
|---|---|
| `⊢ Set.MapsTo f ↑s ↑t` | `x : α, hx : x ∈ ↑s ⊢ f x ∈ ↑t` |

**R12 · `simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx`** changes the **context**: membership in a
coerced filter becomes a conjunction. `Finset.coe_filter : ↑{x ∈ s | p x} = {x | x ∈ s ∧ p x}` and
`Set.mem_setOf_eq : (a ∈ {x | p x}) = p a`. Use it on the goal by dropping `at hx`. Placeholders:
`{α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p]` (`p` can be decided for each `x`; equations
of naturals can).

| Before | After |
|---|---|
| `hx : x ∈ ↑({y ∈ s \| p y})` | `hx : x ∈ s ∧ p x ⊢ p x` |

**R13 · `simp only [Finset.mem_coe]`** changes the **goal**: `Finset.mem_coe : a ∈ ↑s ↔ a ∈ s`. Placeholders:
`{α : Type} (s : Finset α) (a : α)`.

| Before | After |
|---|---|
| `⊢ a ∈ ↑s` | `⊢ a ∈ s` |

**R14 · `Finset.coe_product`, `Set.mem_prod`, then R13** change the **goal**: membership of a pair in a coerced
product becomes one membership per component. `Finset.coe_product : ↑(s ×ˢ t) = ↑s ×ˢ ↑t`,
`Set.mem_prod : p ∈ A ×ˢ B ↔ p.1 ∈ A ∧ p.2 ∈ B`. In practice: one `simp only [Finset.coe_product,
Set.mem_prod, Finset.mem_coe]`. Placeholders: `{α β : Type} (s : Finset α) (t : Finset β) (p : α × β)`.

| Before | After `Finset.coe_product` | After `Set.mem_prod` | After `Finset.mem_coe` |
|---|---|---|---|
| `⊢ p ∈ ↑(s ×ˢ t)` | `⊢ p ∈ ↑s ×ˢ ↑t` | `⊢ p.1 ∈ ↑s ∧ p.2 ∈ ↑t` | `⊢ p.1 ∈ s ∧ p.2 ∈ t` |

**R15 · `Fin.sum_univ_add`** changes the **goal**: a sum over `Fin (a + b)` splits into the first `a` terms and
the last `b` terms, `∑ i, f i = ∑ i, f (Fin.castAdd b i) + ∑ i, f (Fin.natAdd a i)`. This is how "the total
of `x`" becomes "quanta of `A` + quanta of `B`". Placeholders: `{M : Type} [AddCommMonoid M] (a b : ℕ)
(f : Fin (a + b) → M)` (`M` has a commutative `+` with `0`; `ℕ` qualifies).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (∑ i, f (Fin.castAdd b i) + ∑ i, f (Fin.natAdd a i))` |

**R16 · `Fin.append_left`, `Fin.append_right`** change the **goal**: `Fin.append u v (Fin.castAdd n i) = u i`
and `Fin.append u v (Fin.natAdd m j) = v j`. Placeholders: `{α : Type} (m n : ℕ) (u : Fin m → α)
(v : Fin n → α) (i : Fin m) (j : Fin n)`, `P : α → α → Prop`.

| Before | After `simp only [Fin.append_left, Fin.append_right]` |
|---|---|
| `⊢ P (Fin.append u v (Fin.castAdd n i)) (Fin.append u v (Fin.natAdd m j))` | `⊢ P (u i) (v j)` |

**R17 · `omega`** **closes** linear arithmetic over `ℕ` and `ℤ` from the hypotheses in context. A term it does
not understand, such as `∑ i, f i`, counts as one unknown. It knows truncated subtraction (`q - k = 0` when
`k > q`), so it needs `k ≤ q` (here `hk`) to treat `q - k` as a true difference. Placeholders:
`(f : Fin n → ℕ) (g : Fin m → ℕ) (q k : ℕ)`.

| Before | After |
|---|---|
| `⊢ ∑ i, f i = k ∧ ∑ j, g j = q - k` (with `h : ∑ i, f i + ∑ j, g j = q ∧ ∑ i, f i = k`) | no goals |

**R18 · `intro x _` on `Set.LeftInvOn`** changes the **context and the goal**. `Set.LeftInvOn j i A` is
`∀ ⦃x⦄, x ∈ A → j (i x) = x`; `Set.RightInvOn j i B` is the same with `i (j y) = y`. The membership is rarely
needed, so `_` leaves it unnamed (`a✝`). Placeholders: `{α β : Type} (s : Finset α) (i : α → β) (j : β → α)`.

| Before | After |
|---|---|
| `⊢ Set.LeftInvOn j i ↑s` | `x : α, a✝ : x ∈ ↑s ⊢ j (i x) = x` |

**R19 · `exact Fin.append_castAdd_natAdd`** **closes** the goal "glue the two blocks of `f` back together and get
`f`". Lean accepts it even when the goal still shows unreduced `(fun p => …) (…)`, since `exact` compares up
to unfolding. Placeholders: `{α : Type} (m n : ℕ) (f : Fin (m + n) → α)`.

| Before | After |
|---|---|
| `⊢ (Fin.append (fun i => f (Fin.castAdd n i)) fun j => f (Fin.natAdd m j)) = f` | no goals |

**R20 · `refine Prod.ext ?_ ?_`** changes the **goal list**: two pairs are equal when both components are.
`Prod.ext : x.1 = y.1 → x.2 = y.2 → x = y`. Placeholders: `{α β : Type} (x y : α × β)`.

| Before | After |
|---|---|
| `⊢ x = y` | `⊢ x.1 = y.1`, `⊢ x.2 = y.2` |

**R21 · `funext h`** is a term: from `h : ∀ x, f x = g x` it proves `f = g`, so `exact funext h` **closes** the
goal. In `fibre_card` the pointwise fact is R16 itself, `Fin.append_left _ _ : ∀ i, …`.
Placeholders: `{α β : Type} (f g : α → β)`.

| Before | After |
|---|---|
| `⊢ f = g` (with `h : ∀ (x : α), f x = g x`) | no goals |

**W2 · a bijection by R10: swapping the factors of a product.** `refine Finset.card_nbij' Prod.swap Prod.swap
?_ ?_ ?_ ?_` on `(s ×ˢ t).card = (t ×ˢ s).card` leaves four goals. The two `MapsTo` goals close with R11, then
R14 on `hp` and on the goal (`at hp ⊢`), then `⟨hp.2, hp.1⟩`; the two inverse goals with R18 and `rfl`.

```lean-goal
⊢ (s ×ˢ t).card = (t ×ˢ s).card
⊢ Set.MapsTo Prod.swap ↑(s ×ˢ t) ↑(t ×ˢ s)
⊢ Set.MapsTo Prod.swap ↑(t ×ˢ s) ↑(s ×ˢ t)
⊢ Set.LeftInvOn Prod.swap Prod.swap ↑(s ×ˢ t)
⊢ Set.RightInvOn Prod.swap Prod.swap ↑(t ×ˢ s)
```

**W3 · the sum of an appended tuple.** R15 splits the sum, then R16 evaluates `Fin.append` on each block, and
the goal closes:

```lean-goal
⊢ ∑ i, Fin.append u v i = ∑ i, u i + ∑ j, v j
⊢ ∑ i, Fin.append u v (Fin.castAdd n i) + ∑ i, Fin.append u v (Fin.natAdd m i) = ∑ i, u i + ∑ j, v j
```

---

## Part 4 · `thermal_contact`

Statement: `Ω_{a+b}(q) = ∑_{k=0}^{q} Ω_a(k) · Ω_b(q - k)`, every `Ω` written as a `Nat.card` of a subtype. Sort
the joint states by how many quanta `A` holds (`k ∈ {0, …, q}`), and count each class with `fibre_card`.

**R22 · `simp only [h]` with `h : ∀ k, f k = g k`** changes the **goal**: it rewrites every instance, also
under a binder such as the `k` of `∑ k ∈ s, …`. `rw [h]` fails there, because `rw` cannot rewrite a term
that mentions a bound variable. A milestone such as `card_eq` is used the same way. `simp` may rename the
bound variable (`k` → `x`). Placeholders: `(f g : ℕ → ℕ) (s : Finset ℕ)`.

| Before | After |
|---|---|
| `⊢ P (∑ k ∈ s, f k)` | `⊢ P (∑ x ∈ s, g x)` |

**R23 · `rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := t)]`** changes the **goal list**. The lemma is
`Set.MapsTo f ↑s ↑t → s.card = ∑ b ∈ t, {a ∈ s | f a = b}.card`: count `s` by the value of `f`, one fibre per
`b ∈ t`. The goal is rewritten and the side goal `Set.MapsTo f ↑s ↑t` is added after it. Name `f` and `t`:
the goal `s.card` only determines `s`. Placeholders: `{ι M : Type} [DecidableEq M] (f : ι → M)
(s : Finset ι) (t : Finset M)` (`ℕ` meets `DecidableEq`).

| Before | After |
|---|---|
| `⊢ P s.card` | goal 1 below, then `⊢ Set.MapsTo f ↑s ↑t` |

```lean-goal
⊢ P (∑ b ∈ t, {a ∈ s | f a = b}.card)
```

**R24 · `refine Finset.sum_congr rfl ?_`** changes the **goal**: two sums over the same Finset are equal when
the terms are. `Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`; `rfl` proves
`s = s`. As a term, `Finset.sum_congr rfl fun k hk => …` gives the termwise proof directly.
Placeholders: `{ι : Type} (s : Finset ι) (f g : ι → ℕ)`.

| Before | After |
|---|---|
| `⊢ ∑ x ∈ s, f x = ∑ x ∈ s, g x` | `⊢ ∀ x ∈ s, f x = g x` |

**R25 · `Finset.mem_range`** changes the **context** (with `at hm`) or the goal: `m ∈ Finset.range n ↔ m < n`.
Placeholders: `(m n : ℕ)`. As a term, `Finset.mem_range.mp hm : m < n`.

| Before | After `rw [Finset.mem_range] at hm` |
|---|---|
| `hm : m ∈ Finset.range (n + 1) ⊢ m < n + 1` | `hm : m < n + 1 ⊢ m < n + 1` |

**R26 · `Nat.lt_succ_iff`** is `m < n.succ ↔ m ≤ n` (`n.succ` is `n + 1`); `Nat.lt_succ_iff.mp hm` turns
`hm : m < n + 1` into `m ≤ n`, which is the `hk` that `fibre_card` asks for. `omega` (R17) proves the same.
Placeholders: `(m n : ℕ)`.

| Before | After `exact Nat.lt_succ_iff.mp hm` |
|---|---|
| `hm : m < n + 1 ⊢ m ≤ n` | no goals |

**W4 · fibres of `{0, …, 5}` by parity.** R23 with `f := fun x => x % 2`, `t := Finset.range 2`: the main goal
closes by itself (`rw` tries `rfl`), the side goal is handled by R11, R13 with R25, then R17.

```lean-goal
⊢ (Finset.range 6).card = ∑ r ∈ Finset.range 2, {x ∈ Finset.range 6 | x % 2 = r}.card
⊢ Set.MapsTo (fun x => x % 2) ↑(Finset.range 6) ↑(Finset.range 2)
⊢ (fun x => x % 2) x ∈ ↑(Finset.range 2)
⊢ x % 2 < 2
```

---

## Traps

- Three sizes: `Nat.card α` (any type), `Fintype.card α` (a type with a `Fintype` instance), `s.card` (a
  Finset). Lemmas about one do not apply to the others; convert with R3 and R6.
- `Set.MapsTo f ↑s ↑t` goals show `x ∈ ↑s`, a membership in a coerced set. `simp only [Finset.mem_coe, …]`
  (R13) turns it into `x ∈ s`, after which R7 applies. For a filter, `Finset.coe_filter` and
  `Set.mem_setOf_eq` (R12) do the same.
- In a statement you write yourself, give a coercion its type: `x ∈ (↑s : Set α)`. A bare `↑s` with nothing
  saying `Set` elaborates as `x ∈ s`, and the lemmas above make no progress.
- `rw` cannot rewrite under `∑ k ∈ …, …`: use `simp only [card_eq]` (R22).
- R23 needs `(f := …)` and `(t := …)`. After it, the fibre's bound variables are printed as `b_1`, `a_1` when
  your theorem already uses `a`, `b`.
- `q - k` on `ℕ` is truncated. `omega` (R17) needs `hk : k ≤ q` in context to solve the membership goals.
- The `k` from `Finset.range (q + 1)` comes as `hk : k ∈ Finset.range (q + 1)`; `fibre_card` wants `k ≤ q`
  (R25, then R26).
- After `intro` on a `MapsTo` goal for a `fun`, the goal is `(fun x => …) x ∈ …`. `simp only` beta-reduces it;
  `rw` may fail to find a pattern inside it.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| change the type inside `Nat.card` along `e : α ≃ β` | `rw [← Nat.card_congr e]` | R1 |
| subtype of multiplicity functions → multisets | `Sym.equivNatSumOfFintype α n` | R2 |
| `Nat.card` → `Fintype.card` | `rw [Nat.card_eq_fintype_card]` | R3 |
| stars and bars | `rw [Sym.card_sym_eq_choose]` | R4 |
| `Fintype.card (Fin n)` → `n` | `rw [Fintype.card_fin]` | R5 |
| `s.card` → `Nat.card ↥s` | `rw [← Nat.card_eq_finsetCard]` | R6 |
| `x ∈ antidiagonalTuple k n` ↔ `∑ i, x i = n` | `Finset.Nat.mem_antidiagonalTuple` | R7 |
| `Nat.card {x // p x} = Nat.card {x // q x}` | `exact Nat.card_congr (Equiv.subtypeEquivRight h)` | R8 |
| `s.card * t.card` → `(s ×ˢ t).card` | `rw [← Finset.card_product]` | R9 |
| count by a bijection `i`, inverse `j` | `refine Finset.card_nbij' i j ?_ ?_ ?_ ?_` | R10 |
| open a `MapsTo` / `LeftInvOn` goal | `intro x hx` / `intro x _` | R11, R18 |
| `x ∈ ↑{y ∈ s \| p y}` → `x ∈ s ∧ p x` | `simp only [Finset.coe_filter, Set.mem_setOf_eq]` | R12 |
| `x ∈ ↑s` → `x ∈ s` | `simp only [Finset.mem_coe]` | R13 |
| `p ∈ ↑(s ×ˢ t)` → `p.1 ∈ s ∧ p.2 ∈ t` | `simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]` | R14 |
| split a sum over `Fin (a + b)` | `rw [Fin.sum_univ_add]` / `simp only [Fin.sum_univ_add]` | R15 |
| evaluate `Fin.append u v` on a block | `simp only [Fin.append_left, Fin.append_right]` | R16 |
| linear arithmetic over `ℕ` | `omega` | R17 |
| glue the two blocks of `f` back | `exact Fin.append_castAdd_natAdd` | R19 |
| equality of pairs / of functions | `Prod.ext h₁ h₂` / `funext h` | R20, R21 |
| rewrite under `∑` | `simp only [h]` | R22 |
| count by fibres of `f` over `t` | `rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := t)]` | R23 |
| equal sums, term by term | `Finset.sum_congr rfl fun k hk => …` | R24 |
| `k ∈ range (q + 1)` → `k ≤ q` | `Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)` | R25, R26 |
| see the state | infoview | |
