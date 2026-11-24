# M077 · Countable unions of countable sets: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's sets (`Set α`, `⊆`, `Set.univ`,
`Set.range`, indexed unions `⋃`), the Cantor pairing `Nat.pair` / `Nat.unpair`, and the `choose` tactic.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`obtain`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. A bare `P : Prop` or `R : Prop` is a goal the step leaves alone.
- Placeholders are written as Lean binders. `{α : Type}` is any type; `s t : Set α` are sets of elements of
  `α`; `f : ℕ → α` is a sequence in `α`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. A
  hypothesis that itself contains `, ` (such as `∀ (n : ℕ), …` or `⋃ i, s i`) is written as its own span next to the goal.

## Reading the goals

| You see | It means |
|---|---|
| `Set α` | sets of elements of `α`; a set is a predicate `α → Prop`, and `x ∈ s` is `s x` |
| `s ⊆ t` | `∀ x, x ∈ s → x ∈ t` (that is its definition, so `intro` works on it, R2) |
| `Set.univ` | the set of all elements of the type; `p ∈ Set.univ` is `True` |
| `Set.range f` | `{f y \| y}`, the values of `f`; `x ∈ Set.range f` is by definition `∃ y, f y = x` (`Set.mem_range`) |
| `⋃ i, s i` | the union of the family `s : ℕ → Set α`; `x ∈ ⋃ i, s i ↔ ∃ i, x ∈ s i` (`Set.mem_iUnion`) |
| `Nat.pair a b` | one natural number coding the pair `(a, b)`: `if a < b then b * b + a else a * a + a + b`, a bijection `ℕ × ℕ → ℕ` |
| `Nat.unpair k` | the pair coded by `k`, of type `ℕ × ℕ`; `k.unpair` is the same term, printed `Nat.unpair k` |
| `ℕ × ℕ`, `(a, b)` | the type of pairs of naturals, and the pair with coordinates `a`, `b` |
| `p.1`, `p.2` | the first and second coordinate of a pair `p : ℕ × ℕ`; `(p.1, p.2) = p` holds by `rfl` |
| `(Nat.unpair k).1` | the first coordinate of the pair coded by `k` (you write `k.unpair.1`) |
| `fun k => …` | a sequence written as a function; after `ext`/`simp` it can appear applied: `(fun k => …) n` |
| `a✝ : p ∈ Set.univ` | an unnamed hypothesis (from `intro p _`); you cannot refer to it, which is fine |
| `Type u_1` | the universe of `α` in the problem (it says `Type*`); the guide uses `Type`, which behaves the same |

---

## Part 1 · `enumerable_prod`

Statement: `Enumerable (Set.univ : Set (ℕ × ℕ))`, i.e. some sequence `ℕ → ℕ × ℕ` hits every pair.
`Enumerable s` is a `def` whose body is `∃ f : ℕ → α, s ⊆ Set.range f`; `refine`/`exact ⟨…⟩` and `choose`
unfold it by themselves.

**R1 · `refine ⟨f, ?_⟩`** changes the **goal**: it supplies the witness of an `∃` and leaves its property to
prove. It works on a definition whose body is an `∃` (W1), such as `Enumerable s`. Placeholders:
`{α : Type} (s : Set α) (f : ℕ → α)`.

| Before | After |
|---|---|
| `⊢ ∃ g, s ⊆ Set.range g` | `⊢ s ⊆ Set.range f` |

**R2 · `intro x hx`** on `s ⊆ t` changes the **goal and the context**: `⊆` unfolds to `∀ x, x ∈ s → x ∈ t`, so
`intro` takes the point and its membership. Write `intro p _` when the membership is useless (`p ∈ Set.univ`).
Placeholders: `{α : Type} (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ s ⊆ t` | `x : α, hx : x ∈ s ⊢ x ∈ t` |

**R3 · `refine ⟨y, ?_⟩`** on `x ∈ Set.range f` changes the **goal**: you name the index `y` and must show
`f y = x`. This works because `x ∈ Set.range f` is by definition `∃ y, f y = x` (`Set.mem_range`). Placeholders:
`{α : Type} (f : ℕ → α) (x : α) (y : ℕ)`.

| Before | After |
|---|---|
| `⊢ x ∈ Set.range f` | `⊢ f y = x` |

**R4 · `rw [Nat.unpair_pair]`** changes the **goal**. The lemma is
`Nat.unpair_pair (a b : ℕ) : Nat.unpair (Nat.pair a b) = (a, b)`: decoding a code gives back the pair.
`simp [Nat.unpair_pair]` does the same and also reduces `(a, b).1` to `a`. Placeholders: `(a b : ℕ)`,
`(P : ℕ × ℕ → Prop)`. On `Nat.unpair (Nat.pair p.1 p.2) = p`, `rw [Nat.unpair_pair]` leaves
`(p.1, p.2) = p`, which `rw` then closes by `rfl` (a pair is its coordinates, by definition).

| Before | After |
|---|---|
| `⊢ P (Nat.unpair (Nat.pair a b))` | `⊢ P (a, b)` |

**W2: R2, R3, R4 on another sequence.** The first-coordinate sequence `fun k : ℕ => k.unpair.1` hits every
`n : ℕ`, with index `Nat.pair n 0`:

```lean-goal
⊢ Set.univ ⊆ Set.range fun k => (Nat.unpair k).1
⊢ n ∈ Set.range fun k => (Nat.unpair k).1
⊢ (fun k => (Nat.unpair k).1) (Nat.pair n 0) = n
```

`simp [Nat.unpair_pair]` closes the last goal (it applies the `fun`, then R4, then takes `.1`).

---

## Part 2 · `interleave`

Statement: a `def` with a hole. `interleave f : ℕ → α` must be **one** sequence that lists every `f n m`
(`f : ℕ → ℕ → α` is a sequence of sequences). Read the index `k` as the pair `(n, m)` it codes and return entry
`m` of sequence `n`. It must be an actual formula (computable): no `Classical.choose`, no `noncomputable`.

**R5 · `simp only [d]`** on a sequence `d := fun k => …` changes the **goal**: it replaces `d k` by the body
with `k` plugged in. This is how you look inside your own `interleave` in Part 3. The two coordinates of the
pair coded by `k` are written `k.unpair.1`, `k.unpair.2` and printed `(Nat.unpair k).1`, `(Nat.unpair k).2`.
Placeholders: `def sumCoords : ℕ → ℕ := fun k => k.unpair.1 + k.unpair.2`, `(k : ℕ) (P : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (sumCoords k)` | `⊢ P ((Nat.unpair k).1 + (Nat.unpair k).2)` |

**W3: R5, then R4.** Unfolding then decoding evaluates the sequence at a code; the final `rw` closes the goal
because both sides become equal:

```lean-goal
⊢ sumCoords (Nat.pair a b) = a + b
⊢ (Nat.unpair (Nat.pair a b)).1 + (Nat.unpair (Nat.pair a b)).2 = a + b
```

---

## Part 3 · `iUnion_subset_interleave`

Statement: if every `A n` lies in the range of `f n`, the union `⋃ n, A n` lies in the range of
`interleave f`. Take `x` in the union (R2), find its piece `n` (R6), find its index `m` in `f n` (R7, R8), and
give the index of `f n m` in `interleave f` (R3), checked with R5 and R4.

**R6 · `obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx`** changes the **context**: from `hx : x ∈ ⋃ i, s i` you get an
index `i` and `hi : x ∈ s i`. The lemma is `Set.mem_iUnion : x ∈ ⋃ i, s i ↔ ∃ i, x ∈ s i`; `.mp` is its
left-to-right direction (`h.mp : A → B` for `h : A ↔ B`). Placeholders: `{α : Type} (s : ℕ → Set α) (x : α)`.

| Before | After |
|---|---|
| `hx : x ∈ ⋃ i, s i` · `⊢ P` | `i : ℕ, hi : x ∈ s i ⊢ P` |

**R7 · `have hxt := hst hx`** changes the **context**: `hst : s ⊆ t` is a function from proofs of `x ∈ s` to
proofs of `x ∈ t`, so applying it to `hx` gives the new membership. In the problem `hf n : A n ⊆ Set.range (f n)`
is applied the same way. Placeholders: `{α : Type} (s t : Set α) (x : α)`.

| Before | After |
|---|---|
| `hst : s ⊆ t, hx : x ∈ s ⊢ x ∈ t` | `hxt : x ∈ t ⊢ x ∈ t` |

**R8 · `obtain ⟨m, rfl⟩ := hr`** on `hr : x ∈ Set.range f` changes the **context and the goal**: `hr` says
`∃ m, f m = x`; the pattern `rfl` uses the equation to replace `x` by `f m` everywhere and removes `x` and `hr`.
Placeholders: `{α : Type} (f : ℕ → α) (x : α) (P : α → Prop)`.

| Before | After |
|---|---|
| `hr : x ∈ Set.range f ⊢ P x` | `m : ℕ ⊢ P (f m)` |

**W4: R2, R8, R3 on a reindexed sequence.** `Set.range f ⊆ Set.range (fun k : ℕ => f k.unpair.2)`: the value
`f m` sits at index `Nat.pair 0 m`.

```lean-goal
⊢ x ∈ Set.range fun k => f (Nat.unpair k).2
⊢ f m ∈ Set.range fun k => f (Nat.unpair k).2
⊢ (fun k => f (Nat.unpair k).2) (Nat.pair 0 m) = f m
```

`simp [Nat.unpair_pair]` closes the last goal. With a named `def` instead of a `fun`, add its name:
`simp [d, Nat.unpair_pair]`.

**W5: R2, R6, R7.** If one sequence `f` covers every `s i`, it covers `⋃ i, s i`: after `intro x hx` and R6
the goal is still `⊢ x ∈ Set.range f`, and `exact hs i hi` (R7 as a term) closes it.

---

## Part 4 · `enumerable_iUnion`

Statement: a union of countably many enumerable sets is enumerable. `h : ∀ n, Enumerable (A n)` gives, for each
`n`, *some* sequence; `choose` turns that into one function `f : ℕ → ℕ → α`. Then Part 3 does the work.

**R9 · `choose F hF using h`** changes the **context**: from `h : ∀ n, ∃ g, Q n g` it makes a function `F` that
picks a witness for every `n`, and `hF` saying each pick works; `h` is removed. It unfolds `Enumerable`, so in
the problem you get `f : ℕ → ℕ → α` and `hf : ∀ (n : ℕ), A n ⊆ Set.range (f n)`. Placeholders:
`{α : Type} (Q : ℕ → (ℕ → α) → Prop) (R : Prop)`. (`choose` is classical; that is allowed in a proof, only the
`def interleave` must be computable.)

| Before | After |
|---|---|
| `h : ∀ (n : ℕ), ∃ g, Q n g` · `⊢ R` | `F : ℕ → ℕ → α` · `hF : ∀ (n : ℕ), Q n (F n)` · `⊢ R` |

Then R1 (as a term `⟨interleave f, …⟩`) with your Part 3 theorem as the property. A proved spec theorem is
used like a function: `iUnion_subset_interleave A f hf : ⋃ n, A n ⊆ Set.range (interleave f)`.

**W6: R9, R1.** From `h : ∀ n : ℕ, ∃ m, n < m`:

```lean-goal
⊢ ∃ g, ∀ (n : ℕ), n < g n
```

`choose g hg using h` adds `g : ℕ → ℕ` and `hg : ∀ (n : ℕ), n < g n` (the goal is unchanged), and
`exact ⟨g, hg⟩` closes it.

---

## Traps

- `interleave` must be computable (`noncomputable` is banned), so a body built with `Classical.choose` is
  rejected. Write the formula with `k.unpair`.
- The `Set.Countable` API (`Set.Countable`, `Set.countable_iUnion`, `Encodable`, …) is banned: the point is to
  build the enumerations yourself.
- A goal `x ∈ Set.range f` is an `∃`, not a `∀`: `intro` fails on it. Give the index with `refine ⟨y, ?_⟩` (R3).
- After `obtain ⟨m, rfl⟩`, the name `x` is gone; write `f n m` (or let Lean print it) instead. The context
  then shows `hx : f n m ∈ ⋃ n, A n`: the `n` after `⋃` is a bound variable, unrelated to your local `n`.
- `simp [Nat.unpair_pair]` alone does not unfold your `interleave`: pass its name too, `simp [interleave, …]`
  (R5).
- `k.unpair.1` is notation for `(Nat.unpair k).1`: both spellings are the same term.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| give the sequence of an `Enumerable`/`∃` | `refine ⟨f, ?_⟩` or `exact ⟨f, proof⟩` | R1 |
| prove `s ⊆ t` | `intro x hx` | R2 |
| prove `x ∈ Set.range f` | `refine ⟨y, ?_⟩` (goal `f y = x`) | R3 |
| decode a code | `rw [Nat.unpair_pair]`, `simp [Nat.unpair_pair]` | R4 |
| the pair coded by `k` | `k.unpair.1`, `k.unpair.2` | R5 |
| unfold your sequence `d k` | `simp only [d]` | R5 |
| use `hx : x ∈ ⋃ i, s i` | `obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx` | R6 |
| use `hst : s ⊆ t` on `hx : x ∈ s` | `hst hx` | R7 |
| use `hr : x ∈ Set.range f` | `obtain ⟨m, rfl⟩ := hr` | R8 |
| one witness per `n` | `choose F hF using h` | R9 |
| see the state | infoview | |
