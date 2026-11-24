# M170 · Counting the allowed wavenumbers: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's tight-binding chain
(`TightBindingChain`, its wavenumber set `QuantaWaveNumber`), Mathlib's sets (`Set α`, set-builder
`{x | p x}`, `Set.range`), the cardinalities `Set.ncard`, `Nat.card`, `Fintype.card`, injective
functions, casts `ℕ → ℝ`, and the `positivity` and `exact_mod_cast` tactics.

**The physics in one paragraph.** A ring of `N` sites with spacing `a` (periodic boundary conditions:
site `N` is site `0`). A plane wave `exp(i k n a)` is single-valued on the ring only if
`exp(i k N a) = 1`, so `k ∈ (2π / (a N)) ℤ`, and `k` and `k + 2π/a` give the same wave. Picking one
representative per class in the Brillouin zone gives exactly `N` wavenumbers,
`k_m = 2π/(a N) · (m − ⌊N/2⌋)` for `m = 0, …, N − 1`. physlib calls this set `T.QuantaWaveNumber`.
The exercise: it has `N` elements. Proof idea: it is the image of `m ↦ k_m` on `Fin N`, and that map is
injective (an affine map with nonzero slope), so the image has as many elements as `Fin N`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`, `simp only` or `have`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- `G` with `g : … → G` is "any goal": the entry only adds a hypothesis, and `g` finishes the example.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddGroup α]` is a
  requirement on `α` (a *type class*); each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `T : TightBindingChain` | the chain's data: `T.N : ℕ` sites (with `T.N ≠ 0`), spacing `T.a : ℝ` with `T.a_pos : 0 < T.a`, on-site energy `T.E0`, hopping `T.t` |
| `T.QuantaWaveNumber` | the allowed wavenumbers, a `Set ℝ`; by definition `{x \| ∃ n : Fin T.N, 2 * Real.pi / (T.a * ↑T.N) * (↑↑n - ↑(T.N / 2)) = x}` |
| `Set α` | a set of elements of `α`, i.e. a predicate `α → Prop`; `x ∈ s` means `s x` |
| `{x \| p x}` | the set of `x` with property `p` (set-builder) |
| `Set.range f` | the image `{f i \| i}` of `f : ι → α` |
| `s.ncard` | `Set.ncard s : ℕ`, the number of elements of `s`, and **`0` if `s` is infinite** |
| `Nat.card α` | the number of elements of the type `α` (`0` if infinite) |
| `Fintype.card α` | the number of elements of a type with a `Fintype` instance (an explicit finite list of its elements) |
| `Fin k` | `{0, 1, …, k − 1}`; an element `n` is a natural number `↑n` with a proof `↑n < k` |
| `↑↑n` (in `ℝ`) | `n : Fin T.N` cast twice: → `ℕ` → `ℝ` |
| `↑(T.N / 2)` | `T.N / 2` computed in `ℕ`, i.e. `⌊N/2⌋`, then cast to `ℝ` |
| `↑T.N` | the natural number `T.N` cast to `ℝ` |
| `Real.pi` | `π` |
| `fun n => e` | the function `n ↦ e` |
| `Function.Injective f` | `∀ a b, f a = f b → a = b` |
| `inst✝ : NeZero n` | an anonymous instance saying `n ≠ 0`; every `TightBindingChain` provides `NeZero T.N` |
| `this`, `this✝` | the name `have` gives a fact you did not name; `✝` marks an older, shadowed one |

---

## Part 1 · `card_wavenumbers`

Statement: `T.QuantaWaveNumber.ncard = T.N`, the set of allowed wavenumbers has exactly `N` elements.
Because `ncard` is `0` for infinite sets, this also says the set is finite.

### The set as a range (milestone `hset`)

**R1 · `ext x`** changes the **goal and the context**. It uses `Set.ext`: two sets are equal when they
have the same members. Placeholders: `{α : Type} (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ s = t` | `x : α ⊢ x ∈ s ↔ x ∈ t` |

**R2 · `simp only [TightBindingChain.QuantaWaveNumber]`** changes the **goal**: it replaces the name by
its definition, a set-builder. Placeholders: `(T : TightBindingChain) (x : ℝ)`.

| Before | After |
|---|---|
| `⊢ x ∈ T.QuantaWaveNumber` | ⊢ x ∈ {x \| ∃ n, 2 * Real.pi / (T.a * ↑T.N) * (↑↑n - ↑(T.N / 2)) = x} |

The same two states as Lean prints them (a table cannot hold a bare `|` inside code):

```lean-goal
⊢ x ∈ T.QuantaWaveNumber
⊢ x ∈ {x | ∃ n, 2 * Real.pi / (T.a * ↑T.N) * (↑↑n - ↑(T.N / 2)) = x}
```

**R3 · `Set.mem_setOf_eq`** changes the **goal**. The lemma is `(a ∈ {x | p x}) = p a`: membership in a
set-builder is the property itself. Placeholders: `{α : Type} (p : α → Prop) (a : α)`.

| Before | After |
|---|---|
| ⊢ a ∈ {x \| p x} | `⊢ p a` |

```lean-goal
⊢ a ∈ {x | p x}
⊢ p a
```

**R4 · `Set.mem_range`** changes the **goal**. The lemma is `a ∈ Set.range f ↔ ∃ y, f y = a`.
Placeholders: `{α ι : Type} (f : ι → α) (a : α)`. When the two sides of your `↔` become the same text,
`simp only` closes the goal by itself: after R1–R4 the `hset` goal is done.

| Before | After |
|---|---|
| `⊢ a ∈ Set.range f` | `⊢ ∃ y, f y = a` |

### Counting the range

**R5 · `rw [Set.ncard_range_of_injective]`** changes the **goal list**. The lemma is
`Function.Injective f → (Set.range f).ncard = Nat.card ι`. `rw` rewrites the goal and appends the
hypothesis `Function.Injective f` as a new goal at the **end** of the list. Placeholders:
`{α ι : Type} (f : ι → α) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ (Set.range f).ncard = n` | `⊢ Nat.card ι = n`, `⊢ Function.Injective f` |

**R6 · `rw [Nat.card_eq_fintype_card]`** changes the **goal**. The lemma is
`Nat.card α = Fintype.card α` for a type with `[Fintype α]` (`Fin k` qualifies). Placeholders:
`{α : Type} [Fintype α] (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ Nat.card α = n` | `⊢ Fintype.card α = n` |

**R7 · `rw [Fintype.card_fin]`** changes the **goal**. The lemma is `Fintype.card (Fin k) = k`.
Placeholders: `(k : ℕ)`. In the exercise the goal becomes `T.N = T.N`, which `rw` closes by `rfl`;
only the injectivity goal from R5 is left.

| Before | After |
|---|---|
| `⊢ P (Fintype.card (Fin k))` | `⊢ P k` |

### Injectivity

**R8 · `intro a b h`** on `Function.Injective f` changes the **goal and the context**: `Function.Injective f`
is by definition `∀ a b, f a = f b → a = b`, and `intro` sees through the name. Placeholders:
`{α β : Type} (f : α → β)`. When `f` is a `fun`, `h` is printed unreduced,
`(fun n => …) m = (fun n => …) n` (W2); the lemmas below accept it as is.

| Before | After |
|---|---|
| `⊢ Function.Injective f` | `a b : α, h : f a = f b ⊢ a = b` |

**R9 · `have ha := T.a_pos`** changes the **context**. `T.a_pos : 0 < T.a` is a field of the structure:
the spacing is positive. Placeholders: `(T : TightBindingChain)`.

| Before | After |
|---|---|
| `⊢ G` | `ha : 0 < T.a ⊢ G` |

**R10 · `have hn := NeZero.pos n`** changes the **context**. The lemma is `[NeZero n] → 0 < n` in `ℕ`.
`NeZero n` is a type class meaning `n ≠ 0`; a `TightBindingChain` provides `NeZero T.N`, so
`NeZero.pos T.N : 0 < T.N`. Placeholders: `(n : ℕ) [NeZero n]`.

| Before | After |
|---|---|
| `⊢ G` | `hn : 0 < n ⊢ G` |

**R11 · `exact_mod_cast e`** **closes** a goal that is the statement of `e` up to casts. It moves the
casts out of the way with lemmas such as `Nat.cast_pos : 0 < (↑n : ℝ) ↔ 0 < n` and
`Nat.cast_inj : (↑a : ℝ) = ↑b ↔ a = b` (R16). Placeholders: `(n : ℕ) (hn : 0 < n)`. To get
`0 < (T.N : ℝ)` from R10, write `have : (0 : ℝ) < T.N := by exact_mod_cast NeZero.pos T.N`.

| Before | After |
|---|---|
| `hn : 0 < n ⊢ 0 < ↑n` | closed |

**R12 · `positivity`** **closes** a goal `0 < e`, `0 ≤ e` or `e ≠ 0` when `e` is built from `+ * / ^`,
numerals, `Real.pi` and atoms it can bound: an atom `x` needs a hypothesis `0 < x` in the context.
Placeholders: `(x y : ℝ) (hx : 0 < x) (hy : 0 < y)`. In the exercise put `0 < T.a` (R9) and a positivity
fact for `T.N` (R10, R11) in the context first.

| Before | After |
|---|---|
| `hx : 0 < x, hy : 0 < y ⊢ Real.pi / (x * y) ≠ 0` | closed |

**R13 · `have h' := mul_left_cancel₀ ha h`** changes the **context**. The lemma is
`a ≠ 0 → a * b = a * c → b = c`. Placeholders: `{α : Type} [MonoidWithZero α] [IsCancelMulZero α] (a b c : α)`:
`α` has `*`, `1`, `0`, and nonzero factors cancel; `ℝ` and `ℂ` qualify (any field does).

| Before | After |
|---|---|
| `ha : a ≠ 0, h : a * b = a * c ⊢ b = c` | `h' : b = c ⊢ b = c` |

**R14 · `have h' := sub_left_inj.mp h`** changes the **context**. The lemma is
`sub_left_inj : b - a = c - a ↔ b = c` (subtracting the same `a` on the right), and `.mp` uses it left to
right. Placeholders: `{α : Type} [AddGroup α] (a b c : α)`; `ℤ`, `ℝ`, `ℂ` qualify, `ℕ` does not.

| Before | After |
|---|---|
| `h : b - a = c - a ⊢ b = c` | `h' : b = c ⊢ b = c` |

**R15 · `apply Fin.ext`** changes the **goal**: two elements of `Fin k` are equal when their values in `ℕ`
are. The lemma is `Fin.ext : (↑m : ℕ) = ↑n → m = n`. Placeholders: `{k : ℕ} (m n : Fin k)`. As a term:
`exact Fin.ext (by …)`.

| Before | After |
|---|---|
| `⊢ m = n` | `⊢ ↑m = ↑n` |

**R16 · `have h' := Nat.cast_inj.mp h`** changes the **context**. The lemma is
`Nat.cast_inj : (↑a : ℝ) = ↑b ↔ a = b` (the cast `ℕ → ℝ` is injective). Placeholders: `(a b : ℕ)`.
`exact_mod_cast h` (R11) does this step and closes the goal in one go.

| Before | After |
|---|---|
| `h : ↑a = ↑b ⊢ a = b` | `h' : a = b ⊢ a = b` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a set-builder as a range.** R1, then R3, then R4, which closes the `↔`:

```lean-goal
⊢ {x | ∃ n, 3 * ↑↑n + 1 = x} = Set.range fun n => 3 * ↑↑n + 1
⊢ x ∈ {x | ∃ n, 3 * ↑↑n + 1 = x} ↔ x ∈ Set.range fun n => 3 * ↑↑n + 1
⊢ (∃ n, 3 * ↑↑n + 1 = x) ↔ x ∈ Set.range fun n => 3 * ↑↑n + 1
```

**W2: injectivity of `n ↦ 3 (n − 2)` on `Fin 4`.** R8 gives `h` with the `fun` unreduced. Cancel the
factor (R13, with `(by norm_num : (3 : ℝ) ≠ 0)` as the nonzero proof), cancel the shift (R14), then
R15 and R11. The goal stays `m = n` until R15:

```lean-goal
⊢ Function.Injective fun n => 3 * (↑↑n - 2)
⊢ m = n
⊢ ↑m = ↑n
```

**W3: counting a range.** `rw [Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]`
(R5, R6, R7) closes the count `4 = 4` and leaves the side goal:

```lean-goal
⊢ (Set.range f).ncard = 4
⊢ Function.Injective f
```

---

## Traps

- `Set.ncard` of an infinite set is `0`. You never prove finiteness separately: the range of a map on
  `Fin N` is finite, and R5 handles it.
- State `hset` with exactly the formula of R2: `(n : ℝ)` for the index and `(T.N / 2 : ℕ)` for the shift
  (division in `ℕ`, so `⌊N/2⌋`, then cast). `(T.N : ℝ) / 2` is a different real number and the `ext`
  proof fails.
- The shift `↑(T.N / 2)` is the same on both sides of `h`; never compute it, cancel it (R14).
- `rw [Set.ncard_range_of_injective]` puts the injectivity goal **last**. After R6 and R7 the count is
  closed by `rfl`, so the next goal is injectivity.
- Write `(0 : ℝ) < T.N` with the type. A bare `0 < T.N` is a statement in `ℕ` (that is R10's form).
- `positivity` does not look up `T.a_pos` itself: put `0 < T.a` into the context first (R9).
- In `mul_left_cancel₀ hc h` the factor in `hc` must be literally the left factor of both sides of `h`:
  `2 * Real.pi / (T.a * ↑T.N)`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| set equality → membership | `ext x` | R1 |
| unfold the wavenumber set | `simp only [TightBindingChain.QuantaWaveNumber]` | R2 |
| `a ∈ {x \| p x}` → `p a` | `simp only [Set.mem_setOf_eq]` | R3 |
| `a ∈ Set.range f` → `∃ y, f y = a` | `simp only [Set.mem_range]` | R4 |
| count a range of an injective map | `rw [Set.ncard_range_of_injective]` (side goal: injectivity) | R5 |
| `Nat.card` → `Fintype.card` | `rw [Nat.card_eq_fintype_card]` | R6 |
| `Fintype.card (Fin k)` → `k` | `rw [Fintype.card_fin]` | R7 |
| start an injectivity proof | `intro m n h` | R8 |
| `0 < T.a` | `T.a_pos` | R9 |
| `0 < T.N` in `ℕ` / in `ℝ` | `NeZero.pos T.N` / `by exact_mod_cast NeZero.pos T.N` | R10, R11 |
| `e ≠ 0` or `0 < e` for a product/quotient of positives | `positivity` | R12 |
| `a * b = a * c`, `a ≠ 0` → `b = c` | `mul_left_cancel₀ ha h` | R13 |
| `b - a = c - a` → `b = c` | `sub_left_inj.mp h` | R14 |
| `m = n` in `Fin k` → values equal | `Fin.ext` | R15 |
| `(↑a : ℝ) = ↑b` → `a = b` | `Nat.cast_inj.mp h` or `exact_mod_cast h` | R16, R11 |
| see the state | infoview | |
