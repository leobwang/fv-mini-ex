# H042 · Cauchy ⇔ convergent in ℝ: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ` and absolute
value `|x|`, sets given by a property `{x | Q x}`, `Set.Nonempty`, `BddAbove`, the supremum `sSup`, and the
tactics `obtain`, `rintro`, `set`, `calc`, `positivity`, `linarith`, `ring_nf`.

The plan. (←) A convergent sequence is Cauchy: split `a m - a n` through the limit `L` (ε/2 trick,
milestone 1). (→) A Cauchy sequence converges: its limit is built as `L = sSup S`, where
`S = {x | ∃ M, ∀ n ≥ M, x < a n}` is the set of *eventual strict lower bounds* of `a`. If the tail from
`N` stays within `ε` of `a N`, then `a N - ε ∈ S` (milestone 2) and every element of `S` is `≤ a N + ε`
(milestone 3), so `sSup S` lies in `[a N - ε, a N + ε]`, and then so close to every `a n` with `n ≥ N`.

## How to read an entry

Each entry is one tactic or one lemma used with `have`/`exact`/`rw`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- `G : Prop` is an arbitrary goal. Many lemmas here are *forward* facts: `have h := lemma args` adds `h`
  to the context; in the guide a hypothesis `k : … → G` then consumes it.
- `Q`, `R` are arbitrary predicates (`Q : ℝ → Prop`, `Q : ℕ → Prop`, …) standing for "some property".
- Placeholders are written as Lean binders. All lemmas here are stated in Mathlib for general ordered
  types (type classes such as `[ConditionallyCompleteLattice α]`); `ℝ` meets every one of them, and the
  entries use `ℝ` directly.
- A goal or hypothesis containing `|` (absolute value, set-builder) cannot sit in a table cell; it is
  shown in a `lean-goal` block (one goal per line: before, then after) or in the text.
- Every `⊢` cell and every `lean-goal` line is a state Lean reaches in the companion file;
  `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | the real numbers (Mathlib's `Real`), a complete ordered field |
| `a : ℕ → ℝ`, `a n` | a real sequence and its `n`-th term |
| `\|x\|` | absolute value of `x` (Mathlib's `abs x`) |
| `ε > 0` | notation for `0 < ε` (`>` is `<` flipped) |
| `n ≥ N` | notation for `N ≤ n` |
| `∀ ε > 0, Q ε` | `∀ ε, ε > 0 → Q ε`: `intro ε hε` takes both (R1) |
| `∀ n ≥ N, Q n` | `∀ n, n ≥ N → Q n`: apply it as `h n hn` (R5) |
| `∃ N, Q N` | there is an `N` with `Q N`; take apart with `obtain ⟨N, hN⟩` (R2), build with `⟨N, proof⟩` (R4) |
| `Set ℝ` | a set of reals, i.e. a predicate `ℝ → Prop` |
| `{x \| Q x}` | the set of `x` with `Q x`; `y ∈ {x \| Q x}` is *by definition* `Q y` (R11) |
| `∀ x ∈ s, Q x` | `∀ x, x ∈ s → Q x`: `intro x hx` (or `rintro x ⟨…⟩`, R15) takes both |
| `s.Nonempty` | `∃ x, x ∈ s` (R20) |
| `BddAbove s` | some `b` satisfies `x ≤ b` for every `x ∈ s` (R21); Mathlib writes it `(upperBounds s).Nonempty` |
| `upperBounds s` | the set of `b` with `∀ x ∈ s, x ≤ b` |
| `sSup s` | the supremum (least upper bound) of `s`. Defined for *every* set; meaningful only when `s` is nonempty and bounded above (for other sets of reals it is the junk value `0`) |
| `max M N` | the larger of `M` and `N` |
| `S : Set ℝ := e` | a local definition made by `set` (R18): `S` abbreviates `e` |
| `ForallPos Q`, `SomeIndex Q` | toy definitions in the guide, shaped like `ConvergesTo` and `IsCauchy` |
| `case mp`, `case mpr` | after `constructor` on `↔`: the `→` and the `←` direction |

---

## Part 1 · `converges_cauchy` (milestone)

Statement: if `a` converges to `L` then `a` is Cauchy. For `m, n ≥ N` both `a m` and `a n` are within
`ε / 2` of `L`, so `|a m - a n| ≤ |a m - L| + |L - a n| < ε / 2 + ε / 2 = ε`.

**R1 · `intro ε hε`** changes the **goal and the context**. A goal whose definition unfolds to
`∀ ε > 0, Q ε` (here `IsCauchy a`) is introduced directly: `intro` unfolds the definition by itself.
Placeholders: `(Q : ℝ → Prop)`, `def ForallPos (Q) : Prop := ∀ ε > 0, Q ε`.

| Before | After |
|---|---|
| `⊢ ForallPos Q` | `ε : ℝ, hε : ε > 0 ⊢ Q ε` |

**R2 · `obtain ⟨N, hN⟩ := h x hx`** changes the **context**. Applying `h` to `x` and `hx : x > 0` unfolds
its definition (here `SomeIndex Q`, in the exercise `ConvergesTo a L` or `IsCauchy a`) and gives an `∃`;
`obtain ⟨N, hN⟩` splits it into the witness `N` and its property `hN`. The proof of `x > 0` can be written
inline: `h (ε / 2) (by positivity)` (R3). Placeholders: `(Q : ℝ → ℕ → Prop)`,
`def SomeIndex (Q) : Prop := ∀ ε > 0, ∃ N : ℕ, Q ε N`, `(x : ℝ) (hx : x > 0)`.

| Before | After |
|---|---|
| `h : SomeIndex Q, hx : x > 0 ⊢ G` | `N : ℕ, hN : Q x N ⊢ G` |

**R3 · `positivity`** **closes** a goal `0 < e` or `e > 0` when `e` is built from pieces it knows are
positive (numerals, hypotheses `hx : x > 0` in the context) by `+`, `*`, `/`, … Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `hx : x > 0 ⊢ x / 3 > 0` | no goals |

**R4 · `refine ⟨K, fun m hm n hn => ?_⟩`** changes the **goal and the context**: it gives the witness `K`
for the `∃` and introduces the binders of the `∀ m ≥ K, ∀ n ≥ K` that follows; `?_` is the remaining goal.
The `fun` part also sees through a definition: `refine ⟨L, fun ε hε => ?_⟩` proves `∃ L, ConvergesTo a L`
down to the body of `ConvergesTo`. Placeholders: `(P : ℕ → ℕ → Prop) (K : ℕ)`.

| Before | After |
|---|---|
| `⊢ ∃ N, ∀ m ≥ N, ∀ n ≥ N, P m n` | `m : ℕ, hm : m ≥ K, n : ℕ, hn : n ≥ K ⊢ P m n` |

**R5 · `have h1 := hK m hm`** changes the **context**: it instantiates `hK : ∀ n ≥ K, Q n` at `m`, with
`hm : m ≥ K` as the proof of the side condition. In the exercise `hN m hm` takes the Cauchy/convergence
hypothesis at one index (or `hN m hm n hn` at two). Placeholders: `(Q : ℕ → Prop) (K m : ℕ)`.

| Before | After |
|---|---|
| `hm : m ≥ K ⊢ Q m` | `h1 : Q m ⊢ Q m` |

**R6 · `calc`** **closes** the goal `a < d` with a chain of steps, each with its own proof (a term, or
`by tac`). The relations compose: `=` then `≤` then `<` gives `<`. Write the first term after `calc`, each
later line as `_ rel next := proof`. Placeholders: `(a b c d : ℝ)`.

| Before | After |
|---|---|
| `h1 : a = b, h2 : b ≤ c, h3 : c < d ⊢ a < d` | no goals |

**R7 · `ring_nf`** **closes** an equation whose two sides agree after normalising every ring expression,
also inside a function application such as `|·|`. Use it for the first `calc` step
`|a m - a n| = |(a m - L) + (L - a n)|`. `ring` itself fails there (it treats `|…|` as an opaque unknown and
does not look inside); it then falls back to `ring_nf` and prints "Try this: ring_nf". Placeholders:
`(f : ℝ → ℝ) (x y z : ℝ)`.

| Before | After |
|---|---|
| `⊢ f (x - y) = f (x - z + (z - y))` | no goals |

**R8 · `abs_add_le`** changes the **context**. The lemma is `abs_add_le a b : |a + b| ≤ |a| + |b|`, the
triangle inequality. As a `calc` step write `abs_add_le _ _`. Placeholders: `(x y : ℝ)`.

| Before | After `have h := abs_add_le x y` |
|---|---|
| `⊢ G` | context gains `h : \|x + y\| ≤ \|x\| + \|y\|`; goal `G` unchanged |

**R9 · `rw [abs_sub_comm x]`** changes the **goal**. The lemma is `abs_sub_comm a b : |a - b| = |b - a|`.
Giving the first argument `x` makes `rw` flip only `|x - _|`. In the exercise the split gives `|L - a n|`
while the hypothesis is about `|a n - L|`: `rw [abs_sub_comm L]`. Placeholders: `(x y : ℝ)`.

```lean-goal
⊢ P |x - y|
⊢ P |y - x|
```

**R10 · `add_lt_add`** **closes** a goal `a + c < b + d`. The lemma is
`add_lt_add : a < b → c < d → a + c < b + d`. Placeholders: `(a b c d : ℝ)`.

| Before | After |
|---|---|
| `h1 : a < b, h2 : c < d ⊢ a + c < b + d` | no goals |

The last `calc` step `ε / 2 + ε / 2 = ε` is `by ring` (TACTIC_STATES, "Closing").

**W1** chains R6, R7, R8, R10 and `ring` on a sum of two limits, starting from

```lean-goal
⊢ |x + y - (p + q)| < e
```

---

## Part 2 · `tail_lower` (milestone)

Statement: if every two terms from index `N` on are `ε`-close (`hN`), then `a N - ε ∈ S`: from index `N`
on, every `a n` is strictly above `a N - ε`.

**R11 · `Set.mem_setOf_eq`** changes the **goal**. The lemma is `(a ∈ {x | p x}) = p a`: membership in a
set-builder set *is* the property. Because this holds by definition, you can skip the `rw` and work on the
property directly: `refine ⟨N, fun n hn => ?_⟩` (R4) on `a N - ε ∈ {x | ∃ M, …}` already works.
Placeholders: `(Q : ℝ → Prop) (x : ℝ)`.

```lean-goal
⊢ x ∈ {y | Q y}
⊢ Q x
```

**R12 · `le_rfl`** proves `a ≤ a`. Since `K ≥ K` is `K ≤ K`, it is the side condition when you instantiate a
`∀ n ≥ K` hypothesis at `n := K` itself: `hN n hn N le_rfl`. Changes the **context** in the example.
Placeholders: `(Q : ℕ → Prop) (K : ℕ)`, `hK : ∀ n ≥ K, Q n`.

| Before | After |
|---|---|
| `⊢ G` | `h : Q K ⊢ G` |

**R13 · `rw [abs_lt] at h ⊢`** changes the **context and the goal**. The lemma is
`abs_lt : |a| < b ↔ -b < a ∧ a < b`. `at h` rewrites the hypothesis `h`, `at h ⊢` the hypothesis and the
goal together. Placeholders: `(x b y c : ℝ)`.

| Before | After |
|---|---|
| `h : \|x\| < b`, goal `\|y\| < c` (block below) | `h : -b < x ∧ x < b ⊢ -c < y ∧ y < c` |

```lean-goal
⊢ |y| < c
⊢ -c < y ∧ y < c
```

**R14 · `linarith`** **closes** a goal that is a linear (in)equality following from the hypotheses by
adding them with nonnegative coefficients. It uses hypotheses of the form `A ∧ B` with linear `A`, `B`, but
it treats `|x|` as an opaque unknown: unfold with R13 first. It does not split a goal `A ∧ B`: use
`constructor <;> linarith`. Placeholders: `(x y z : ℝ)`.

| Before | After |
|---|---|
| `h1 : -1 < x - y ∧ x - y < 1, h2 : y ≤ z ⊢ x < z + 1` | no goals |

---

## Part 3 · `tail_bound` (milestone)

Statement: with `hN` as in Part 2, every `x ∈ S` satisfies `x ≤ a N + ε`. If `x < a k` for all `k ≥ M`,
take `k = max M N`: then `x < a k` and `a k < a N + ε`.

**R15 · `rintro x ⟨M, hM⟩`** changes the **goal and the context**. It introduces `x` and takes the
membership `x ∈ {x | ∃ M, Q x M}` apart at once (membership is the `∃`, R11). The same tactic with only a
pattern, `rintro ⟨L, hL⟩`, takes apart the hypothesis of a goal `(∃ L, Q L) → G`.
Placeholders: `(Q : ℝ → ℕ → Prop) (G : ℝ → Prop)`.

```lean-goal
⊢ ∀ x ∈ {x | ∃ M, Q x M}, G x
```

| Before | After |
|---|---|
| goal in the block above | `x : ℝ, M : ℕ, hM : Q x M ⊢ G x` |

**R16 · `le_max_left`, `le_max_right`** change the **context** in the example. The lemmas are
`le_max_left a b : a ≤ max a b` and `le_max_right a b : b ≤ max a b`, i.e. `max M N ≥ M` and
`max M N ≥ N`: the side conditions for instantiating `hM : ∀ n ≥ M, …` and `hN : ∀ n ≥ N, …` at the common
index `max M N`. Placeholders: `(M N : ℕ) (Q R : ℕ → Prop)`.

| Before | After `have h1 := hM (max M N) (le_max_left M N)` | After `have h2 := hN (max M N) (le_max_right M N)` |
|---|---|---|
| `⊢ G` | `h1 : Q (max M N) ⊢ G` | `h2 : R (max M N) ⊢ G` |

Then R13 on the Cauchy fact and R14 finish, as in Part 2.

---

## Part 4 · `cauchy_iff_converges`

Statement: `IsCauchy a ↔ ∃ L, ConvergesTo a L`. Prove the three milestones first.

**R17 · `constructor`** on `A ↔ B` changes the **goal list**: one goal per direction, named `mp` (`A → B`)
and `mpr` (`B → A`). Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R18 · `set S : Set ℝ := e`** changes the **context and the goal**: the context gains the local definition
`S : Set ℝ := e`, and every `e` in the goal is replaced by `S`. Here it only names the set; the milestones
still mention `{x | …}` literally, and Lean accepts them for `S` because `S` unfolds to that. Placeholders:
`(Q : ℝ → Prop) (G : Set ℝ → Prop)`, with `e := {x | Q x}`.

| Before | After |
|---|---|
| goal `G {x \| Q x}` | context gains `S : Set ℝ := {x \| Q x}`; goal `G S` |

```lean-goal
⊢ G {x | Q x}
⊢ G S
```

**R19 · `one_pos`** proves `0 < 1`, which is `1 > 0`: the side condition when you use the Cauchy property at
`ε := 1`, as in `h 1 one_pos` or `obtain ⟨N0, hN0⟩ := h 1 one_pos` (R2). Changes the **context** in the
example. Placeholders: `(Q : ℝ → Prop)`, `h : ∀ e > 0, Q e`.

| Before | After |
|---|---|
| `⊢ G` | `h1 : Q 1 ⊢ G` |

**R20 · `Set.Nonempty`**: `s.Nonempty` is `∃ x, x ∈ s`, so `⟨x, hx⟩` proves it, and `⟨_, hx⟩` lets Lean read
`x` off `hx`. With milestone 2 as `hx`: `⟨_, tail_lower a 1 N0 hN0⟩`. **Closes** the goal. Placeholders:
`(s : Set ℝ) (x : ℝ)`.

| Before | After |
|---|---|
| `hx : x ∈ s ⊢ s.Nonempty` | no goals |

**R21 · `BddAbove`**: `BddAbove s` is defined as `(upperBounds s).Nonempty`, where `b ∈ upperBounds s` is
`∀ x ∈ s, x ≤ b`. So `⟨b, hb⟩` with `hb : ∀ x ∈ s, x ≤ b` proves it (milestone 3 has exactly this shape).
**Closes** the goal. Placeholders: `(s : Set ℝ) (b : ℝ)`.

| Before | After |
|---|---|
| `⊢ BddAbove s` | no goals |

**R22 · `le_csSup`** changes the **context**. The lemma is `le_csSup : BddAbove s → a ∈ s → a ≤ sSup s`:
an element of a bounded-above set is at most its supremum (`cs` = "conditionally complete": it needs the
boundedness hypothesis). Placeholders: `(s : Set ℝ) (x : ℝ)`.

| Before | After |
|---|---|
| `hb : BddAbove s, hx : x ∈ s ⊢ G` | `h : x ≤ sSup s ⊢ G` |

**R23 · `csSup_le`** changes the **context**. The lemma is
`csSup_le : s.Nonempty → (∀ b ∈ s, b ≤ a) → sSup s ≤ a`: the supremum of a nonempty set is at most any
upper bound. Placeholders: `(s : Set ℝ) (b : ℝ)`.

| Before | After |
|---|---|
| `hne : s.Nonempty ⊢ G` | `h : sSup s ≤ b ⊢ G` |

The final step uses R13 on the hypothesis and the goal together, then `constructor <;> linarith` (R14),
as in **W2**:

```lean-goal
⊢ |y - t| < 2 * e
⊢ -(2 * e) < y - t ∧ y - t < 2 * e
```

**W3** builds `Nonempty`, `BddAbove` and both `sSup` bounds for `T = {x | x < 1}`:

```lean-goal
⊢ sSup {x | x < 1} ≤ 1 ∧ 0 ≤ sSup {x | x < 1}
⊢ sSup T ≤ 1 ∧ 0 ≤ sSup T
```

---

## Traps

- **Imports are frozen** and `import` is on the `BANNED:` line: the toolbox is ℝ's order and `sSup` plus the
  tactics `linarith`, `positivity`, `ring` and Mathlib's common tactics. No filters or topology. Mathlib's own
  Cauchy sequences (`CauSeq`, `IsCauSeq`, its limit `lim`, `Real.cauchy`, …) are banned: build the limit as
  `sSup S` yourself.
- `sSup s` exists for every set, with a junk value when `s` is empty or unbounded. R22 and R23 therefore
  need `hbdd : BddAbove S` and `hne : S.Nonempty`: prove both first, from the Cauchy property at `ε = 1`
  (R19) and milestones 2 and 3.
- Milestones are separate theorems: call them with arguments, `tail_lower a _ N hN`; the `_` lets Lean read
  `ε` (here `ε / 2`) off `hN`.
- `n ≥ N` is `N ≤ n`. Instantiating at `n := N` needs `le_rfl` (R12); at the common index `max M N`,
  `le_max_left` / `le_max_right` (R16).
- The triangle split gives `|L - a n|`, the hypothesis is about `|a n - L|`: flip with
  `rw [abs_sub_comm L]` (R9).
- `linarith` and `ring` do not look inside `|·|`. Unfold `|·| < ε` with `rw [abs_lt]` (R13) first; prove the
  `calc` step `|a m - a n| = |(a m - L) + (L - a n)|` with `ring_nf` (R7), not `ring`.
- `linarith` does not prove a goal `A ∧ B`: `constructor <;> linarith`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| take `∀ ε > 0` (through a `def`) | `intro ε hε` | R1 |
| use an ε–N hypothesis at `x` | `obtain ⟨N, hN⟩ := h x (by positivity)` | R2, R3 |
| `0 < ε / 2` | `by positivity` | R3 |
| give `N`, take `m hm n hn` | `refine ⟨N, fun m hm n hn => ?_⟩` | R4 |
| a `∀ n ≥ N` fact at `m` | `have h1 := hN m hm` | R5 |
| chain `=`, `≤`, `<` | `calc a = b := … _ ≤ c := … _ < d := …` | R6 |
| equation under `\|·\|` | `by ring_nf` | R7 |
| triangle inequality | `abs_add_le _ _` | R8 |
| `\|x - y\|` → `\|y - x\|` | `rw [abs_sub_comm x]` | R9 |
| add two `<` | `add_lt_add h1 h2` | R10 |
| `x ∈ {y \| Q y}` → `Q x` | `rw [Set.mem_setOf_eq]` (or nothing: it is definitional) | R11 |
| `N ≥ N` | `le_rfl` | R12 |
| `\|x\| < b` → two inequalities | `rw [abs_lt] at h`, or at h ⊢ for the goal too | R13 |
| linear arithmetic | `linarith`; for `A ∧ B`: `constructor <;> linarith` | R14 |
| take `x ∈ {x \| ∃ M, …}` apart | `rintro x ⟨M, hM⟩` | R15 |
| `max M N ≥ M`, `≥ N` | `le_max_left M N`, `le_max_right M N` | R16 |
| split `↔` | `constructor` | R17 |
| name a set | `set S : Set ℝ := {x \| …}` | R18 |
| `1 > 0` | `one_pos` | R19 |
| `S.Nonempty` | `⟨_, hx⟩` | R20 |
| `BddAbove S` | `⟨b, hb⟩` with `hb : ∀ x ∈ S, x ≤ b` | R21 |
| `x ≤ sSup S` | `le_csSup hbdd hx` | R22 |
| `sSup S ≤ b` | `csSup_le hne hb` | R23 |
| see the state | infoview | |
