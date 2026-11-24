# H043 · ℝ is uncountable: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def` by pattern matching, `theorem`, `intro`, `exact`,
`apply`, `have`, `refine`, `rcases`/`obtain` patterns, `induction … with`, `∃`/`∧`/`∨`/`¬`,
`Or.inl`/`Or.inr`, `<;>`.
**New here:** Mathlib's real numbers `ℝ` with their order, pairs `ℝ × ℝ`, `if` inside a `noncomputable`
definition, the tactics `split_ifs`, `push Not`, `linarith`, `set`, and the order library: `Monotone`,
`Antitone`, `max`, `Set.range`, `upperBounds`, `BddAbove`, `sSup`.

**The maths (Cantor's nested intervals).** Given `f : ℕ → ℝ`, build closed intervals `[lₙ, rₙ]` with
`lₙ < rₙ`, starting from `[0, 1]`. Step `n` cuts `[a, b]` into thirds and keeps an outer third that
misses `f n`: if `f n < (a + 2b)/3` keep `[(a + 2b)/3, b]`, else (`f n ≥ (a + 2b)/3 > (2a + b)/3`) keep
`[a, (2a + b)/3]`. So `f n ∉ [lₙ₊₁, rₙ₊₁]`. The left ends increase, the right ends decrease, and every
left end is below every right end (`lₙ ≤ l_{max n m} < r_{max n m} ≤ r_m`). Hence
`x = sup {lₙ}` exists and satisfies `lₖ ≤ x ≤ rₖ` for every `k`; with `k = n + 1`, `x ≠ f n`.

The guide never uses the exercise's `step` or `I`; it uses placeholders and toy objects: `order` (sort a
pair), the sequence `T`, and the halving sequence `J`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
gives the lemma's statement and its placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`), or the whole goal (`P : Prop`). A hypothesis `h` in an
  entry is only there to finish the example.
- `{α : Type}` is any type. A bracket such as `[Preorder α]` is a requirement on `α` (a *type class*: here,
  `α` has a reflexive, transitive `≤`). `ℕ` and `ℝ` meet every order bracket used here.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers; `/` is exact division (`(a + 2 * b) / 3`), not `ℕ`'s rounding division |
| `ℝ × ℝ`, `(a, b)` | the type of pairs of reals; the pair with first component `a`, second `b` |
| `p.1`, `p.2` | the first and second component of the pair `p` (`(a, b).1` is `a` after `simp only`) |
| `(step p z).1` | the left end of the interval `step p z`; `(I f n).1`, `(I f n).2` are `lₙ`, `rₙ` |
| `if c then x else y` | `x` when `c` holds, `y` otherwise; `c` must be decidable (on `ℝ`, classically) |
| `noncomputable def` | a definition Lean cannot run as a program (comparisons of reals are not computable) |
| `case pos`, `case neg` | after `split_ifs`: the branch where the condition holds / fails |
| `case zero`, `case succ`, `case inl`, `case h₁`, `case pos.refine_1` | goal labels from `induction`, `rcases … with h \| h`, `apply` (one per premise) and `refine` (one per `?_`); only names, not part of the goal |
| `¬a < b` | the negation; `push Not` turns it into `b ≤ a` |
| `max a b` | the larger of `a` and `b` |
| `Monotone g` | `∀ ⦃a b⦄, a ≤ b → g a ≤ g b` (`g` never decreases) |
| `Antitone g` | `∀ ⦃a b⦄, a ≤ b → g b ≤ g a` (`g` never increases) |
| `⦃a b⦄` | strict-implicit arguments: `hm hab` fills `a b` from `hab : a ≤ b` |
| `Monotone fun n => (J n).1` | `Monotone` applied to the function `n ↦ (J n).1` |
| `Set.range g` | the set of values `{y \| ∃ k, g k = y}` of `g : ℕ → ℝ` |
| `s.Nonempty` | `∃ y, y ∈ s` |
| `upperBounds s` | `{M \| ∀ ⦃y⦄, y ∈ s → y ≤ M}` |
| `BddAbove s` | `∃ M, M ∈ upperBounds s` (some upper bound exists) |
| `sSup s` | the least upper bound (supremum) of `s : Set ℝ`; meaningful when `s` is nonempty and bounded above |
| `∀ b ∈ s, P b` | `∀ b, b ∈ s → P b` |
| `x : ℝ := e` | after `set`: `x` is a local name for `e`; Lean may shorten it to `x : ℝ := ⋯` |
| `(fun k => (I f k).1) k` | the function applied to `k`, i.e. `(I f k).1`; appears after `rintro _ ⟨k, rfl⟩` on `Set.range fun k => …`. `exact` accepts it as is; `simp only` rewrites it to `(I f k).1` |
| `a ≠ b` | `a = b → False` |
| `inst✝ : Decidable c` | an anonymous type-class hypothesis (here: `c` can be decided by `if`) |

---

## Part 1 · `step` (milestone definition)

Statement: `step p z` is the interval kept from `p = (a, b)`: `[(a + 2b)/3, b]` if `z < (a + 2b)/3`, else
`[a, (2a + b)/3]`.

**R1 · `if c then (a, b) else (a', b')`** is a definition body (it changes no proof state) that returns one
of two pairs. The test `c` is a real comparison such as `z < (p.1 + 2 * p.2) / 3`; that is why the
definition is `noncomputable`.
Guide example: `order p := if p.1 ≤ p.2 then p else (p.2, p.1)` (sort a pair). Test your `step` with a
small `example` and `norm_num [step]`.

## Part 2 · `step_spec` (milestone)

Statement: if `p.1 < p.2`, the new interval is nonempty, nested in `p`, and `z` lies strictly outside it.

**R2 · `unfold d`** changes the **goal**: the defined name is replaced by its body.
Placeholders: `(p : ℝ × ℝ) (P : ℝ × ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (order p)` | `⊢ P (if p.1 ≤ p.2 then p else (p.2, p.1))` |

**R3 · `split_ifs with hc`** changes the **goal list** and the **context**: a goal containing
`if c then a else b` becomes two goals, one with `hc : c` and `a`, one with `hc : ¬c` and `b`. It splits
every `if` with the same condition at once. Placeholders: `(c : Prop) [Decidable c] (a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (if c then a else b)` | `hc : c ⊢ P a`, `hc : ¬c ⊢ P b` |

**R4 · `simp only`** (no lemmas) changes the **goal**: it reduces projections of explicit pairs,
`(a, b).1 ↦ a`, `(a, b).2 ↦ b`. Do this before `linarith`, which treats `(a, b).1` as an unknown.
Placeholders: `(a b : ℝ) (P : ℝ → ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (a, b).1 (a, b).2` | `⊢ P a b` |

**R5 · `linarith`** **closes** a goal `t < s`, `t ≤ s`, `t = s` or `False` that follows from the hypotheses
by adding up linear inequalities. Terms that are not sums of numeral multiples (such as `(step p z).1` or
`f n`) are unknowns; `/ 3` of a linear term is fine. Placeholders: `(a b z : ℝ)`.

| Before | After |
|---|---|
| `h : a < b, hz : z < a ⊢ z < (a + 2 * b) / 3` | closed |

**R6 · `le_rfl`** **closes** `a ≤ a`. Statement: `le_rfl : a ≤ a`. Placeholders:
`{α : Type} [Preorder α] (a : α)`. In `step_spec` one endpoint does not move, so one nesting inequality is
`le_rfl`.

**R7 · `push Not at hc`** changes the **context**: it pushes `¬` inward, so `¬a < b` becomes `b ≤ a`, which
`linarith` can use (it cannot use `¬a < b`). Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `hc : ¬a < b ⊢ P` | `hc : b ≤ a ⊢ P` |

**W1** chains R2 → R3 → (R4, R5 or `push Not` R7) on `order`:

```lean-goal
⊢ (order p).1 ≤ (order p).2
⊢ (if p.1 ≤ p.2 then p else (p.2, p.1)).1 ≤ (if p.1 ≤ p.2 then p else (p.2, p.1)).2
⊢ (p.2, p.1).1 ≤ (p.2, p.1).2
```

## Part 3 · `I_lt` (milestone)

Statement: every interval `I f n` is nonempty, `(I f n).1 < (I f n).2`. Induction on `n`.

**R8 · `simp [T]`** **closes** a goal about index `0` of a recursive sequence: it unfolds `T 0` to the
base pair, reduces the projections and decides `0 < 2`. Placeholders: the toy `T : ℕ → ℝ × ℝ` with
`T 0 = (0, 2)`, `T (n + 1) = ((T n).1, (T n).2 / 2)`.

| Before | After |
|---|---|
| `⊢ (T 0).1 < (T 0).2` | closed |

**R9 · `simp only [T] at h`** changes the **context**: `T (n + 1)` inside `h` is unfolded one step, to the
`n + 1` equation of the definition. Without `at h` it acts on the goal. `exact` needs neither: `T (n + 1)`
*is* `((T n).1, (T n).2 / 2)` by definition, so a term of the unfolded type is accepted as is.
Placeholders: `(n : ℕ) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `h : P (T (n + 1)).2 ⊢ False` | `h : P ((T n).2 / 2) ⊢ False` |

**R10 · `h.1`, `h.2.1`, `h.2.2.1`, `h.2.2.2`** add a part of `h : A ∧ B ∧ C ∧ D` to the **context** (with
`have`) or use it directly. `∧` nests to the right (`A ∧ (B ∧ (C ∧ D))`), so `.2` is "the rest" and
`.2.2.1` is the third part. Placeholders: `(A B C D : Prop)`. In the exercise:
`(step_spec p z hp).1` is nonemptiness, `.2.1` and `.2.2.1` are the nesting, `.2.2.2` is "z is outside".

| Before | After |
|---|---|
| `h : A ∧ B ∧ C ∧ D ⊢ P` | `hc : C ⊢ P` |

**W2** proves `(J n).1 < (J n).2` for the halving sequence `J` by induction: `zero` is R8; in `succ`,
`simp only [J]` (R9 on the goal) and `linarith` with `ih` (R5).

## Part 4 · `left_le_right` (milestone)

Statement: every left end is below every right end, `(I f n).1 ≤ (I f m).2`, for all `n m`.

**R11 · `hm hab`** with `hm : Monotone g` adds `g a ≤ g b` to the **context**: `Monotone g` is a function
from `a ≤ b` to `g a ≤ g b`. For `ha : Antitone g`, `ha hab : g b ≤ g a`. Placeholders:
`(g : ℕ → ℝ) (a b : ℕ)`.

| Before | After |
|---|---|
| `hab : a ≤ b ⊢ P` | `hg : g a ≤ g b ⊢ P` |

**R12 · `monotone_nat_of_le_succ`** changes the **goal**: on `ℕ`, monotone follows from one step.
Statement: `(∀ n, g n ≤ g (n + 1)) → Monotone g`. Placeholders: `{α : Type} [Preorder α] (g : ℕ → α)`.
For `g := fun k => (I f k).1`, the step is a part of `step_spec` (R10).

| Before | After |
|---|---|
| `⊢ Monotone g` | `⊢ ∀ (n : ℕ), g n ≤ g (n + 1)` |

**R13 · `antitone_nat_of_succ_le`** changes the **goal**. Statement:
`(∀ n, g (n + 1) ≤ g n) → Antitone g`. Placeholders as in R12.

| Before | After |
|---|---|
| `⊢ Antitone g` | `⊢ ∀ (n : ℕ), g (n + 1) ≤ g n` |

**R14 · `le_max_left a b`, `le_max_right a b`** add facts to the **context**. Statements:
`a ≤ max a b`, `b ≤ max a b`. Placeholders: `{α : Type} [LinearOrder α] (a b : α)` (`ℕ` qualifies).

| Before | After |
|---|---|
| `⊢ P` | `h1 : a ≤ max a b, h2 : b ≤ max a b ⊢ P` |

**R15 · `hlt.le`** (`LT.lt.le`) adds `a ≤ b` to the **context** from `hlt : a < b`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `hlt : a < b ⊢ P` | `hle : a ≤ b ⊢ P` |

**R16 · `calc`** **closes** `a ≤ d` from a chain. Each line is `_ ≤ next := proof`, and `_` is the previous
right-hand side. Mixing `<` and `≤` is allowed (the result is `<` if any link is). Placeholders:
`(a b c d : ℝ)`. In the exercise: `(I f n).1 ≤ (I f (max n m)).1 ≤ (I f (max n m)).2 ≤ (I f m).2`, with
R11 + R14, then R15 on `I_lt`, then R11 + R14.

| Before | After |
|---|---|
| `h1 : a ≤ b, h2 : b ≤ c, h3 : c ≤ d ⊢ a ≤ d` | closed |

**W3** is R12 → `intro n` → R9 (on the goal) → R6 on `J`:

```lean-goal
⊢ Monotone fun n => (J n).1
⊢ ∀ (n : ℕ), (J n).1 ≤ (J (n + 1)).1
⊢ (J n).1 ≤ (J (n + 1)).1
⊢ (J n).1 ≤ (J n).1
```

## Part 5 · `real_uncountable`

Statement: `∃ x : ℝ, ∀ n, f n ≠ x`. The witness is `x := sSup (Set.range fun k => (I f k).1)`.

**R17 · `set x := e with hx`** changes the **context** and the **goal**: it adds `x : ℝ := e` and
`hx : x = e`, and replaces every `e` in the goal by `x`. Placeholders: `(g : ℕ → ℝ) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (sSup (Set.range g))` | `x : ℝ := sSup (Set.range g), hx : x = sSup (Set.range g) ⊢ P x` |

**R18 · `⟨k, rfl⟩`** proves `g k ∈ Set.range g`: a member of `Set.range g` is an index and an equation
`g k = y`. Placeholders: `(g : ℕ → ℝ) (k : ℕ)`. This is the `a ∈ s` argument of R21.

**R19 · `refine ⟨M, ?_⟩`** on `BddAbove s` changes the **goal**: you name the bound `M` and must show it is
one. Placeholders: `(s : Set ℝ) (M : ℝ)`. In the exercise, `M := (I f 0).2` works by `left_le_right`.
As a term: `⟨M, proof⟩`.

| Before | After |
|---|---|
| `⊢ BddAbove s` | `⊢ M ∈ upperBounds s` |

**R20 · `rintro _ ⟨k, rfl⟩`** changes the **goal** and the **context**: on `M ∈ upperBounds (Set.range g)`
(or `∀ y ∈ Set.range g, y ≤ M`) it introduces the element, takes its membership apart into an index `k`,
and substitutes `y := g k`. Placeholders: `(g : ℕ → ℝ) (M : ℝ)`.

| Before | After |
|---|---|
| `⊢ M ∈ upperBounds (Set.range g)` | `k : ℕ ⊢ g k ≤ M` |

**R21 · `le_csSup hb ha`** adds `a ≤ sSup s` to the **context**. Statement:
`le_csSup : BddAbove s → a ∈ s → a ≤ sSup s`. `cs` means *conditionally complete*: in `ℝ`, `sSup s` is the
least upper bound only when `s` is nonempty and bounded above, so the lemmas ask for those facts.
Placeholders: `(s : Set ℝ) (a : ℝ)`. In the exercise: `le_csSup hbdd ⟨k, rfl⟩ : (I f k).1 ≤ x`.

| Before | After |
|---|---|
| `hb : BddAbove s, ha : a ∈ s ⊢ P` | `hle : a ≤ sSup s ⊢ P` |

**R22 · `csSup_le`** changes the **goal list**. Statement:
`csSup_le : s.Nonempty → (∀ b ∈ s, b ≤ a) → sSup s ≤ a` ("a bound for every element bounds the least upper
bound"). `apply` leaves both premises as goals; pass the first directly as `csSup_le hne`.
Placeholders: `(s : Set ℝ) (a : ℝ)`. In the exercise: `x ≤ (I f k).2`, each `(I f j).1 ≤ (I f k).2` by
`left_le_right`.

| Before | After |
|---|---|
| `⊢ sSup s ≤ a` | `⊢ s.Nonempty`, `⊢ ∀ b ∈ s, b ≤ a` |

**R23 · `Set.range_nonempty g`** adds `(Set.range g).Nonempty` to the **context**: a sequence has a value.
Placeholders: `{α : Type} (g : ℕ → α)`.

| Before | After |
|---|---|
| `⊢ P` | `hne : (Set.range g).Nonempty ⊢ P` |

**R24 · `intro hn`** on `a ≠ b` changes the **context** and the **goal**: `a ≠ b` is `a = b → False`.
Placeholders: `(a b : ℝ)`. In a term, `fun n hn => ?_` does the same for `∀ n, f n ≠ x`. With the
contradictory inequalities in the context, `linarith` (R5) closes `False`.

| Before | After |
|---|---|
| `hab : a < b ⊢ a ≠ b` | `hn : a = b ⊢ False` |

**W4** is R22 with R23, then R20: `sSup (Set.range g) ≤ 1` from `∀ k, g k ≤ 1`:

```lean-goal
⊢ sSup (Set.range g) ≤ 1
⊢ ∀ b ∈ Set.range g, b ≤ 1
⊢ g k ≤ 1
```

The last move of the exercise: after R24, take `h1 := hlo (n + 1)`, `h2 := hhi (n + 1)`, unfold `I` one
step in both (R9), split `(step_spec (I f n) (f n) (I_lt f n)).2.2.2` (R10) with `rcases … with h | h`,
and each side is `linarith` with `hn : f n = x`.

---

## Traps

- The imports are frozen and `import` is BANNED: you get `ℝ`, its order and `sSup`, but no countability,
  measure theory or topology. Use only the entries here.
- `linarith` does not reduce `((u, v)).1`: run `simp only` (R4) first, or it reports failure on a goal that
  looks linear.
- `linarith` cannot use `¬a < b`: `push Not at hz` (R7) first.
- After `unfold step` the condition of the `if` appears in all three or four places at once; one
  `split_ifs with hz` splits them all.
- `simp only [I]` on `I f k` with a variable `k` does nothing: it unfolds only at `0` or `n + 1`. Specialise
  first (`hlo (n + 1)`), then unfold.
- `sSup` of an unbounded or empty set is a junk value: `le_csSup` needs `BddAbove`, `csSup_le` needs
  `Nonempty` (R23).
- `induction n with` needs one alternative per case, `| zero => …` and `| succ n ih => …`. In `succ`,
  `ih` is the statement for `n` and the goal is about `I f (n + 1)`, which `exact` reads as
  `step (I f n) (f n)` (R9).
- After `rintro _ ⟨k, rfl⟩` on `Set.range fun k => (I f k).1` the goal reads `(fun k => (I f k).1) k ≤ …`.
  That is just `(I f k).1 ≤ …`: `exact left_le_right …` works as is, and `simp only` tidies it.
- `f n ≠ x` is a function to `False`: introduce `hn : f n = x` (R24) and derive `False`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a pair-valued definition by cases | `if c then (a, b) else (a', b')` | R1 |
| unfold a definition in the goal | `unfold step` | R2 |
| split an `if` | `split_ifs with hz` | R3 |
| `(u, v).1 → u` | `simp only` | R4 |
| linear arithmetic over `ℝ` (also `False`) | `linarith` | R5 |
| `a ≤ a` | `le_rfl` | R6 |
| `¬a < b → b ≤ a` in a hypothesis | `push Not at hz` | R7 |
| base case of a recursive sequence | `simp [I]` | R8 |
| unfold one step of `I f (n + 1)` | `simp only [I] at h1 h2` | R9 |
| parts of `A ∧ B ∧ C ∧ D` | `h.1`, `h.2.1`, `h.2.2.1`, `h.2.2.2` | R10 |
| use `Monotone` / `Antitone` | `hm hab`, `ha hab` | R11 |
| monotone / antitone on `ℕ` from one step | `monotone_nat_of_le_succ`, `antitone_nat_of_succ_le` | R12, R13 |
| `n ≤ max n m`, `m ≤ max n m` | `le_max_left _ _`, `le_max_right _ _` | R14 |
| `<` to `≤` | `h.le` | R15 |
| chain inequalities | `calc a ≤ b := … _ ≤ c := …` | R16 |
| name the supremum | `set x := sSup (Set.range fun k => (I f k).1)` | R17 |
| `g k ∈ Set.range g` | `⟨k, rfl⟩` | R18 |
| prove `BddAbove (Set.range g)` | `⟨M, by rintro _ ⟨k, rfl⟩; …⟩` | R19, R20 |
| element `≤ sSup` | `le_csSup hbdd ⟨k, rfl⟩` | R21 |
| `sSup ≤` a bound | `csSup_le (Set.range_nonempty _) (by rintro _ ⟨j, rfl⟩; …)` | R22, R23, R20 |
| open `f n ≠ x` | `intro hn` / `fun n hn => ?_` | R24 |
| see the state | infoview | |
