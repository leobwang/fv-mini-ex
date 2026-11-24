# H041 · Intermediate value theorem: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def`, `theorem`, `intro`, `exact`, `apply`, `have`,
`obtain`/`rcases` patterns, `refine`, `constructor`, `<;>`, `∃`/`∧`/`¬`, anonymous constructors `⟨_, _⟩`.
**New here:** Mathlib's real numbers `ℝ` with their order: closed intervals `Set.Icc`, set-builder sets
`{x | …}`, least upper bounds `sSup`, `BddAbove`, `Set.Nonempty`, absolute value `|·|`, `min`; the tactics
`set`, `by_contra`, `push Not`, `linarith`.

**The maths.** `ContAt f x` is the ε–δ definition: for every `ε > 0` there is `δ > 0` with
`|y - x| < δ → |f y - f x| < ε`. Let `S = {x ∈ [a, b] | f x ≤ 0}` and `c = sup S` (the least upper bound,
which exists in `ℝ` because `S` contains `a` and is bounded above by `b`: *completeness*).

1. *`c ∈ [a, b]`:* `a ∈ S` gives `a ≤ c`; every element of `S` is `≤ b` gives `c ≤ b`.
2. *`f c ≤ 0`:* suppose `f c > 0`. Take `ε = f c` and its `δ`. Since `c - δ < c = sup S`, some `s ∈ S` has
   `c - δ < s ≤ c`, so `|s - c| < δ` and `f s > f c - ε = 0`, contradicting `f s ≤ 0` (`s ∈ S`).
3. *`0 ≤ f c`:* suppose `f c < 0`. Then `c ≠ b` (else `f b < 0 ≤ f b`), so `c < b`. Take `ε = -f c` and its
   `δ`. The point `y = min (c + δ/2) b` has `c < y ≤ b` and `|y - c| < δ`, so `f y < f c + ε = 0`: `y ∈ S`,
   hence `y ≤ c`, contradicting `c < y`.
4. *Zero:* `f c ≤ 0` and `0 ≤ f c` give `f c = 0` (antisymmetry).

The guide never uses the exercise's `f`, `S` or `ContAt`; it uses placeholders, the toy definition
`EpsDelta`, the toy set `{x | x ∈ Set.Icc 0 2 ∧ x ≤ 1}` and a toy function `g`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`apply`/`obtain`. It says what changes
(**goal**, **context**, or **goal list**), gives the lemma's statement and its placeholders with their
types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change, plus, in a
  Before cell, the hypotheses the step uses; those stay in the context unless the After cell shows them changed
  under the same name (R10, R15, R18).
- `P` is "the rest of your goal" (`P : ℝ → Prop`), or the whole goal (`P : Prop`). A hypothesis `h` or `k`
  in an entry is only there to finish the example.
- All placeholders here are real numbers `(a b : ℝ)`, real sets `(s : Set ℝ)` or predicates
  `(p : ℝ → Prop)`; no type-class brackets are needed.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | the real numbers (Mathlib's `Real`) |
| `Set ℝ` | sets of reals; a set is a predicate, `x ∈ s` is a `Prop` |
| `Set.Icc a b` | the closed interval `[a, b] = {x \| a ≤ x ∧ x ≤ b}`; `x ∈ Set.Icc a b` *is* `a ≤ x ∧ x ≤ b` |
| `{x \| q x}` | the set of `x` with `q x`; `y ∈ {x \| q x}` *is* `q y` |
| `∃ c ∈ s, P c` | `∃ c, c ∈ s ∧ P c` |
| `∀ x ∈ s, P x` | `∀ x, x ∈ s → P x` |
| `∀ ε > 0, …`, `∃ δ > 0, …` | `∀ ε, ε > 0 → …`, `∃ δ, δ > 0 ∧ …` |
| `ε > 0`, `x ≥ y` | notation for `0 < ε`, `y ≤ x` (lemmas are stated with `<`, `≤`) |
| `\|a\|` | absolute value of `a : ℝ` |
| `min a b` | the smaller of `a` and `b` |
| `- -f c` | `-(-f c)`, i.e. `f c`: what `rw [abs_lt]` gives for `ε = -f c`; `linarith` reads it as is |
| `a ≠ b` | `a = b → False` |
| `this` | the name `have := …` gives a fact when you give none |
| `sSup s` | the least upper bound of `s : Set ℝ`. Mathlib defines it for every set (junk value `0` when `s` is empty or unbounded), so its lemmas ask for `s.Nonempty` and/or `BddAbove s` |
| `s.Nonempty` | `∃ x, x ∈ s` |
| `upperBounds s` | `{b \| ∀ ⦃x⦄, x ∈ s → x ≤ b}`: the set of upper bounds |
| `∀ ⦃x⦄, …` | a *strict-implicit* `∀`: `x` is not written; it is filled in once the next argument (`x ∈ s`) is given |
| `BddAbove s` | `(upperBounds s).Nonempty`: some upper bound exists |
| `csSup`, `cs` in a lemma name | *conditionally complete*: the `sSup` lemmas for `ℝ`, which need the side conditions above |
| `y : ℝ := e` | a local definition made by `set`: `y` is a name for `e` |
| `T : Set ℝ := ⋯` | the same, with the body hidden by the infoview |
| `∀ (y : ℝ), P y` | `∀ y, P y` with the type written out |
| `case refine_1`, `case h₁`, `case a`, `case left` | names of the goals a tactic produced (ignore them; work top to bottom) |

---

## Part 1 · `sup_bounds` (milestone)

Statement: if `a ∈ S` and every element of `S` is `≤ b`, then `a ≤ sSup S ≤ b`. This is the only place the
side conditions of `sSup` are built; Parts 2–4 reuse the same two constructions.

**R1 · `refine ⟨b, ?_⟩` on `BddAbove s`** changes the **goal**. `BddAbove s` unfolds to `∃ b, b ∈ upperBounds s`;
giving the bound leaves `b ∈ upperBounds s`, which unfolds to `∀ ⦃x⦄, x ∈ s → x ≤ b`, so a hypothesis
`h : ∀ x ∈ s, x ≤ b` closes it. As a term: `⟨b, h⟩ : BddAbove s`. Placeholders: `(s : Set ℝ) (b : ℝ)`.

| Before | After |
|---|---|
| `⊢ BddAbove s` | `⊢ b ∈ upperBounds s` |

**R2 · `refine ⟨a, ?_⟩` on `s.Nonempty`** changes the **goal**: `s.Nonempty` is `∃ x, x ∈ s`. As a term:
`⟨a, ha⟩ : s.Nonempty`. Placeholders: `(s : Set ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ s.Nonempty` | `⊢ a ∈ s` |

**R3 · `le_csSup`** changes the **context** (with `have`). Statement: `le_csSup : BddAbove s → a ∈ s → a ≤ sSup s`
(an element is below the least upper bound). Placeholders: `(s : Set ℝ) (a : ℝ)`, `hb : BddAbove s`, `ha : a ∈ s`.

| Before | After |
|---|---|
| `ha : a ∈ s ⊢ P` | `h1 : a ≤ sSup s ⊢ P` |

**R4 · `csSup_le`** changes the **goal list** (with `apply`). Statement:
`csSup_le : s.Nonempty → (∀ x ∈ s, x ≤ b) → sSup s ≤ b` (an upper bound is above the least one). As a term:
`csSup_le hs h`. Placeholders: `(s : Set ℝ) (b : ℝ)`. The bound variable prints as `b_1` to avoid a clash.

| Before | After |
|---|---|
| `⊢ sSup s ≤ b` | `⊢ s.Nonempty`, `⊢ ∀ b_1 ∈ s, b_1 ≤ b` |

---

## Part 2 · `f_sup_le` (milestone)

Statement: with `S = {x | x ∈ Set.Icc a b ∧ f x ≤ 0}`, `f (sSup S) ≤ 0` (step 2 of the maths).

### Naming the set and its supremum

**R5 · `set y := e`** changes the **context and the goal**: it adds the local definition `y : τ := e` and replaces
every `e` in the goal by `y`. Write `set S : Set ℝ := {x | …}` (type given) and then `set c := sSup S`. Placeholders:
`(g : ℝ → ℝ) (P : ℝ → Prop)`, with `e := g 0 + 1`.

| Before | After |
|---|---|
| `⊢ P (g 0 + 1)` | `y : ℝ := g 0 + 1 ⊢ P y` |

**R6 · `refine ⟨⟨?_, ?_⟩, ?_⟩` on `x ∈ {x | x ∈ Set.Icc a b ∧ p x}`** changes the **goal list**: membership in
the set is the nested conjunction `(a ≤ x ∧ x ≤ b) ∧ p x`, so the anonymous constructor splits it in three. As a
term: `⟨⟨h1, h2⟩, h3⟩`. Placeholders: `(a b x : ℝ) (p : ℝ → Prop)` (in the exercise `p x` is `f x ≤ 0`).

| Before | After |
|---|---|
| ⊢ x ∈ {x \| x ∈ Set.Icc a b ∧ p x} | `⊢ a ≤ x`, `⊢ x ≤ b`, `⊢ p x` |

The same goals as Lean prints them:

```lean-goal
⊢ x ∈ {x | x ∈ Set.Icc a b ∧ p x}
⊢ a ≤ x
⊢ x ≤ b
⊢ p x
```

**R7 · `le_rfl`** **closes** `a ≤ a` (reflexivity of `≤`). Use it for `a ≤ a` in `a ∈ Set.Icc a b`.
Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ≤ a` | closed |

**R8 · `hx.1.2`, `hx.2`** change the **context** (with `have`): `.1`/`.2` take the left/right side of an `∧`, and
Lean sees the `∧` inside `x ∈ {…}` and `x ∈ Set.Icc a b` without any rewriting. So `hx.1.2 : x ≤ b` and
`hx.2 : p x`. This also works when the set has a `set` name: `hsS.2 : f s ≤ 0` for `hsS : s ∈ S`. This is how
`fun x hx => hx.1.2` proves "every element of `S` is `≤ b`" for R1.
Placeholders: `(a b x : ℝ) (p : ℝ → Prop)`.

| Before | After `have hxb := hx.1.2` | After `have hpx := hx.2` |
|---|---|---|
| hx : x ∈ {x \| x ∈ Set.Icc a b ∧ p x} ⊢ P | `hxb : x ≤ b ⊢ P` | `hxb : x ≤ b, hpx : p x ⊢ P` |

### Proof by contradiction

**R9 · `by_contra h`** changes the **goal and the context**: the goal `G` becomes `False` and `h : ¬G` is added.
Placeholders: `(a b : ℝ)`, goal `a ≤ b`.

| Before | After |
|---|---|
| `⊢ a ≤ b` | `h : ¬a ≤ b ⊢ False` |

**R10 · `push Not at h`** changes the **context**: it pushes `¬` inward, and `¬a ≤ b` becomes `b < a` (on `ℝ`).
(`push_neg at h` is the older spelling of the same thing.) Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : ¬a ≤ b ⊢ P` | `h : b < a ⊢ P` |

### Using the ε–δ hypothesis

**R11 · `obtain ⟨δ, hδ, hd⟩ := hg e he`** changes the **context**. A hypothesis whose type is a definition with
body `∀ ε > 0, ∃ δ > 0, Q ε δ` (the toy `EpsDelta Q`; in the exercise `hf c : ContAt f c`) can be applied to `e`
and `he : e > 0` directly: Lean unfolds the definition. The pattern then takes the `∃ δ > 0, …` apart.
Placeholders: `(Q : ℝ → ℝ → Prop) (e : ℝ)`. In the exercise `Q ε δ` is `∀ y, |y - c| < δ → |f y - f c| < ε`.

| Before | After |
|---|---|
| `hg : EpsDelta Q, he : e > 0 ⊢ P` | `δ : ℝ, hδ : δ > 0, hd : Q e δ ⊢ P` |

**R12 · `sub_lt_self`** changes the **context**. Statement: `sub_lt_self a : 0 < b → a - b < a`.
Placeholders: `(a b : ℝ)`. In the exercise: `sub_lt_self c hδ : c - δ < c`, and `c` *is* `sSup S`.

| Before | After |
|---|---|
| `hb : 0 < b ⊢ P` | `hlt : a - b < a ⊢ P` |

**R13 · `exists_lt_of_lt_csSup`** changes the **context**. Statement:
`exists_lt_of_lt_csSup : s.Nonempty → b < sSup s → ∃ x ∈ s, b < x` (below the least upper bound there is an element
of `s` above you: this is where completeness does the work). Placeholders: `(s : Set ℝ) (b : ℝ)`.

| Before | After |
|---|---|
| `hs : s.Nonempty, hb : b < sSup s ⊢ P` | `x : ℝ, hxs : x ∈ s, hbx : b < x ⊢ P` |

**R14 · `rw [abs_lt]`** changes the **goal**. Statement: `abs_lt : |a| < b ↔ -b < a ∧ a < b`. Use it to prove the
`|y - c| < δ` that `hd` asks for: `hd y (by rw [abs_lt]; constructor <;> linarith)`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| ⊢ \|a\| < b | `⊢ -b < a ∧ a < b` |

```lean-goal
⊢ |a| < b
⊢ -b < a ∧ a < b
```

**R15 · `rw [abs_lt] at h`** changes the **context**: the same lemma, applied to the `|f y - f c| < ε` you get back.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| h : \|a\| < b ⊢ P | `h : -b < a ∧ a < b ⊢ P` |

**R16 · `linarith`** **closes** a goal `t < u`, `t ≤ u`, `t = u` or `False` that follows from the hypotheses by
adding up linear (in)equalities with rational coefficients. It reads both sides of an `∧` hypothesis (so R15's
result needs no splitting) and treats `f c`, `f s`, `δ / 2` as unknowns. `linarith [t₁, t₂]` also uses the
proofs `tᵢ`, e.g. `linarith [hsS.2]` adds `f s ≤ 0`. Placeholders: `(x y e : ℝ)`.

| Before | After |
|---|---|
| `h : -e < x - y ∧ x - y < e, hy : y ≤ 0 ⊢ x < e` | closed |

---

## Part 3 · `f_sup_ge` (milestone)

Statement: with `S` as in Part 2 and also `0 ≤ f b`, `0 ≤ f (sSup S)` (step 3 of the maths). Start as in Part 2
(R5, R6, R7, R8, R9, R10, R11), and use `sup_bounds` for `c ≤ b`. New are R17–R21.

**R17 · `lt_of_le_of_ne`** changes the **goal**. Statement: `lt_of_le_of_ne : a ≤ b → a ≠ b → a < b`. `a ≠ b` is
`a = b → False`, so give it as `fun h => …`. Placeholders: `(a b : ℝ)`.

| Before | After `refine lt_of_le_of_ne h1 (fun h => ?_)` |
|---|---|
| `h1 : a ≤ b ⊢ a < b` | `h : a = b ⊢ False` |

**R18 · `rw [h] at h'`** changes the **context**: with `h : a = b`, every `a` in `h'` becomes `b`. In the exercise:
`h : c = b` turns `hneg : f c < 0` into `f b < 0`, which contradicts `hb` by `linarith`. Placeholders:
`(a b : ℝ) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `h' : P a ⊢ False` | `h' : P b ⊢ False` |

**R19 · `lt_min`** changes the **goal list**. Statement: `lt_min : a < b → a < c → a < min b c`. As a term:
`lt_min h1 h2`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `⊢ a < min b c` | `⊢ a < b`, `⊢ a < c` |

**R20 · `min_le_left`** changes the **context**. Statement: `min_le_left a b : min a b ≤ a`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P` | `h : min a b ≤ a ⊢ P` |

**R21 · `min_le_right`** changes the **context**. Statement: `min_le_right a b : min a b ≤ b`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ P` | `h : min a b ≤ b ⊢ P` |

---

## Part 4 · `ivt`

Statement: `∃ c ∈ Set.Icc a b, f c = 0`. Only assembly: `sup_bounds` gives `c ∈ [a, b]`, `f_sup_le` and
`f_sup_ge` give the two inequalities.

**R22 · `le_antisymm`** changes the **goal list**. Statement: `le_antisymm : a ≤ b → b ≤ a → a = b`. As a term:
`le_antisymm h1 h2`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ a = b` | `⊢ a ≤ b`, `⊢ b ≤ a` |

**R23 · `refine ⟨x, ⟨?_, ?_⟩, ?_⟩` on `∃ c ∈ Set.Icc a b, P c`** changes the **goal list**: the witness, then the
two halves of `x ∈ Set.Icc a b`, then `P x`. Placeholders: `(a b x : ℝ) (P : ℝ → Prop)`.
You may write `_` instead of the witness `x` only when a part given *as a term in the same `refine`* mentions it:
with `h1 : a ≤ x`, `refine ⟨_, ⟨h1, h2⟩, ?_⟩` works, but `refine ⟨_, ⟨?_, ?_⟩, ?_⟩` is an error
(`don't know how to synthesize placeholder`). In `ivt` that is how you avoid typing out `sSup {…}`.

| Before | After `refine ⟨x, ⟨?_, ?_⟩, ?_⟩` | After `refine ⟨_, ⟨h1, h2⟩, ?_⟩` |
|---|---|---|
| `⊢ ∃ c ∈ Set.Icc a b, P c` | `⊢ a ≤ x`, `⊢ x ≤ b`, `⊢ P x` | `⊢ P x` |

---

## Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: both bounds on a toy `sSup`** (R5, R6–R8, R1–R4). `set` names the set, and both bounds come out as terms:

```lean-goal
⊢ 0 ≤ sSup {x | x ∈ Set.Icc 0 2 ∧ x ≤ 1} ∧ sSup {x | x ∈ Set.Icc 0 2 ∧ x ≤ 1} ≤ 2
⊢ 0 ≤ sSup T ∧ sSup T ≤ 2
⊢ 0 ≤ sSup T
⊢ sSup T ≤ 2
```

**W2: one use of an ε–δ bound** (R14, R15, R16), for a toy `g` with `ε = 1`. `hd u (by rw [abs_lt]; constructor <;> linarith)`
gives `|g u - g t| < 1`; R15 splits it; `linarith` finishes:

```lean-goal
⊢ g t - 1 < g u
```

**W3: a point to the right of `t`, but not past `5`** (R5, R19, R21): `set y := min (t + δ / 2) 5`, then
`lt_min (by linarith) ht : t < y` and `min_le_right _ _ : y ≤ 5`.

```lean-goal
⊢ t < min (t + δ / 2) 5 ∧ min (t + δ / 2) 5 ≤ 5
⊢ t < y ∧ y ≤ 5
```

---

## Traps

- Mathlib's `Continuous`, filters, `fun_prop` and every IVT variant are **BANNED**: continuity is only the
  exercise's `ContAt`, used through R11. The long BANNED list closes bridges; R1–R23 are all you need.
- `sSup` is defined for every set, so `le_csSup`, `csSup_le`, `exists_lt_of_lt_csSup` each demand their side
  condition (`BddAbove S`, `S.Nonempty`). Build them once with R1, R2 and keep them as `have`s.
- `rintro rfl` (or `subst`) fails on a `set` variable such as `c`: it is a local definition, not a free variable.
  Prove `c < b` with `lt_of_le_of_ne` and `fun h => …` (R17), and use `rw [h] at …` (R18).
- After `set c := sSup S`, the goal and hypotheses show `c`, but R12/R13 need `b < sSup S`: `c - δ < c` *is* that,
  since `c` unfolds to `sSup S`.
- `hd y` needs `|y - c| < δ`, not `|c - y| < δ`: the order inside `|·|` is fixed by the definition.
- In the right-hand case the point must stay in `[a, b]`: `c + δ / 2` may exceed `b`, hence `min (c + δ / 2) b`.
- A `have h : T := by` proof must be indented further than `have`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `BddAbove S` from `∀ x ∈ S, x ≤ b` | `⟨b, h⟩` | R1 |
| `S.Nonempty` from `a ∈ S` | `⟨a, ha⟩` | R2 |
| `a ≤ sSup S` | `le_csSup hbdd ha` | R3 |
| `sSup S ≤ b` | `csSup_le hne h` | R4 |
| name `sSup S` | `set c := sSup S` | R5 |
| `x ∈ {x \| x ∈ Set.Icc a b ∧ p x}` | `⟨⟨h1, h2⟩, h3⟩` | R6 |
| `a ≤ a` | `le_rfl` | R7 |
| parts of a membership | `hx.1.1`, `hx.1.2`, `hx.2` | R8 |
| contradiction, `¬ ≤` → `<` | `by_contra h; push Not at h` | R9, R10 |
| a δ for a given ε | `obtain ⟨δ, hδ, hd⟩ := hf c ε hε` | R11 |
| `c - δ < c` | `sub_lt_self c hδ` | R12 |
| an element of `S` above `b < sSup S` | `obtain ⟨s, hsS, hs⟩ := exists_lt_of_lt_csSup hne hlt` | R13 |
| prove / use `\|t\| < e` | `rw [abs_lt]` / `rw [abs_lt] at h` | R14, R15 |
| linear arithmetic | `linarith [extra facts]` | R16 |
| `a < b` from `a ≤ b` and `a ≠ b` | `lt_of_le_of_ne h (fun h' => …)` | R17 |
| substitute in a hypothesis | `rw [h] at h'` | R18 |
| `a < min b c` | `lt_min h1 h2` | R19 |
| `min a b ≤ a`, `min a b ≤ b` | `min_le_left _ _`, `min_le_right _ _` | R20, R21 |
| `a = b` from `≤` both ways | `le_antisymm h1 h2` | R22 |
| `∃ c ∈ Set.Icc a b, P c` | `⟨_, ⟨h1, h2⟩, h3⟩` | R23 |
| see the state | infoview | |
