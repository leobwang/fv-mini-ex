# M105 · Interval arithmetic: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): structures, `def`, `∧`, `refine`, `exact`, `·` focusing.
**New here:** Mathlib's real numbers `ℝ`, `min`/`max` and their order lemmas, the case split
`le_total`, and the arithmetic deciders `linarith` / `nlinarith`.

The guide works on its own structure `Seg` (fields `lo hi : ℝ`, membership `Seg.In x S`), which behaves
exactly like the exercise's `Ival` / `Ival.Mem`.

## How to read an entry

Each entry is one tactic or one lemma used with `refine`/`exact`/`simp`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`, or `P : Prop` for a whole goal). The step changes only
  the part inside `P (…)`.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[LinearOrder α]`
  is a requirement on `α` (a *type class*). `[Preorder α]`: `α` has a reflexive, transitive `≤`.
  `[LinearOrder α]`: moreover any two elements are comparable, which is what `min`/`max` need. `ℝ`, `ℚ`,
  `ℤ`, `ℕ` meet both.
- `exacts [p, q]` in the guide closes the open goals in order with `p`, then `q`; it only finishes an
  example, like `h`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (`Real`). Equality and `≤` on `ℝ` are not decidable, so `decide` is useless here |
| `I.lo`, `I.hi` | the fields `lo`, `hi` of the structure `I : Ival` (projections `Ival.lo I`, `Ival.hi I`) |
| `⟨a, b⟩` (expected type `Ival`) | the anonymous constructor `Ival.mk a b`: the interval with `lo = a`, `hi = b` |
| `I.add J`, `I.mul J` | dot notation for `Ival.add I J`, `Ival.mul I J` (`I : Ival`, so `I.add` means `Ival.add I`) |
| `(I.mul J).lo` | the field `lo` of the interval `I.mul J`; it unfolds (R3) to the `min` of four products |
| `Ival.Mem x I` | `I.lo ≤ x ∧ x ≤ I.hi`. It is a `def`, so R1/R2 see through it, but `simp`/`rw` patterns do not until you unfold it |
| `min a b`, `max a b` | the smaller / larger of `a`, `b` (any linear order) |
| `noncomputable def` | a definition Lean cannot compile to code; `min` on `ℝ` needs classical logic, so `Ival.mul` carries it. It changes nothing in proofs |
| `case inl`, `case inr` | the two goals of a case split on `A ∨ B` (left / right disjunct), R5 |
| `case refine_1`, `case refine_2` | the goals left by the `?_` holes of a `refine`, in order |
| `inst✝ : LinearOrder α` | the unnamed type-class assumption from `[LinearOrder α]` |

---

## Part 1 · `add_sound`

Statement: if `x ∈ I` and `y ∈ J` then `x + y ∈ I.add J`, i.e. `I.lo + J.lo ≤ x + y ∧ x + y ≤ I.hi + J.hi`.
Take the hypotheses apart (R1), split the goal (R2), unfold `Ival.add` (R3), add the bounds (R4).

**R1 · `obtain ⟨h1, h2⟩ := hx`** changes the **context**: `hx : A ∧ B` is replaced by its two halves. It
looks through a `def` whose body is a conjunction, so it works directly on `hx : Ival.Mem x I`.
Placeholders: `(x : ℝ) (S : Seg) (hx : Seg.In x S)`.

| Before | After |
|---|---|
| `hx : Seg.In x S ⊢ P` | `h1 : S.lo ≤ x, h2 : x ≤ S.hi ⊢ P` |

**R2 · `refine ⟨?_, ?_⟩`** changes the **goal list**: a goal `A ∧ B` becomes the two goals `A` and `B`. Like
R1 it looks through the `def`. `exact ⟨p, q⟩` is the same move when both proofs are ready.
Placeholders: `(x : ℝ) (S : Seg)`.

| Before | After |
|---|---|
| `⊢ Seg.In x S` | `⊢ S.lo ≤ x`, `⊢ x ≤ S.hi` |

**R3 · `simp only [Seg.shift]`** changes the **goal**: it replaces the defined name by its body
`⟨S.lo + c, S.hi + c⟩` and reduces the field access. In the exercise: `simp only [Ival.add]` turns
`(I.add J).lo` into `I.lo + J.lo`; `simp only [Ival.Mem, Ival.mul]` turns the whole `mul_sound` goal into
`min (min …) (min …) ≤ x * y ∧ x * y ≤ max (max …) (max …)`. Placeholders: `(S : Seg) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (S.shift c).lo` | `⊢ P (S.lo + c)` |

**R4 · `linarith`** **closes** a goal `t ≤ u`, `t < u` or `t = u` that is a nonnegative linear combination of
the hypotheses (it multiplies hypotheses only by constants, never by each other). Placeholders:
`(a c x y : ℝ)`.

| Before | After |
|---|---|
| `h1 : a ≤ x, h3 : c ≤ y ⊢ a + c ≤ x + y` | closed |

**W1** (negation `Seg.neg S = ⟨-S.hi, -S.lo⟩`, not the exercise's addition) runs R1, R2, then R3 and R4 in
each goal. After R2 the first goal is

```lean-goal
⊢ S.neg.lo ≤ -x
```

---

## Part 2 · `mul_sound`

Statement: if `x ∈ I` and `y ∈ J` then `x * y ∈ I.mul J`, whose endpoints are the `min` and `max` of the four
products `I.lo * J.lo`, `I.lo * J.hi`, `I.hi * J.lo`, `I.hi * J.hi`.

Idea: for fixed `y`, the map $t \mapsto t\,y$ is monotone (if $y \ge 0$) or antitone (if $y \le 0$). So for
$a \le x \le b$,
$$\min(a y, b y) \;\le\; x y \;\le\; \max(a y, b y).$$
Prove this once as a **milestone** lemma `between`, above `mul_sound`. Use it three times: in `x` (endpoints
`I.lo`, `I.hi`, factor `y`), then in `y` with factor `I.lo`, and in `y` with factor `I.hi`. The two last
calls bound `I.lo * y` and `I.hi * y` by endpoint products; chaining gives the result.

### Milestone `between`: sign split, then one product inequality per side

**R5 · `rcases le_total a b with h | h`** changes the **goal list and the context**. `le_total a b : a ≤ b ∨ b ≤ a`;
`rcases … with h | h` makes one goal per disjunct, each with its own `h`. For `between`, split on
`le_total 0 y`. Placeholders: `{α : Type} [LinearOrder α] (a b : α) (P : Prop)`.

| Before | After |
|---|---|
| `⊢ P` | `h : a ≤ b ⊢ P`, `h : b ≤ a ⊢ P` |

**R6 · `refine le_trans ?_ hbc`** changes the **goal**. `le_trans : a ≤ b → b ≤ c → a ≤ c`. Give the step
you have, keep `?_` for the other. `refine le_trans hab ?_` leaves `b ≤ c` instead. Placeholders:
`{α : Type} [Preorder α] (a b c : α)`.

| Before | After |
|---|---|
| `hbc : b ≤ c ⊢ a ≤ c` | `⊢ a ≤ b` |

**R7 · `min_le_left a b`, `min_le_right a b`** **close** the goal. Statements: `min a b ≤ a`,
`min a b ≤ b`. Write `_ _` for the arguments; Lean reads them off the goal. Placeholders:
`{α : Type} [LinearOrder α] (a b : α)`.

| Before | After |
|---|---|
| `⊢ min a b ≤ a` | closed by `exact min_le_left a b` |
| `⊢ min a b ≤ b` | closed by `exact min_le_right a b` |

**R8 · `le_max_left a b`, `le_max_right a b`** **close** the goal. Statements: `a ≤ max a b`,
`b ≤ max a b`. Placeholders as R7.

| Before | After |
|---|---|
| `⊢ a ≤ max a b` | closed by `exact le_max_left a b` |
| `⊢ b ≤ max a b` | closed by `exact le_max_right a b` |

**R9 · `nlinarith`** **closes** a goal that follows from the hypotheses and their pairwise **products**. It is
`linarith` (R4) plus products. Here it multiplies $0 \le x - a$ by $0 \le y$ (or by $0 \le -y$).
Placeholders: `(a x y : ℝ)`.

| Before | After |
|---|---|
| `h : a ≤ x, hy : 0 ≤ y ⊢ a * y ≤ x * y` | closed |
| `h : a ≤ x, hy : y ≤ 0 ⊢ x * y ≤ a * y` | closed (the inequality flips) |

So in the case `0 ≤ y` the lower bound of `between` is `min (a*y) (b*y) ≤ a*y ≤ x*y`: R6 with R7 for the first
step and R9 for the second; the upper bound is `x*y ≤ b*y ≤ max (a*y) (b*y)`: R6, R9, R8. In the case `y ≤ 0`
swap `left` and `right`. **W2** shows the pattern (`0 ≤ max y (-y)`).

### Main proof: instantiate, flip, chain

**R10 · `obtain ⟨k1, k2⟩ := addBoth p q r hpq`** changes the **context**: a lemma whose conclusion is
`A ∧ B`, applied to your own arguments, gives both halves. The arguments replace the lemma's variables in
order, so the roles can be swapped: `between J.lo J.hi y I.lo …` bounds `y * I.lo`. Placeholders: the guide
lemma `addBoth (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c ∧ c + a ≤ c + b` and `(p q r : ℝ) (hpq : p ≤ q)`.

| Before | After |
|---|---|
| `hpq : p ≤ q ⊢ P` | `k1 : p + r ≤ q + r, k2 : r + p ≤ r + q ⊢ P` |

**R11 · `simp only [mul_comm _ a] at h`** changes the **context**: every product `? * a` inside `h` becomes
`a * ?`. `mul_comm x y : x * y = y * x`; the `_` lets `simp` match any left factor, `a` fixes the right one.
Needed because `between J.lo J.hi y I.lo` speaks of `J.lo * I.lo` while `Ival.mul` has `I.lo * J.lo`. List
several hypotheses after `at`, and several lemmas in the brackets. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `h : c ≤ b * a ⊢ P c` | `h : c ≤ a * b ⊢ P c` |

**R12 · `refine le_min ?_ ?_`** changes the **goal list**. `le_min : a ≤ b → a ≤ c → a ≤ min b c`: to be
below a `min`, be below both. Placeholders: `{α : Type} [LinearOrder α] (a b c : α)`.

| Before | After |
|---|---|
| `⊢ a ≤ min b c` | `⊢ a ≤ b`, `⊢ a ≤ c` |

**R13 · `refine max_le ?_ ?_`** changes the **goal list**. `max_le : a ≤ c → b ≤ c → max a b ≤ c`: to be
above a `max`, be above both. Placeholders as R12.

| Before | After |
|---|---|
| `⊢ max a b ≤ c` | `⊢ a ≤ c`, `⊢ b ≤ c` |

How they combine in the lower bound of `mul_sound`: the goal `(I.mul J).lo ≤ x * y` goes through
`min (I.lo * y) (I.hi * y)` (R6 with the `x`-call of `between`); that `min` is above the big `min` by R12 on
`I.lo * y` and `I.hi * y`, each reached from one half of the big `min` (R6 with R7) and the corresponding
`y`-call. The upper bound is the mirror image with R13 and R8.

**W3: getting out of a nested `min`** (R6 twice, then R7):

```lean-goal
⊢ min (min a b) c ≤ t
⊢ min (min a b) c ≤ b
⊢ min a b ≤ b
```

**W4: getting into a nested `min`** (R12 twice), from `t ≤ min a (min b c)`:

```lean-goal
⊢ t ≤ min a (min b c)
⊢ t ≤ min b c
```

**W5: flip, then add** (R11 at two hypotheses, then R4):

| Before | After |
|---|---|
| `h1 : 0 ≤ u * s, h2 : u * s ≤ v * s ⊢ 0 ≤ s * v` | `h1 : 0 ≤ s * u, h2 : s * u ≤ s * v ⊢ 0 ≤ s * v` |

---

## Traps

- `linarith` does not multiply hypotheses together. Any goal with `x * y` where both are variables needs
  `nlinarith` (R9), and `nlinarith` needs the sign hypothesis (`0 ≤ y` or `y ≤ 0`) in the context: do R5 first.
- `linarith` and `nlinarith` treat `(I.add J).lo` or `(I.mul J).lo` as an unknown number: on
  `h1 : I.lo ≤ x, h3 : J.lo ≤ y ⊢ (I.add J).lo ≤ x + y` `linarith` fails. Unfold with
  `simp only [Ival.add]` (R3) first, which gives `⊢ I.lo + J.lo ≤ x + y`.
- `nlinarith` may time out if the context is big. Prove `between` as a separate lemma with only `a b x y`
  in scope, not inside `mul_sound`.
- `between` must be stated **above** `mul_sound` (Lean reads top to bottom), and outside the spec regions.
- `rw [mul_comm]` with no arguments rewrites the first product it finds, often the wrong one; give it
  arguments (`mul_comm _ I.lo`), or use `simp only [mul_comm _ I.lo] at …` to rewrite all matching products.
- `min_le_left _ _` closes a goal only if it is literally `min a b ≤ a`. If the goal is `(I.mul J).lo ≤ …`,
  `exact`/`refine` still see through it (definitional unfolding), but `rw`/`simp` patterns do not:
  unfold with `simp only [Ival.Mem, Ival.mul]` (R3) first if you want to see the `min`s.
- The order of the four products in `Ival.mul` is fixed: `min (min (lo*lo) (lo*hi)) (min (hi*lo) (hi*hi))`.
  Use `min_le_left` for the first half (`I.lo` products) and `min_le_right` for the second (`I.hi` products).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `hx : x ∈ I` | `obtain ⟨h1, h2⟩ := hx` | R1 |
| split a goal `A ∧ B` | `refine ⟨?_, ?_⟩` / `exact ⟨p, q⟩` | R2 |
| unfold `Ival.add`, `Ival.mul`, `Ival.Mem` | `simp only [Ival.add]` | R3 |
| linear arithmetic from hypotheses | `linarith` | R4 |
| case on the sign of `y` | `rcases le_total 0 y with hy \| hy` | R5 |
| go through a middle term | `refine le_trans ?_ h` / `le_trans h ?_` | R6 |
| `min a b ≤ a`, `min a b ≤ b` | `min_le_left _ _`, `min_le_right _ _` | R7 |
| `a ≤ max a b`, `b ≤ max a b` | `le_max_left _ _`, `le_max_right _ _` | R8 |
| `a * y ≤ x * y` from `a ≤ x`, `0 ≤ y` | `nlinarith` | R9 |
| use your lemma at chosen arguments | `obtain ⟨k1, k2⟩ := between a b x y h1 h2` | R10 |
| `J.lo * I.lo` → `I.lo * J.lo` in hypotheses | `simp only [mul_comm _ I.lo] at h` | R11 |
| below a `min` | `le_min h₁ h₂` | R12 |
| above a `max` | `max_le h₁ h₂` | R13 |
| see the state | infoview | |
