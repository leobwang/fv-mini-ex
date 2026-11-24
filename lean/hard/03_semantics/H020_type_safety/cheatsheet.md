# H020 · Type safety: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033: `intro`, `exact`, `cases`/`rcases`/`obtain` on `∨` and `∃`,
`refine`, `<;>`, anonymous constructors `⟨_, _⟩`, `rfl`). **New here:** inductive *relations* (`HasType`,
`Value`, `Step` are `Prop`-valued inductive families), induction on a *derivation* (a proof of such a
relation), *inversion* with `cases`, canonical-forms lemmas, and the progress + preservation recipe for type
safety. No Mathlib: everything is core Lean.

## How to read an entry

Each entry is one tactic or one proof term. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P`, `G` are "the rest of your goal". The step changes only the part shown inside `P (…)`.
- The guide does not use the exercise's objects. It uses a toy language with the same shape:

  | Toy (guide) | Exercise | Role |
  |---|---|---|
  | `Kd` with `num`, `flag` | `Ty` with `nat`, `bool` | types |
  | `Ex` with `k n`, `on`, `off`, `add a b`, `pos a` | `Tm` with `lit n`, `tt`, `ff`, `plus a b`, `isZero t` (and `ite c t e`) | syntax |
  | `Ok e K` | `HasType t T` | the typing relation; a proof is a derivation tree |
  | `Done e` (rules `k`, `on`, `off`) | `Value t` (rules `lit`, `tt`, `ff`) | values |
  | `Red e e'` (`addK`, `addL`, `posZ`, `posS`, `posC`) | `Step t t'` (`plusLit`, `plusL`, `plusR`, `isZeroZ`, `isZeroS`, `isZeroC`, `ite…`) | one step |

- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `HasType t T` | the term `t` has type `T`: there is a derivation built from the rules of `HasType` |
| `Value t` | `t` is a literal, `tt` or `ff` (a finished result) |
| `Step t t'` | `t` reduces to `t'` in one step (call-by-value, left to right) |
| `Ty.nat`, `Tm.lit n`, `Tm.tt` | constructors with their namespace; in source you may write `.nat`, `.lit n`, `.tt` when the type is known |
| `a✝.plus b✝`, `(Tm.lit n).isZero`, `c✝.ite t✝ e✝` | `Tm.plus a✝ b✝`, `Tm.isZero (Tm.lit n)`, `Tm.ite c✝ t✝ e✝`: Lean prints a constructor applied to its first argument with dot notation |
| `.plusL sa`, `.lit` | a rule used as a proof (`Step.plusL sa`, `HasType.lit`); Lean reads the namespace off the expected type (R4) |
| `a✝`, `n✝`, `T✝` | an *inaccessible* name: Lean made it, you cannot type it. Name it with `with \| rule x y =>` |
| `a✝¹`, `a✝²`, `c'✝` | more inaccessible names: the superscript only tells apart several hidden `a`s; `c'✝` is a hidden `c'` |
| `a_ih✝` | an induction hypothesis Lean made (R5) |
| `∀ {T : Ty}, HasType c✝ T → …` in an IH | the IH holds at every type; Lean fills in `T` when you apply it (R12, R15) |
| `case plus`, `case isZero.inl` | the goal for the `plus` rule; the `isZero` rule, then the left side of an `rcases` |

---

## Part 1 · `canonical_nat` (milestone 1, used in progress `plus` and `isZero`)

Statement: a value `v` of type `nat` is a literal, `∃ n, v = .lit n`. Split on the value (R1). The `lit` case
is `⟨_, rfl⟩` (R2); in the `tt` and `ff` cases `h : HasType Tm.tt Ty.nat` cannot be derived (R3).

**R1 · `cases hv`** with `hv : Done e` changes the **goal list**: one goal per rule of `Done`, and in each
`e` is replaced by that rule's conclusion. Write `cases hv with | k => … | on => … | off => …`.
Placeholders: `{e : Ex}`, `(P : Ex → Prop)`, `(hv : Done e)`.

| Before | After |
|---|---|
| `hv : Done e ⊢ P e` | `n✝ : Nat ⊢ P (Ex.k n✝)`, `⊢ P Ex.on`, `⊢ P Ex.off` |

In `canonical_nat` the `tt` case is `h : HasType Tm.tt Ty.nat ⊢ ∃ n, Tm.tt = Tm.lit n`: `h` was rewritten too.

**R2 · `exact ⟨_, rfl⟩`** **closes** `∃ n, a = b` when the two sides agree for some `n`; Lean finds the
witness `_` while checking `rfl`. Placeholders: `(m : Nat)`.

| Before | After |
|---|---|
| `⊢ ∃ n, Ex.k m = Ex.k n` | no goals |

**R3 · `cases h`** where no rule can produce `h` **closes** the goal. `cases` keeps only the rules whose
conclusion can match `h`'s indices; here none can, so no goal is left. Placeholders: `(G : Prop)`,
`(h : Ok .on .num)`.

| Before | After |
|---|---|
| `h : Ok Ex.on Kd.num ⊢ G` | no goals |

## Part 2 · `canonical_bool` (milestone 2, used in progress `ite`)

Statement: a value of type `bool` is `.tt` or `.ff`. Same shape as Part 1: R1, then R3 in the `lit` case, and
R4 with `rfl` (`Or.inl rfl`, `Or.inr rfl`) in the other two.

**R4 · `exact Or.inl x`** (or `Or.inr x`) **closes** `A ∨ B` with a proof of one side. A rule is a function
from its premises to its conclusion; `Done.k : Done (.k n)` has no premises, so `.k` alone proves
`Done (.k n)`. The leading dot means "look the name up in the namespace of the expected type". Placeholders:
`(n : Nat) (B : Prop)`.

| Before | After |
|---|---|
| `⊢ Done (Ex.k n) ∨ B` | no goals |

---

## Part 3 · `progress`

Statement: `HasType t T → Value t ∨ ∃ t', Step t t'`. Induction on the typing derivation `h` (R5). Leaves
(`lit`, `tt`, `ff`) are values (R4). Every compound rule steps, so go `right` (R6) and split the IH of the
leftmost subterm (R7; the value goal comes first, then the step goal): if it is a value, move to the next
subterm (`plus`) or use a canonical-forms lemma (R8, R10) and the matching computation rule (R9); if it steps,
the congruence rule steps (R9). In `isZero` the
literal `n` must be split into `0` and `n + 1` first (R11).

**R5 · `induction h`** with `h : Ok e K` changes the **goal list**: one goal per rule of `Ok`, with the
rule's premises as hypotheses and one IH per premise that is itself an `Ok`. With
`induction h with | add ha hb iha ihb => …` you name the explicit premises first, then the IHs; the implicit
`{a b}` stay `a✝ b✝`. Placeholders: `{e : Ex} {K : Kd}`, `(P : Ex → Kd → Prop)`, `(h : Ok e K)`.

| Before | After (one goal per rule) |
|---|---|
| `h : Ok e K ⊢ P e K` | `n✝ : Nat ⊢ P (Ex.k n✝) Kd.num` |
| | `⊢ P Ex.on Kd.flag`, `⊢ P Ex.off Kd.flag` |
| | `a✝¹ : Ok a✝² Kd.num, a✝ : Ok b✝ Kd.num, a_ih✝¹ : P a✝² Kd.num, a_ih✝ : P b✝ Kd.num ⊢ P (a✝².add b✝) Kd.num` |
| | `a✝ : Ok a✝¹ Kd.num, a_ih✝ : P a✝¹ Kd.num ⊢ P a✝¹.pos Kd.flag` |

In `progress`, `| plus ha hb iha ihb =>` gives `iha : Value a✝ ∨ ∃ t', Step a✝ t'` and
`ihb : Value b✝ ∨ ∃ t', Step b✝ t'`, with goal `Value (a✝.plus b✝) ∨ ∃ t', Step (a✝.plus b✝) t'`.

**R6 · `right`** changes the **goal**: `A ∨ B` becomes `B` (`left` gives `A`). Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∨ B` | `⊢ B` |

**R7 · `rcases ih with hv | ⟨a', st⟩`** changes the **goal list and the context**: one goal per side of `∨`,
and the `∃` is opened into a witness and its proof. Placeholders: `{a : Ex}`, `(G : Prop)`,
`(ih : Done a ∨ ∃ a', Red a a')`.

| Before | After |
|---|---|
| `⊢ G` (with `ih : Done a ∨ ∃ a', Red a a'`) | `hv : Done a ⊢ G`, `a' : Ex, st : Red a a' ⊢ G` |

**R8 · `obtain ⟨n, rfl⟩ := hc`** with `hc : ∃ n, e = Ex.k n` changes the **context and goal**: the `rfl`
pattern substitutes the equation, so `e` becomes `Ex.k n` in the goal and in every hypothesis. `e` must be a
local variable (it is: `a✝` from R5). Use it as `obtain ⟨n, rfl⟩ := canonical_nat ha va`.
Placeholders: `{e : Ex}`, `(P : Ex → Prop)`.

| Before | After |
|---|---|
| `⊢ P e` (with `hc : ∃ n, e = Ex.k n`) | `n : Nat ⊢ P (Ex.k n)` |

**R9 · `exact ⟨_, .addK⟩`** **closes** `∃ e', Red e e'`: the rule proves the `Red`, and the witness `_` is
read off the rule's conclusion. The rule must match the term *literally* (up to computation): `.addK` needs
both sides to be `Ex.k _` already, which is why R8 comes first. Congruence rules take the inner step:
`⟨_, .plusL sa⟩`, `⟨_, .plusR va sb⟩`. Placeholders: `(n m : Nat)`.

| Before | After |
|---|---|
| `⊢ ∃ e', Red ((Ex.k n).add (Ex.k m)) e'` | no goals |

**R10 · `rcases hc with rfl | rfl`** with `hc : e = Ex.on ∨ e = Ex.off` changes the **goal list**: two goals,
with `e` replaced by each constructor. Use it as `rcases canonical_bool hc vc with rfl | rfl`, so that `.iteT`
and `.iteF` match. Placeholders: `{e : Ex}`, `(P : Ex → Prop)`.

| Before | After |
|---|---|
| `hc : e = Ex.on ∨ e = Ex.off ⊢ P e` | `⊢ P Ex.on`, `⊢ P Ex.off` |

**R11 · `cases n`** on a `Nat` inside a term changes the **goal list**: one goal with `0`, one with `n✝ + 1`.
A rule stated for `k 0` or `k (n + 1)` (in the exercise `isZeroZ`, `isZeroS`) only matches after this split.
Write `cases n with | zero => … | succ n => …` to name the new `n`. Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `⊢ ∃ e', Red (Ex.k n).pos e'` | `⊢ ∃ e', Red (Ex.k 0).pos e'`, `n✝ : Nat ⊢ ∃ e', Red (Ex.k (n✝ + 1)).pos e'` |

In `progress`, after R8 the `isZero` goal is `∃ t', Step (Tm.lit n).isZero t'`.

---

## Part 4 · `preservation`

Statement: `HasType t T → Step t t' → HasType t' T`. Induct on the **step** `hs`, generalizing `T` (R12): in a
congruence case the IH is needed at the type of the subterm (`c✝` has type `Ty.bool` inside an `ite` of type `T`). In each
case invert `h` (R13, R14) to get the typings of the parts, then rebuild with a rule (R15).

**R12 · `induction hs generalizing K`** changes the **goal list**: one goal per rule of `Red`. `h : Ok e K`
mentions the index `e`, so Lean carries `h` into each goal (rewritten to that rule's term); `generalizing K`
makes each IH read `a_ih✝ : ∀ {K : Kd}, Ok a✝¹ K → P a'✝ K`, usable at any kind. Placeholders:
`{e e' : Ex} {K : Kd}`, `(P : Ex → Kd → Prop)`, `(h : Ok e K)`, `(hs : Red e e')`.

| Before | After (three of the five goals) |
|---|---|
| `h : Ok e K, hs : Red e e' ⊢ P e' K` | `h : Ok ((Ex.k n✝).add (Ex.k m✝)) K ⊢ P (Ex.k (n✝ * m✝)) K` |
| | `h : Ok (a✝¹.add b✝) K ⊢ P (a'✝.add b✝) K` (with the IH above) |
| | `h : Ok (Ex.k 0).pos K ⊢ P Ex.off K` |

In `preservation` the `iteC` goal is `h : HasType (c✝.ite t✝ e✝) T ⊢ HasType (c'✝.ite t✝ e✝) T` with
`ih : ∀ {T : Ty}, HasType c✝ T → HasType c'✝ T`.

**R13 · `cases h`** (inversion) with `h : Ok (.add a b) K` changes the **context and goal**: `h` is replaced
by the premises of the only rule that concludes `Ok (.add …) _`, and the index `K` is unified with that
rule's kind `.num` everywhere. Name the premises: `cases h with | add ha hb => …`. Placeholders:
`{a b : Ex} {K : Kd}`, `(P : Kd → Prop)`.

| Before | After |
|---|---|
| `h : Ok (a.add b) K ⊢ P K` | `a✝¹ : Ok a Kd.num, a✝ : Ok b Kd.num ⊢ P Kd.num` |

For the `ite` rule the type index stays a variable: `cases h with | ite hc ht he => …` gives `ht : HasType t✝ T`.

**R14 · `cases h`** with `h : Ok (.k n) K` (a rule with no premises) changes the **context and goal**: `h`
disappears and `K` becomes `.num`. Then the goal is a rule: `exact .k`. Placeholders: `{n m : Nat} {K : Kd}`.

| Before | After |
|---|---|
| `h : Ok (Ex.k n) K ⊢ Ok (Ex.k m) K` | `⊢ Ok (Ex.k m) Kd.num` |

**R15 · `exact .add (ih ha) hb`** **closes** the goal: the rule `.add` applied to the IH, whose implicit `{K}`
Lean finds from `ha`. Placeholders: `{a a' b : Ex}`, `(ih : ∀ {K : Kd}, Ok a K → Ok a' K)`.

| Before | After |
|---|---|
| `ha : Ok a Kd.num, hb : Ok b Kd.num ⊢ Ok (a'.add b) Kd.num` | no goals |

**W3** in the guide is the whole pattern on the toy language (R12, then R13/R14 and R15 in each case).

---

## Part 5 · `type_unique`

Statement: `HasType t T1 → HasType t T2 → T1 = T2`. Induct on `h1` (R5), generalizing `T2` (as in R12) so that
the IHs read `∀ {T2 : Ty}, HasType t✝ T2 → T✝ = T2`. In every case invert `h2` (R13, R14): for the leaves and
for `plus`, `isZero` this fixes `T2` and the goal becomes `Ty.nat = Ty.nat` or `Ty.bool = Ty.bool` (`rfl`).
For `ite` the goal is `T✝ = T2` with `h2 : HasType (c✝.ite t✝ e✝) T2`; inversion gives a typing of the
then-branch at `T2`, and the then-branch IH finishes.

---

## Traps

- In `preservation`, induct on the step `hs`, not on `h`: the cases you need are the step rules.
- Forgetting `generalizing T` (preservation) or `generalizing T2` (type_unique) fixes the IH at one type; in
  the `iteC` case you need it at `Ty.bool`, in the `ite` case at `T2`.
- `exact ⟨_, .plusLit⟩` fails until both summands are literally `Tm.lit _`: run `canonical_nat` with
  `obtain ⟨n, rfl⟩` (R8) on both first. Likewise `.isZeroS` needs `Tm.lit (n + 1)`: `cases n` (R11).
- `.plusR` needs a `Value` of the left summand; if the left summand steps, use `.plusL` whatever the right does.
- `cases h` must come after the step case has fixed the shape of `t`; on `h : HasType t T` with `t` a variable it
  produces all six rules.
- The `ite` typing rule keeps the type `T` as a variable, so `cases h` there does not fix `T`; the branches carry it.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split a value into its shapes | `cases hv with \| lit => … \| tt => … \| ff => …` | R1 |
| `∃ n, Tm.lit m = Tm.lit n` | `exact ⟨_, rfl⟩` | R2 |
| impossible typing such as `HasType Tm.tt Ty.nat` | `cases h` | R3 |
| prove one side of `∨` | `exact Or.inl rfl`, `exact Or.inl .lit` | R4 |
| induct on a typing derivation | `induction h with \| plus ha hb iha ihb => … \| …` | R5 |
| choose the right disjunct | `right` / `left` | R6 |
| value or steps? | `rcases iha with va \| ⟨a', sa⟩` | R7 |
| value of type nat → literal | `obtain ⟨n, rfl⟩ := canonical_nat ha va` | R8 |
| produce a step | `exact ⟨_, .plusLit⟩`, `⟨_, .plusL sa⟩`, `⟨_, .plusR va sb⟩` | R9 |
| value of type bool → `tt` / `ff` | `rcases canonical_bool hc vc with rfl \| rfl` | R10 |
| literal `0` vs `n + 1` | `cases n with \| zero => … \| succ n => …` | R11 |
| induct on the step, IH at any type | `induction hs generalizing T with \| plusL _ ih => … \| …` | R12 |
| invert a typing | `cases h with \| plus ha hb => …` | R13 |
| invert a leaf typing (fixes the type) | `cases h; exact .lit` | R14 |
| rebuild with the IH | `exact .plus (ih ha) hb` | R15 |
| uniqueness: same as R12 on `h1` | `induction h1 generalizing T2`, then `cases h2` | R5, R12, R13 |
| see the state | infoview | |
