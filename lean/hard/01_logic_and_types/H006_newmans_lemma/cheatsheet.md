# H006 · Newman's lemma: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `inductive`, `def`, `theorem`, `intro`, `exact`, `have`,
`rw`, `cases`/`induction` on `Nat`, `∃`/`∧`/`¬`. **New here:** induction and case analysis on a
*derivation* of an inductive relation (`Star R a b`), well-founded induction (`WellFounded.induction`,
core Lean), naming inaccessible variables, `first`, `nomatch`, `absurd`, `subst`, and case analysis on a
concrete finite relation. Core Lean only: no Mathlib.

**The maths.** Write `a → b` for `R a b` and `a →* b` for `Star R a b` (zero or more steps). `b, c` are
*joinable* if `b →* d` and `c →* d` for some `d`. `R` is *locally confluent* if any two ONE-step reducts
`a → b`, `a → c` are joinable; *confluent* if any two MANY-step reducts are. `R` *terminates* if there is no
infinite chain `a₀ → a₁ → a₂ → …`. Newman: terminating + locally confluent ⇒ confluent. Proof by
well-founded induction on the peak `a`, assuming the claim for every one-step reduct of `a`:

```
          a
        ↙   ↘
      b1     c1        local confluence joins b1, c1 at d
     ↙  ↘   ↙  ↘
    b    d      c      IH at b1 joins b, d at e
     ↘  ↙      ↙       IH at c1 joins e (c1 →* d →* e) and c at f
      e       ↙
       ↘    ↙
         f
```

The guide never uses the exercise's `Star`, `P`, `R4`. It uses toy objects:

```lean
inductive EvenPath {α : Type} (r : α → α → Prop) : α → α → Prop   -- a reaches b in an EVEN number of steps
  | nil (a : α) : EvenPath r a a
  | two {a b c d : α} : r a b → r b c → EvenPath r c d → EvenPath r a d
def Always {α : Type} (Q : α → Prop) : Prop := ∀ x, Q x
def Both {α : Type} (Q Q' : α → Prop) : Prop := ∃ z, Q z ∧ Q' z
inductive Col where | red | green | blue | white
inductive Next : Col → Col → Prop                -- a diamond: red → green, red → blue, green → white, blue → white
  | rg : Next .red .green | rb : Next .red .blue | gw : Next .green .white | bw : Next .blue .white
```

## How to read an entry

Each entry is one tactic or one term-building move. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P`, `Q`, `C` are "the rest of your goal": predicates such as `Q : α → Prop` or `P : α → α → Prop`.
  (In the entries `P` is such a predicate, never the exercise's point type `P` with `pa pb pc pd`.)
- Placeholders are written as Lean binders: `{α : Type}` is any type; `(r : α → α → Prop)` is a binary
  relation; `(A G : Prop)` are propositions; `(p : EvenPath r a b)` is a derivation (a proof built from
  constructors).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Star R a b` | a derivation of `a →* b`: either `.refl a` (`b` is `a`) or `.step h hs` with `h : R a x`, `hs : Star R x b` |
| `Joinable R b c`, `LocallyConfluent R`, `Confluent R` | definitions: Lean prints the name, not the body. `intro`, `⟨…⟩` and `obtain` see through them (R6, R8, R9) |
| `Terminating R` | by definition `WellFounded fun b a => R a b`: the converse of `R` is well-founded, i.e. no infinite `R`-chain |
| `WellFounded r` | `r : α → α → Prop` has no infinite descending chain `… r a₂ a₁`, `r a₁ a₀`. Here `r b a` means `R a b`, so "descending" = "one more `R`-step" |
| `fun b a => R a b` | the relation that holds of `(b, a)` when `R a b`: the converse of `R` |
| `a✝`, `b✝¹`, `a_ih✝` | names Lean invented (after `induction`/`cases` without names); you cannot type them. Name them with `with`, `rename_i` or `next` (R2, R3) |
| `case step`, `case h.step.step` | the goal belongs to constructor `step`; `h.step.step` = case `h` of the induction, then `step` of the first `cases`, then `step` of the second |
| `P.pa`, `.pa` | constructor `pa` of the type `P`; `.pa` in source means "constructor `pa` of the expected type" |
| `R4 P.pb P.pa` | the one-step relation of the counterexample: `pb → pa` |
| `¬A` | `A → False`: prove it with `intro` (R14), use it by applying it or with `absurd` (R13) |
| `∀ (z : α), ¬R x z` | "no step out of `x`": `x` is a *normal form* |

---

## Part 1 · `star_trans` (milestone)

Statement: `Star R a b → Star R b c → Star R a c`: paths compose. Prove it first; Newman uses it to glue
`c1 →* d →* e`. Induct on the derivation `h1` (not on a point). `h2 : Star R b c` mentions the index `b`,
so `induction` puts it into the IH (R1): in the `step` case you get
`ih : Star R c✝ c → Star R b✝ c` and must build `Star R a✝¹ c` with a constructor (R4).
The original `a b c : α` stay in the context after `induction h1` but are no longer tied to anything: the
goals are about the new points `a✝`, `a✝¹`, `b✝`, `c✝` (and `c`, which is not an index of `h1`).

### Derivations of an inductive relation

**R1 · `induction p`** (with `p : EvenPath r a b`) changes the **goal list**: one goal per constructor of
`EvenPath`. In each, the indices `a`, `b` are replaced by that constructor's pattern. A constructor with a
recursive premise (`EvenPath r c d`) also gets an induction hypothesis. A hypothesis that mentions an index
(`hb : Q b`) is generalized automatically: it reappears with the new index AND becomes a premise of the IH
(`a_ih✝ : Q d✝ → Q c✝`). Placeholders: `{α : Type} (r : α → α → Prop) (Q : α → Prop) (a b : α)`.

| Before | After |
|---|---|
| `p : EvenPath r a b, hb : Q b ⊢ Q a` | `a✝ : α, hb : Q a✝ ⊢ Q a✝`, `a✝² : r a✝³ b✝, a✝¹ : r b✝ c✝, a✝ : EvenPath r c✝ d✝, a_ih✝ : Q d✝ → Q c✝, hb : Q d✝ ⊢ Q a✝³` |

**R2 · `rename_i x y …`** changes the **context**: it names the LAST inaccessible (`✝`) variables of the
current goal, in order; `_` skips one. Placeholders: fresh names. Here `rename_i s t _ ih` on the `two` goal:

| Before | After |
|---|---|
| `a✝² : r a✝³ b✝, a✝¹ : r b✝ c✝, a_ih✝ : Q d✝ → Q c✝ ⊢ Q a✝³` | `s : r a✝¹ b✝, t : r b✝ c✝, ih : Q d✝ → Q c✝ ⊢ Q a✝¹` |

`next x y … => tac` does the same and then runs `tac` on that goal.

**R3 · `induction p with | nil a => … | two s t _ ih => …`** changes the **goal list**, with names.
`| c x y => …` names only the EXPLICIT arguments of constructor `c` (its premises; not the implicit
`{a b c d}`, which stay `✝`), then the IH of each recursive premise. After `=>` comes a tactic block; `?_`
(used in the guide only to show the states) leaves the goal open.

| Before | After |
|---|---|
| `p : EvenPath r a b, hb : Q b ⊢ Q a` | `a : α, hb : Q a ⊢ Q a`, `s : r a✝¹ b✝, t : r b✝ c✝, ih : Q d✝ → Q c✝, hb : Q d✝ ⊢ Q a✝¹` |

For `Star`: `induction h1 with | refl => … | step s _ ih => …` (`refl` has the explicit argument `a`,
which you may leave unnamed).

**R4 · `exact .c args`** **closes** the goal by building a derivation. `.two s t p` is `EvenPath.two s t p`: a
leading `.` takes the constructor from the goal's type. Implicit arguments are inferred; an explicit one
can be `_` (`.nil _`). Nest them to build longer paths: `.two s t (.two s' t' (.nil _))`. Placeholders:
`(a b c : α) (s : r a b) (t : r b c)`.

| Before | After |
|---|---|
| `s : r a b, t : r b c ⊢ EvenPath r a c` | closed by `exact .two s t (.nil _)` |

---

## Part 2 · `newman`

Statement: `Terminating R → LocallyConfluent R → Confluent R`. Outline: `intro a` (R6), well-founded
induction on `a` (R7), introduce `b c hb hc`, case-split both paths on their first step (R5), and in the
`step`/`step` case join as in the diagram (R2, R9, R8, R4, `star_trans`).

**R5 · `cases p with | nil a => … | two s t q => …`** changes the **goal list**: one goal per constructor,
with no IH. In the `nil` goal the end index is unified with the start: `b` is replaced by `a` everywhere.
In the `two` goal the intermediate points are new (`b✝ c✝`). Placeholders:
`{α : Type} (r P : α → α → Prop) (a b : α)`.

| Before | After |
|---|---|
| `p : EvenPath r a b ⊢ P a b` | `a : α ⊢ P a a`, `s : r a b✝, t : r b✝ c✝, q : EvenPath r c✝ b ⊢ P a b` |

In Newman: `cases hb with | refl => … | step hab1 hb1 => …`. In the `refl` case `b` becomes `a`, and
`⟨c, hc, .refl c⟩` joins (R8, R4). After the second `cases hc`, the two first-step targets are `b✝¹`, `b✝`:
name them with `rename_i b1 c1` (R2).

### Definitions, `∃`, well-founded induction

**R6 · `intro x`** on a definition changes the **context**: `intro` unfolds the definition (`Always Q` is
`∀ x, Q x`) to find the binder. `Confluent R` unfolds the same way: `intro a` gives
`⊢ ∀ (b c : α), Star R a b → Star R a c → Joinable R b c`. Placeholders: `{α : Type} (Q : α → Prop)`.

| Before | After |
|---|---|
| `⊢ Always Q` | `x : α ⊢ Q x` |

**R7 · `induction a using hw.induction`** changes the **goal and the context**. The lemma is
`WellFounded.induction : WellFounded r → ∀ a, (∀ x, (∀ y, r y x → C y) → C x) → C a`, with motive
`C : α → Prop` = the current goal as a function of `a`. With `hw : WellFounded fun b a => r a b`, the premise
`r' y x` reads `r x y`: you prove `C x` assuming `C y` for every `y` ONE `r`-step after `x`. Placeholders:
`{α : Type} (r : α → α → Prop) (C : α → Prop) (a : α)`.

| Before | After | After `rename_i a ih` |
|---|---|---|
| `a : α ⊢ C a` | `x✝ : α ⊢ C x✝` (and `a✝`, the IH) | `a : α ⊢ C a` (and `ih : ∀ (y : α), r a y → C y`) |

Name them directly with `induction a using hw.induction with | _ a ih => …` (one alternative, called `h`; `_`
matches it). In the exercise `ht : Terminating R`: `ht.induction` works because `Terminating R` unfolds to a
`WellFounded`, so Lean finds `WellFounded.induction`. **Order matters:** everything still in the goal goes into
`C`. `intro a` only, then induct: `ih` then covers all `b c` and all paths out of each `y` (W1).

**R8 · `exact ⟨z, hq, hq'⟩`** **closes** a goal `∃ z, Q z ∧ Q' z`, also when it is hidden behind a definition
(`Both Q Q'`, `Joinable R b c`). `⟨z, hq, hq'⟩` is `⟨z, ⟨hq, hq'⟩⟩`. Placeholders:
`{α : Type} (Q Q' : α → Prop) (z : α)`. Any argument may be `_` when Lean can infer it (`⟨_, .refl _, hc⟩`).

| Before | After |
|---|---|
| `hq : Q z, hq' : Q' z ⊢ Both Q Q'` | closed |

**R9 · `obtain ⟨z, hq, hq'⟩ := e`** changes the **context**: `e : ∃ z, Q z ∧ Q' z` (or a definition unfolding
to it) becomes a witness `z` and two facts. `e` may be an application such as `f _ hx`: `_` asks Lean to infer
that argument from the types of the later ones. Placeholders: `{α : Type} (Q Q' R : α → Prop)`,
`(f : ∀ x, R x → Both Q Q')`.

| Before | After |
|---|---|
| `hx : R x ⊢ G` | `z : α, hq : Q z, hq' : Q' z ⊢ G` |

In Newman: `obtain ⟨d, hb1d, hc1d⟩ := hl _ _ _ hab1 hac1`, then the same with `ih b1 hab1 _ _ …` and
`ih c1 hac1 _ _ …` (the IH is a function: give it the point, the step, then the two paths).

---

## Part 3 · `r4_locally_confluent`

Statement: `LocallyConfluent R4` for `pa ← pb ⇄ pc → pd`. Introduce `a b c hb hc`, list every pair of steps out
of the same point with `cases hb <;> cases hc` (R10; `<;>` runs the second `cases` on every goal of the
first). That leaves eight goals, named by the two constructors used: `case ba.bc` is `Joinable R4 P.pa P.pc`
(the steps pb → pa and pb → pc), `case cd.cd` is `Joinable R4 P.pd P.pd`, and so on. Then close all goals with one
`all_goals first | … | …` (R11) of candidate joins (R8 with R4 paths such as `.step .cb (.step .ba (.refl _))`).

### Concrete finite relations

**R10 · `cases h`** with `h : Next .red x` changes the **goal list**: one goal per constructor whose indices
FIT. Only `rg` and `rb` start at `.red`; `x` is replaced by their targets. Placeholders: `(P : Col → Prop)
(x : Col)`. Two hypotheses `h1 : Next a b`, `h2 : Next a c` with `a` a variable: `cases h1 <;> cases h2`
keeps only pairs that start at the same point (W2).

| Before | After |
|---|---|
| `h : Next Col.red x ⊢ P x` | `⊢ P Col.green`, `⊢ P Col.blue` |

**R11 · `first | tac₁ | tac₂ | …`** changes the **goal list**: it runs `tac₁`; if that fails, `tac₂`; and so
on, keeping the first that succeeds (and fails if all do). Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `hb : B ⊢ A ∨ B` | closed: `exact Or.inl hb` fails, `exact Or.inr hb` succeeds |

---

## Part 4 · `star_from_normal` (milestone)

Statement: if no step leaves `x` (`hn : ∀ z, ¬ R x z`) then every path out of `x` is empty: `Star R x y → y = x`.
`cases h` (R5): `refl` gives `x = x` (`rfl`); `step s _` gives `s : R x _`, contradicting `hn _` (R13). Used
twice in Part 5, for `pa` and `pd`.

**R13 · `absurd h hn`** **closes** any goal. The lemma is `absurd : a → ¬a → b`. Placeholders: `(A G : Prop)`.

| Before | After |
|---|---|
| `h : A, hn : ¬A ⊢ G` | closed by `exact absurd h hn` |

---

## Part 5 · `r4_not_confluent`

Statement: `¬ Confluent R4`. Assume `h : Confluent R4` (R14). Apply it to the two paths `pb →* pa` and
`pb →* pd` (R4) and unpack the join `e` (R9). `pa` and `pd` are normal forms (R12), so `star_from_normal`
gives `e = pa` and `e = pd`; substitute one (R15), and `pd = pa` is impossible (R16).

**R14 · `intro h`** on `¬ A` changes the **goal and the context**: `¬ A` is `A → False`, so `h : A` is added
and the goal becomes `False`. Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬A` | `h : A ⊢ False` |

**R12 · `nomatch h`** **closes** any goal when no constructor can produce `h`'s type. No `Next` constructor
starts at `.white`. As a term, `fun z h => nomatch h` proves `∀ z, ¬ Next .white z` (that is
`∀ z, Next .white z → False`): the `hn` argument of `star_from_normal`. Placeholders: `(G : Prop) (x : Col)`.

| Before | After |
|---|---|
| `h : Next Col.white x ⊢ G` | closed |

**R15 · `subst h`** (with `h : y = e`, `y` a local variable) changes the **context and the goal**: `y` is
replaced by `e` everywhere and `h` disappears. Either side may be the variable; if both are, the right-hand one
goes. Placeholders: `(P : Col → Prop) (y : Col)`.

| Before | After |
|---|---|
| `h : y = Col.red, hp : P Col.red ⊢ P y` | `hp : P Col.red ⊢ P Col.red` |

**R16 · `cases h`** with `h : Col.red = Col.blue` **closes** the goal: two different constructors are never
equal, so `cases` finds no way `h` could hold. Placeholders: `(G : Prop)`.

| Before | After |
|---|---|
| `h : Col.red = Col.blue ⊢ G` | closed |

### Worked combinations (W1–W4, on the toy objects)

**W1: irreflexivity from termination.** `∀ a, ¬ r a a`: `intro a`, then `induction a using hw.induction with
| _ a ih =>`, then `intro h` and `exact ih a h h` (the IH at `y := a`, reached by the step `h`). Before the
induction:

```lean-goal
⊢ ¬r a a
```

**W2: all pairs of steps.** `cases h1 <;> cases h2` on `h1 : Next a b`, `h2 : Next a c` leaves six goals (only
pairs out of the same colour), for example

```lean-goal
⊢ ∃ d, (d = Col.green ∨ Next Col.green d) ∧ (d = Col.blue ∨ Next Col.blue d)
⊢ ∃ d, (d = Col.white ∨ Next Col.white d) ∧ (d = Col.white ∨ Next Col.white d)
```

and `all_goals first | exact ⟨_, .inl rfl, .inl rfl⟩ | exact ⟨.white, .inr .gw, .inr .bw⟩ | …` closes them.

**W3: `subst` then a constructor clash.** From `h1 : x = .red`, `h2 : x = .blue`, `subst h1` leaves
`h2 : Col.red = Col.blue ⊢ False`, which `cases h2` closes.

**W4: a derivation out of a dead end.** `cases p with | nil => rfl | two s _ _ => nomatch s` on
`p : EvenPath Next .white x`.

---

## Traps

- **`intro` too much before the induction.** After `intro a b c hb hc`, induction on `a` keeps `b c` fixed:
  the IH can only join paths ending at that same `b` and `c`, but at `b1` you must join `b` with `d`.
  Introduce `a` alone, induct, then `intro b c hb hc` (R7, W1).
- **Induct on the derivation, not on a point**, in `star_trans`: `induction h1`, with `h2` left in the
  context so it lands in the IH (R1).
- **`with` names only explicit arguments.** In `cases hb with | step hab1 hb1`, the middle point stays `b✝`;
  after the second `cases`, use `rename_i b1 c1` (R2). Writing `| step b1 hab1 hb1` fails with
  "Too many variable names provided".
- **`;` vs `<;>`.** `cases hb; cases hc` would split `hc` only in the first goal. Use `<;>` and `all_goals`
  (TACTIC_STATES, "Structure").
- **IH direction.** The IH of R7 is about points one step AFTER `a` (`R a y`), because `Terminating` is the
  converse of `R` being well-founded.
- **Glue before applying the IH at `c1`.** You need a path `c1 →* e`, but have `c1 →* d` and `d →* e`: that is
  what `star_trans` is for.
- `rfl` closes `x = x`; `cases h` with `h : P.pd = P.pa` closes the goal (R16), but `rfl` cannot prove a false
  equation.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induct on a derivation | `induction h with \| refl => … \| step s _ ih => …` | R1, R3 |
| name `✝` variables | `rename_i x y`, `next x y => …` | R2 |
| build a path | `.step h (.step h' (.refl _))` | R4 |
| split a path on its first step | `cases h with \| refl => … \| step s hs => …` | R5 |
| open a `def` whose body is `∀` | `intro x` | R6 |
| well-founded induction | `intro a; induction a using ht.induction with \| _ a ih => …` | R7 |
| prove `Joinable R b c` | `exact ⟨d, hbd, hcd⟩` | R8 |
| use `Joinable`/`∃` (also a function's result) | `obtain ⟨d, hbd, hcd⟩ := hl _ _ _ h1 h2` | R9 |
| all steps out of a concrete point | `cases h`, `cases h1 <;> cases h2` | R10 |
| try several closers on every goal | `all_goals first \| tac₁ \| tac₂` | R11 |
| impossible step | `nomatch h`, `fun z h => nomatch h` | R12 |
| `h : A`, `hn : ¬A` | `absurd h hn` | R13 |
| prove `¬A` | `intro h` (goal `False`) | R14 |
| eliminate `y = e` | `subst h` | R15 |
| `h : c₁ = c₂`, different constructors | `cases h` | R16 |
| glue paths | `star_trans h1 h2` (milestone) | Part 1 |
| see the state | infoview | |
