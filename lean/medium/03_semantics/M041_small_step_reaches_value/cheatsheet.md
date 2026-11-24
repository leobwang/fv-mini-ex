# M041 · Small-step arithmetic reaches its value: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): inductive types, pattern-matching definitions, `induction`,
`cases`, `exact`, `rw`, `simp`, `·` focusing, writing your own helper `theorem`. M040 defines the same `Step`
relation. **New here:** induction on a *proof* of an inductive relation (one goal per rule), the
reflexive-transitive closure `Star` and the two helper lemmas every closure proof needs (transitivity,
congruence), and passing a rule of a relation as a function. Core Lean only, no Mathlib.

## The objects

- `Expr`: arithmetic expressions `num n`, `plus a b`, `times a b` over `Nat`. `eval : Expr → Nat` is the
  evaluator (big-step meaning).
- `Step e e' : Prop`: one left-to-right reduction step. Rules: `plusNum`/`timesNum` compute
  `num m ⊕ num n` to `num (m ⊕ n)` (`⊕` is `+` or `*`); `plusL`/`timesL` step inside the left operand;
  `plusR`/`timesR` step inside the right operand, **only when the left one is already a numeral `num m`**.
- `Star e e' : Prop`: zero or more steps. `Star.refl e : Star e e`; `Star.step : Step a b → Star b c → Star a c`
  (one step at the front, then the rest of the run).
- The three theorems: `step_eval` (a step keeps `eval`), `reaches_value` (every `e` runs to
  `num (eval e)`), `star_value` (any numeral `e` runs to is `num (eval e)`).

## How to read an entry

Each entry is one tactic or one proof move. It says what changes (**goal**, **context**, or **goal
list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
  `∅` means the goal is closed.
- `P`, `Q`, `R`, `r` are "the rest of your goal" (`P : Tm → Tm → Prop`, `Q : Tm → Prop`, …).
- Entries use the guide's toy language, **not** `Expr`: `Tm` (`val n`, `wrap t`, `pair s t`), its value
  `ev : Tm → Nat` (`ev (val n) = n`, `ev (wrap t) = ev t`, `ev (pair s t) = ev s + ev t`), the step
  `TStep` (`unwrap : TStep (wrap (val n)) (val n)`, `cong : TStep t t' → TStep (wrap t) (wrap t')`) and
  its closure `TStar` (rules `refl`, `step`, exactly shaped like `Star`).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `(Expr.num m).plus b` | `Expr.plus (Expr.num m) b`, written `.plus (.num m) b` in the source. Lean prints `Expr.plus x y` as `x.plus y` because `x : Expr`; same for `(Tm.val n).wrap` |
| `Expr.num (eval e)` | the numeral whose value is `eval e` (no dot form: the argument is a `Nat`) |
| `m✝`, `a'✝`, `t✝` | an *inaccessible* name: a variable `induction` introduced (a rule's implicit argument). You cannot type it; use `_`, `‹_›`, or name it with `with`/`rename_i` |
| `a✝ : Step a✝¹ a'✝` | the premise of the rule `plusL`/`timesL`/… for this goal |
| `a_ih✝ : eval a'✝ = eval a✝¹` | the induction hypothesis for that premise |
| `a✝²`, `a✝¹` | further inaccessible names; the superscript only tells them apart |
| `case plusNum`, `case step` | the goal for that rule of the relation |
| `∀ {a b : Tm}, …` | a statement whose `a b` are implicit: Lean fills them from the next argument's type |
| `(fun x => x.wrap) a` | a function applied to `a`; it is `a.wrap` by β-reduction (Lean computes it by itself) |
| `.plus · b`, `.plus (.num m) ·` (skeleton, text) | a *context*: the expression with a hole `·`, i.e. the function `fun x => .plus x b` (valid Lean inside parentheses) |

---

## Part 1 · `step_eval`

Statement: `Step e e' → eval e' = eval e`. Induct on the proof of `Step e e'`, then compute.

**R1 · `induction h`** on `h : TStep a b` changes the **goal list and the context**: one goal per rule of the
relation, with `a`, `b` replaced by that rule's terms. A rule with a premise (`cong`, or `plusL` in the
exercise) also adds the premise `a✝` and its IH `a_ih✝`. Placeholders:
`(P : Tm → Tm → Prop) (a b : Tm) (h : TStep a b)`. In the exercise this gives six goals,
`plusNum` … `timesR`; e.g. `plusL`: `a_ih✝ : eval a'✝ = eval a✝¹ ⊢ eval (a'✝.plus b✝) = eval (a✝¹.plus b✝)`.
In the guide, `‹_›` (typed `\f<` `_` `\f>`) is "some hypothesis of the type Lean expects here", found by
`assumption`; it is how you pass an inaccessible hypothesis such as `a_ih✝` without naming it.

| Before | After |
|---|---|
| `h : TStep a b ⊢ P a b` | `n✝ : Nat ⊢ P (Tm.val n✝).wrap (Tm.val n✝)`, `a✝ : TStep t✝ t'✝, a_ih✝ : P t✝ t'✝ ⊢ P t✝.wrap t'✝.wrap` |

**R2 · `simp_all [f]`** **closes** the goal (or fails): it simplifies the goal and every hypothesis, unfolding
the equations of `f`, and uses each hypothesis `x = y` to rewrite the others. That is the IH `a_ih✝` in the
congruence cases. Run it on every goal of R1 with `induction h <;> simp_all [eval]`. Placeholders:
`(n : Nat)`, `(f : Tm → Nat) (s s' : Tm) (k : Nat)`.

| Before | After |
|---|---|
| `n : Nat ⊢ ev (Tm.val n) = ev (Tm.val n).wrap` | ∅ (`simp_all [ev]`) |
| `ih : f s' = f s ⊢ f s' + k = f s + k` | ∅ (`simp_all`) |

**W1** in the guide does Part 1 for `TStep`: `induction h <;> simp_all [ev]`.

---

## Part 2 · `reaches_value`

Statement: `Star e (.num (eval e))`. Induct on `e`. For `plus a b` the run has three stretches:
`a` → `num (eval a)` inside the left operand, then `b` → `num (eval b)` inside the right operand, then one
`plusNum`. Gluing stretches needs **transitivity** of `Star`, and running inside an operand needs
**congruence**; prove both as your own helper theorems first (milestones in the skeleton).

### Milestones: induction on a `Star`

**R3 · `induction h with | refl t => … | step s hs ih => …`** on `h : TStar a b` changes the **goal list and the
context**: `refl`, where both ends are `t`; `step`, with the first step `s`, the rest `hs` and the IH `ih` for
`hs`. Placeholders: `(P : Tm → Tm → Prop) (a b : Tm) (h : TStar a b)`. Without `with` the names are
inaccessible; `rename_i s hs ih` names them (the states below are after it). `rename_i x y z` gives names
to the last inaccessible variables and hypotheses of the current goal, oldest first; the `refl`/`step`
alternatives of `with` take their names in the order the rule lists its arguments (`step {a b c} (s) (hs)`
then the IH, implicit `a b c` skipped).

| Before | After |
|---|---|
| `h : TStar a b ⊢ P a b` | `⊢ P t✝ t✝`, `s : TStep a✝ b✝, hs : TStar b✝ c✝, ih : P b✝ c✝ ⊢ P a✝ c✝` |

**R4 · `induction h` with `k` about an index** changes the **goal list and the context**, like R3, but a
hypothesis `k` that mentions `b` (an end of `h`) is first moved into the goal. So the IH gets `k`'s statement
as a premise, `ih : Q c✝ → R b✝ c✝`, and `k` comes back for the case's own end. For transitivity
(`Star a b → Star b c → Star a c`) induct on the first run: the second, `h2 : Star b c`, is `k`, and in the
`step` case `ih h2` is the run from the middle. Placeholders: `(Q : Tm → Prop) (R : Tm → Tm → Prop) (k : Q b)`.

| Before | After |
|---|---|
| `h : TStar a b, k : Q b ⊢ R a b` | `k : Q t✝ ⊢ R t✝ t✝`, `ih : Q c✝ → R b✝ c✝, k : Q c✝ ⊢ R a✝ c✝` |

**R5 · `exact .ctor args`** **closes** the goal with a rule. `.refl _` is `TStar.refl _` (Lean takes the
namespace from the goal's head); `_` is an explicit argument it infers; implicit `{a b c}` are never written.
`.step s r` puts one step in front of a run; `.step .unwrap (.refl _)` is a run of exactly one step.

| Before | After |
|---|---|
| `t : Tm ⊢ TStar t t` | ∅ (`exact .refl _`) |
| `s : TStep a b, r : TStar b c ⊢ TStar a c` | ∅ (`exact .step s r`) |
| `n : Nat ⊢ TStar (Tm.val n).wrap (Tm.val n)` | ∅ (`exact .step .unwrap (.refl _)`) |

**W2** proves the congruence for the one context `wrap`, `TStar a b → TStar a.wrap b.wrap`, by R3 and R5:
`refl` gives `.refl _`, `step` gives `.step (.cong s) ih`. The exercise has four contexts (`.plus · b`,
`.plus (.num m) ·`, `.times · b`, `.times (.num m) ·`); one helper with the context as a function `f` and a
hypothesis `hf : ∀ {a b}, Step a b → Step (f a) (f b)` covers all four (R10).

### The induction on `e`

**R8 · `induction t with | val n => … | wrap t ih => … | pair s t ihs iht => …`** changes the **goal list and
the context**: one goal per constructor, one IH per argument of the inductive type. In the exercise:
`| num n => … | plus a b iha ihb => … | times a b iha ihb => …`, with
`iha : Star a (Expr.num (eval a))`. Placeholders: `(P : Tm → Prop) (t : Tm)`.

| Before | After `induction t` | After `rename_i s t ihs iht` (last goal) |
|---|---|---|
| `t : Tm ⊢ P t` | `n✝ : Nat ⊢ P (Tm.val n✝)`, `t_ih✝ : P t✝ ⊢ P t✝.wrap`, `s_ih✝ : P s✝, t_ih✝ : P t✝ ⊢ P (s✝.pair t✝)` | `ihs : P s, iht : P t ⊢ P (s.pair t)` |

**R9 · `refine lem x ?_`** changes the **goal**: the lemma is applied, the arguments you give are used, and each
`?_` becomes a goal. With transitivity `tr : r a b → r b c → r a c`, `refine tr hab ?_` keeps only the rest of
the run. Lean finds the middle point `b` from `hab`. Placeholders:
`(r : Tm → Tm → Prop) (tr : ∀ {x y z : Tm}, r x y → r y z → r x z) (hab : r a b)`.

| Before | After |
|---|---|
| `hab : r a b ⊢ r a c` | `⊢ r b c` |

In the exercise, `plus a b` starts at `⊢ Star (a.plus b) (Expr.num (eval (a.plus b)))`; after the first
`refine star_trans (…) ?_` it is `⊢ Star ((Expr.num (eval a)).plus b) (Expr.num (eval (a.plus b)))`, and
after the second `⊢ Star ((Expr.num (eval a)).plus (Expr.num (eval b))) (Expr.num (eval (a.plus b)))`.
The last `plusNum` step produces `Expr.num (eval a + eval b)`, and `eval (a.plus b)` unfolds to exactly that
(R7, Part 3), so `.step .plusNum (.refl _)` closes it with no rewriting. The `num n` case is R7 too:
`Expr.num (eval (Expr.num n))` is `Expr.num n`, so `.refl _` closes it.

**R10 · a rule is a function** · `exact .cong` **closes** `∀ {a b}, TStep a b → TStep (g a) (g b)` for
`g := fun x => x.wrap`. A rule with a premise *is* a proof of "premise → conclusion" for all its implicit
arguments, so `.plusL` can be passed as the `hf` of your congruence helper with `f := fun x => .plus x b`.
`(fun x => x.wrap) a` reduces to `a.wrap` (β-reduction) without any tactic. Placeholders: none.

| Before | After |
|---|---|
| `⊢ ∀ {a b : Tm}, TStep a b → TStep ((fun x => x.wrap) a) ((fun x => x.wrap) b)` | ∅ |

**W3** chains R9, R10 and R5 on `wrap (wrap (val n))`, given a transitivity fact `tr` and a lifting fact
`lift`:

```lean-goal
⊢ TStar (Tm.val n).wrap.wrap (Tm.val n)
⊢ TStar (Tm.val n).wrap (Tm.val n)
```

---

## Part 3 · `star_value`

Statement: `Star e (.num n) → n = eval e`. `induction h` fails here: the end `.num n` is not a variable, so
Lean cannot replace it by each rule's end. Prove the general fact `Star e e' → eval e' = eval e` as a helper
(milestone) by R3, then apply it to `h`.

**R6 · `rw [h₁]`, then `rw [h₂]`** changes the **goal**; when the goal becomes `x = x`, `rw` closes it by
`rfl`. In the helper's `step` case: `rw [ih, step_eval s]`. Placeholders:
`(f : Tm → Nat) (a b c : Tm) (h₁ : f c = f b) (h₂ : f b = f a)`.

| Before | After `rw [h₁]` | After `rw [h₂]` |
|---|---|---|
| `h₁ : f c = f b, h₂ : f b = f a ⊢ f c = f a` | `⊢ f b = f a` | ∅ |

**R7 · definitional unfolding** **closes** a goal with a term whose type *unfolds* to the goal. `ev (Tm.val n)`
is `n` by `ev`'s first equation, so `h : ev (Tm.val n) = m` proves `⊢ n = m` with `exact h`, no rewriting.
Likewise the helper applied to `h : Star e (Expr.num n)` has type `eval (Expr.num n) = eval e`, which *is*
`n = eval e`. The helper's `refl` case `eval e = eval e` is `rfl`. Placeholders: `(n m : Nat)`.

| Before | After |
|---|---|
| `h : ev (Tm.val n) = m ⊢ n = m` | ∅ (`exact h`) |

---

## Traps

- **`grind` and `try?` are banned** (`try?` would print a `grind` one-liner for `step_eval`). Use `simp_all`
  (R2). Do not leave search tactics (`exact?`, `apply?`) in the file.
- **Order of the stretches.** `plusR`/`timesR` only step the right operand once the left one is `num m`. Run
  the left operand down first, then the right one with `f := fun x => .plus (.num (eval a)) x`.
- **`induction h` on `h : Star e (.num n)` fails** (`Invalid target: Index in target's type is not a variable`). Generalize:
  prove the claim for every end `e'` (Part 3).
- **Transitivity: induct on the first run**, not the second. The `Star.step` rule adds steps at the front.
- **Indent the alternatives** of `induction … with` (`| refl t => …`) consistently; each must cover one rule.
- Write helper theorems **before** the theorem that uses them and **outside** the `BEGIN SPEC`/`END SPEC`
  regions.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| one goal per rule of `Step` | `induction h` | R1 |
| compute both sides, use the IH | `simp_all [eval]` (all goals: `induction h <;> simp_all [eval]`) | R2 |
| induction on a run | `induction h with \| refl e => … \| step s hs ih => …` | R3 |
| IH that takes another run | keep `h2 : Star b c` in the context, then `ih h2` | R4 |
| build a run | `.refl _`, `.step s r`, `.step .plusNum (.refl _)` | R5 |
| chain equations | `rw [ih, step_eval s]` | R6 |
| `eval (.num n)` is `n` | `exact (helper h)` as is | R7 |
| induction on `e` | `induction e with \| num n => … \| plus a b iha ihb => … \| times a b iha ihb => …` | R8 |
| glue two runs | `refine star_trans (…) ?_` | R9 |
| a rule as a step-lifting function | `.plusL`, `.plusR`, … with `f := fun x => .plus x b` | R10 |
| see the state | infoview | |
