# M040 · Small-step arithmetic: progress and determinism: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033: `intro`, `exact`, `cases`/`rcases` on `∨` and `∃`, anonymous
constructors `⟨_, _⟩`, `rfl`, `<;>`, structural induction on `Nat` and lists). **New here:** an inductive
*relation* `Step : Expr → Expr → Prop` (a small-step semantics), proofs of it as *derivations* (trees of
rules), *inversion* with `cases`, induction on a derivation with `generalizing`, and `simp_all`. No Mathlib:
everything is core Lean.

## How to read an entry

Each entry is one tactic or one proof term. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P`, `G` are "the rest of your goal" (`P : Ex → Prop`, `G : Prop`). The step changes only the part shown
  inside `P (…)`.
- The guide does not use the exercise's objects. It uses a toy language with the same shape:

  | Toy (guide) | Exercise | Role |
  |---|---|---|
  | `Ex` with `k n`, `sub a b`, `dbl a` | `Expr` with `num n`, `plus a b`, `times a b` | syntax |
  | `Red e e'` | `Step e e'` | one reduction step; a proof is a derivation tree |
  | `subK`, `dblK` | `plusNum`, `timesNum` | compute on two numerals (no premise) |
  | `subL` | `plusL`, `timesL` | step inside the left operand |
  | `subR` (left side already `.k m`) | `plusR`, `timesR` (left side already `.num m`) | step inside the right operand |
  | `dblC` | (none) | step inside the only operand |
  | `k_stuck : ¬ Red (.k n) e` | your `num_stuck` | a numeral does not step |

- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Step e e'` | `e` reduces to `e'` in one step: there is a derivation built from the six rules of `Step` |
| `Expr.num n`, `Ex.k n` | a constructor with its namespace; in source you may write `.num n` when the type is known |
| `a.plus b`, `(Expr.num m).plus b`, `a✝.dbl` | `Expr.plus a b`, `Expr.plus (Expr.num m) b`, `Ex.dbl a✝`: Lean prints a constructor applied to its first argument with dot notation |
| `¬A` | `A → False` |
| `.plusL h`, `.subK`, `.inl x` | a rule (or `Or.inl`) used as a proof term; the leading dot means "look the name up in the namespace of the expected type" (R4, R7) |
| `a✝`, `m✝`, `a'✝¹` | an *inaccessible* name: Lean made it, you cannot type it. Name it with `with \| rule x y =>`; `✝¹` tells two of them apart |
| `a_ih✝` | an induction hypothesis Lean made (R3, R9) |
| `∀ {e2 : Expr}, Step a✝ e2 → a'✝ = e2` in an IH | the IH holds for every target `e2`; Lean fills `e2` in when you apply it (R9, R13) |
| `‹_›` | `by assumption`: some hypothesis of the needed type (R13) |
| `case plus`, `case plusL.plusR`, `case inl` | the goal for constructor `plus`; for rule `plusL` of `h1` then rule `plusR` of `h2`; the left side of an `rcases` |

---

## Part 1 · `num_stuck` (used in Part 3)

Statement: `¬ Step (.num n) e`: a numeral does not step. Introduce the step (R1) and invert it (R2): no rule of
`Step` has a numeral on the left, so nothing is left to prove.

**R1 · `intro h`** changes the **goal and the context**: `¬ A` is `A → False`, so `intro` moves `A` into the
context as `h` and leaves `False`. Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬A` | `h : A ⊢ False` |

**R2 · `cases h`** where no rule can produce `h` **closes** the goal. `cases` keeps only the rules whose
conclusion can match `h`'s arguments (its *indices*); every rule of `Red` concludes `Red (.sub …) _` or
`Red (.dbl …) _`, none `Red (.k n) _`, so no goal is left. Placeholders: `(n : Nat) (e : Ex) (G : Prop)`.

| Before | After |
|---|---|
| `h : Red (Ex.k n) e ⊢ G` | no goals |

---

## Part 2 · `progress`

Statement: `(∃ n, e = .num n) ∨ ∃ e', Step e e'`: every expression is a numeral or can step. Induction on the
syntax `e` (R3). The `num` case is the left side (R4). In `plus a b` (and `times a b`) go `right` (R5) and split
the IH of `a` (R6): if `a` steps, the left congruence rule steps (R8); if `a` is a numeral `.num m`, split the IH
of `b` (R6): `b` steps → right congruence rule (R8), `b` a numeral → the computation rule (R7).

**R3 · `induction e`** with `e : Ex` changes the **goal list**: one goal per constructor, and one IH per argument of
type `Ex`. With `induction e with | k n => … | sub a b iha ihb => … | dbl a iha => …` you name the arguments
first, then the IHs. Placeholders: `(e : Ex) (P : Ex → Prop)`.

| Before | After (one goal per constructor) |
|---|---|
| `⊢ P e` | `n✝ : Nat ⊢ P (Ex.k n✝)` |
| | `a✝ b✝ : Ex, a_ih✝ : P a✝, b_ih✝ : P b✝ ⊢ P (a✝.sub b✝)` |
| | `a✝ : Ex, a_ih✝ : P a✝ ⊢ P a✝.dbl` |

In `progress`, `| plus a b iha ihb =>` gives `iha : (∃ n, a = Expr.num n) ∨ ∃ e', Step a e'`, the same for `b`,
and the goal `(∃ n, a.plus b = Expr.num n) ∨ ∃ e', Step (a.plus b) e'`.

**R4 · `exact .inl ⟨n, rfl⟩`** **closes** `(∃ m, x = y) ∨ B` with its left side. `.inl` is `Or.inl`; `⟨n, rfl⟩`
gives the witness `n` and proves the equation by `rfl`. Placeholders: `(n : Nat) (B : Prop)`.

| Before | After |
|---|---|
| `⊢ (∃ m, Ex.k n = Ex.k m) ∨ B` | no goals |

**R5 · `right`** changes the **goal**: `A ∨ B` becomes `B` (`left` gives `A`). Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∨ B` | `⊢ B` |

**R6 · `rcases ih with ⟨m, rfl⟩ | ⟨a', ha⟩`** changes the **goal list and the context**: one goal per side of the
`∨`. In the left goal the `∃` is opened and the `rfl` pattern substitutes `a := Ex.k m` in the goal and in every
hypothesis (`a` must be a local variable; after R3 it is). In the right goal you get the witness `a'` and its
step `ha`. Placeholders: `{a : Ex} (P : Ex → Prop)`, `(ih : (∃ m, a = .k m) ∨ ∃ a', Red a a')`.

| Before | After |
|---|---|
| `⊢ P a` (with `ih` as above) | `m : Nat ⊢ P (Ex.k m)`, `a' : Ex, ha : Red a a' ⊢ P a` |

**R7 · `exact ⟨_, .subK⟩`** **closes** `∃ e', Red e e'` with a computation rule: the rule proves the `Red`, and
the witness `_` is read off its conclusion. The rule must match `e` *literally* (up to computation): `.subK`
needs both operands to be `Ex.k _` already, which is what the two `rfl`s of R6 achieve. Placeholders:
`(m n : Nat)`.

| Before | After |
|---|---|
| `⊢ ∃ e', Red ((Ex.k m).sub (Ex.k n)) e'` | no goals |

**R8 · `exact ⟨_, .subL ha⟩`** **closes** `∃ e', Red e e'` with a congruence rule applied to a step `ha` of a
subexpression. In the exercise: `⟨_, .plusL ha⟩`, `⟨_, .plusR hb⟩` (the latter only after `a` became `.num m`).
Placeholders: `{a a' : Ex} (b : Ex) (ha : Red a a')`.

| Before | After |
|---|---|
| `ha : Red a a' ⊢ ∃ e', Red (a.sub b) e'` | no goals |

---

## Part 3 · `step_det`

Statement: `Step e e1 → Step e e2 → e1 = e2`. Induct on the first derivation `h1`, keeping `e2` general (R9). In
each of the six cases invert `h2` (R10). The pairs of different rules always contain a step out of a numeral
(`plusNum` against `plusL` needs `Step (.num m) _`; `plusL` against `plusR` too), which `simp_all [num_stuck]`
kills (R11). Same rule on both sides: computation rules give `x = x`, closed by `simp_all`; congruence rules give
`a'.plus b = a''.plus b`, which `simp_all` reduces to `a' = a''` (R12) and the IH closes (R13).

**R9 · `induction h1 generalizing e2`** changes the **goal list**: one goal per rule of `Red`, with the rule's
premises as hypotheses and one IH per premise that is itself a `Red`. `h2 : Red e e2` mentions `e`, so Lean
reverts and reintroduces it in every goal with `e` replaced by the rule's left side. `generalizing e2` makes each
IH read `∀ {e2 : Ex}, Red a e2 → …`: it applies to *whatever* the other derivation reduces to. With
`induction h1 generalizing e2 with | subK | dblK => tac | subL _ ih | subR _ ih => tac …` several rules can share
one `=> tac` (the names they bind must agree). Placeholders: `{e e1 e2 : Ex} (P : Ex → Ex → Prop)`.

| Before | After (one goal per rule) |
|---|---|
| `h1 : Red e e1, h2 : Red e e2 ⊢ P e1 e2` | `m✝ n✝ : Nat, h2 : Red ((Ex.k m✝).sub (Ex.k n✝)) e2 ⊢ P (Ex.k (m✝ - n✝)) e2` |
| | `a✝ : Red a✝¹ a'✝, h2 : Red (a✝¹.sub b✝) e2 ⊢ P (a'✝.sub b✝) e2` |
| | `a✝ : Red b✝ b'✝, h2 : Red ((Ex.k m✝).sub b✝) e2 ⊢ P ((Ex.k m✝).sub b'✝) e2` |
| | `h2 : Red (Ex.k n✝).dbl e2 ⊢ P (Ex.k (2 * n✝)) e2` |
| | `a✝ : Red a✝¹ a'✝, h2 : Red a✝¹.dbl e2 ⊢ P a'✝.dbl e2` |

In the `subL` goal the IH is `a_ih✝ : ∀ {e2 : Ex}, Red a✝¹ e2 → P a'✝ e2`. Without `generalizing e2` it would
be stated for the one fixed `e2`, the target of the whole step, and be useless.

**R10 · `cases h2`** with `h2 : Red (.sub a b) e2` (*inversion*) changes the **goal list and the context**: one
goal per rule whose left side can be `.sub a b`, and in each `a`, `b`, `e2` are replaced by that rule's shapes
(in `subK`, `a` and `b` become numerals). `dblK`, `dblC` cannot match and do not appear. Placeholders:
`{a b e2 : Ex} (P : Ex → Prop)`.

| Before | After (one goal per matching rule) |
|---|---|
| `h2 : Red (a.sub b) e2 ⊢ P e2` | `m✝ n✝ : Nat ⊢ P (Ex.k (m✝ - n✝))` |
| | `a✝ : Red a a'✝ ⊢ P (a'✝.sub b)` |
| | `a✝ : Red b b'✝ ⊢ P ((Ex.k m✝).sub b'✝)` |

After `induction h1` this produces the rule *pairs*: in `step_det`, `cases h2` in the `plusL` goal gives
`case plusL.plusNum`, `case plusL.plusL`, `case plusL.plusR`. In the mismatched ones the variable from `h1`'s rule
has become a numeral, e.g. `a✝ : Step (Expr.num m✝) a'✝`.

**R11 · `simp_all [k_stuck]`** **closes** a goal whose context holds a step out of a numeral. `simp_all`
simplifies all hypotheses and the goal together; the lemma `k_stuck : ¬ Red (.k n) e` rewrites
`h : Red (.k n) e` to `False`, and a `False` hypothesis closes the goal. A theorem must be named in the brackets
(hypotheses are used unnamed). In the exercise, pass your Part 1 theorem: `simp_all [num_stuck]`.
Placeholders: `{n : Nat} {e : Ex} (G : Prop)`.

| Before | After |
|---|---|
| `h : Red (Ex.k n) e ⊢ G` | no goals |

**R12 · constructor injectivity (`Ex.sub.injEq`, applied by `simp` and `simp_all`)** changes the **goal**.
Lemma: `(Ex.sub a b = Ex.sub a' b') = (a = a' ∧ b = b')`. Lean generates one `injEq` lemma per constructor
(`Expr.plus.injEq`, …) and `simp` uses them without being told; `b = b` then becomes `True` and drops out.
Placeholders: `{a a' b : Ex}`.

| Before | After `simp` |
|---|---|
| `⊢ a.sub b = a'.sub b` | `⊢ a = a'` |

**R13 · `exact ih ‹_›`** **closes** the goal with the IH. `‹T›` means `by assumption` (a hypothesis of type `T`);
with `‹_›` Lean first computes `T` from `ih`'s premise and the goal (here `Red a a''`). Placeholders:
`{a a' a'' : Ex}`, `(ih : ∀ {e2 : Ex}, Red a e2 → a' = e2)`.

| Before | After |
|---|---|
| `h : Red a a'' ⊢ a' = a''` | no goals |

### Worked combinations (W1–W4, on the toy objects)

**W1.** Rules are constructors, so they build derivations: `.subL .subK` proves
`Red (.sub (.sub (.k 5) (.k 2)) (.k 1)) (.sub (.k 3) (.k 1))` (`5 - 2` computes to `3`).

**W2: inversion twice.** `Red (.dbl (.k 3)) e → e = .k 6`: R1, then R10 on `h` leaves `dblK` (closed by `rfl`) and
`dblC h'` with `h' : Red (.k 3) _`, closed by R2.

```lean-goal
⊢ Red (Ex.k 3).dbl e → e = Ex.k 6
⊢ e = Ex.k 6
```

**W3: progress for `dbl` alone.** R6 on the IH, then R7 (`⟨_, .dblK⟩`) or R8 (`⟨_, .dblC ha⟩`):

```lean-goal
⊢ ∃ e', Red a.dbl e'
⊢ ∃ e', Red (Ex.k m).dbl e'
```

**W4: one congruence case of determinism, for `dbl`.** With `ha : Red a a'` and the IH, `cases h2 <;> simp_all
[k_stuck]` (R10, R11, R12) kills `dblK` (there `ha` became a step out of `Ex.k _`) and reduces `dblC` to one
equation, which R13 closes:

```lean-goal
⊢ a'.dbl = e2
⊢ a' = a'✝
```

---

## Traps

- `induction h1` without `generalizing e2`: the IH is about the fixed `e2` and never applies (R9).
- `rcases … with ⟨m, rfl⟩` only substitutes when the left side of the equation is a local variable. Use it on the
  IH of the named argument `a` from `induction e with | plus a b iha ihb`.
- Split the IH of the **left** operand first. `plusR` only matches `.plus (.num m) b`: you need `a` to be a
  numeral before the right operand may step.
- `simp_all [num_stuck]` needs the name: `num_stuck` is a theorem, not a hypothesis, so plain `simp_all` will not
  see it. It may also leave the congruence goals `a' = a''` open; that is expected, finish them with the IH (R13).
- `t1 ; t2` runs `t2` on the first goal only. After `cases h2`, use `<;>` or `all_goals`.
- Merged alternatives `| plusL _ ih | plusR _ ih => …` must bind the same names in each rule.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `¬ A` | `intro h` | R1 |
| a step that no rule produces | `cases h` | R2 |
| induction on syntax, named | `induction e with \| num n => … \| plus a b iha ihb => …` | R3 |
| `(∃ m, x = x') ∨ B` by the left side | `exact .inl ⟨n, rfl⟩` | R4 |
| pick the right side of `∨` | `right` | R5 |
| split "numeral or steps", substitute | `rcases ih with ⟨m, rfl⟩ \| ⟨a', ha⟩` | R6 |
| `∃ e', Step e e'` by a computation rule | `exact ⟨_, .plusNum⟩` | R7 |
| `∃ e', Step e e'` by a congruence rule | `exact ⟨_, .plusL ha⟩` | R8 |
| induction on a derivation, IH for every target | `induction h1 generalizing e2 with …` | R9 |
| invert the other derivation | `cases h2` | R10 |
| kill rule pairs with a numeral that steps | `simp_all [num_stuck]` | R11 |
| `c a b = c a' b` → `a = a'` | `simp` / `simp_all` | R12 |
| finish with the IH | `exact ih ‹_›` | R13 |
| see the state | infoview | |
