# H023 · Small-step and big-step IMP agree: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): inductive types, `induction`/`cases` on `Nat` and lists,
`exact`, `rfl`, anonymous constructors `⟨_, _⟩`. **New here:** inductive *predicates* (relations defined
by rules, such as `BigStep`, `SmallStep`, `Star`), induction and case analysis on their derivations,
indices that are pairs (`generalize`), and inversion (`cases` on a derivation). No Mathlib.

The guide works on its own objects, not IMP:

| Guide object | Plays the role of | Definition |
|---|---|---|
| `Rtc r a c` | `Star p r` | zero or more `r`-steps from `a` to `c`; rules `refl (a)` and `step : r a b → Rtc r b c → Rtc r a c` |
| `Tm`, `Ev t v` | `Com`, `BigStep c s s'` | expressions `lit n`, `add a b`, `pick a b`; `Ev t v`: `t` evaluates to `v` (`pick` may take either side) |
| `Step t t'` | `SmallStep` | add two literals, or step inside the left operand of `add` |
| `Inc` on `Nat × Nat` | `SmallStep` on `Com × State` | `Inc (n, m) (n + 1, m)` |

## How to read an entry

Each entry is one tactic or one proof-term move. It says what changes (**goal**, **context**, or **goal
list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- A hypothesis that contains a pair, such as `hp : (a, b) = p`, is written in its own code span on the line
  above the `⊢` span (a `, ` inside it would otherwise read as a separator).
- `P` is "the rest of your goal". The step changes only what is shown; `hP` exists only to close the example.
- Placeholders are Lean binders: `{α β : Type}` any types, `r : α → α → Prop` any relation.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Com × State` | a *configuration*: a pair of a command and a state; `(c, s)` builds one |
| `State` | `Nat → Int`: variable number ↦ value (an `abbrev`, so Lean may print either) |
| `SmallStep p q` | configuration `p` becomes `q` in exactly one step |
| `Star p q` | `p` reaches `q` in zero or more `SmallStep`s |
| `BigStep c s s'` | running `c` from state `s` terminates in `s'` |
| `hb : beval s b = true` | the guard `b` holds in state `s` (`= false`: it fails); `beval`/`aeval` evaluate a `BExp`/`AExp` |
| `update s x v` | the state `s` with variable `x` set to `v` |
| leftover `p q : Com × State` | the variables `generalize` introduced, still in the context after `induction`; unused, ignore them |
| `c.seq c'` | `Com.seq c c'`. Lean prints `Com.f x …` as `x.f …` when the first explicit argument `x` is a `Com` |
| `Com.while b c`, `Com.ite b c1 c2` | printed in full: their first argument is a `BExp`, not a `Com` |
| `Com.skip` | the final command; `.skip` in your own code when the expected type is known |
| `a.add b`, `Tm.lit n` | guide: `Tm.add a b` (field notation as above), the literal `n` |
| `a✝`, `b✝`, `a✝¹`, `a✝²` | *inaccessible* names: fields that `induction`/`cases` introduced and you did not name. You cannot write them; name them in the pattern (R2, R3) |
| `case refl`, `case step` | the goal for that constructor. After several `cases`, tags chain: `case add.lit` |
| `ih : ∀ {a : α} {b : β}, (a, b) = y → …` | an induction hypothesis with generalized variables and an equation premise (R5) |

---

## Part 1 · `star_trans` (milestone)

Statement: `Star p q → Star q r → Star p r`. Induction on the first run; its indices `p q` are variables.

### Building derivations

**R1 · `refine .step hab ?_` / `exact .refl _`** changes the **goal**: it applies one rule (constructor) of
an inductive predicate. `.step` is `Rtc.step` (in the exercise `.step` is `Star.step`, `.seqStep` is
`SmallStep.seqStep`, `.seq` is `BigStep.seq`): Lean reads the type name off the expected type. Implicit
fields are found by unification with the goal, so `.step .whileUnfold (…)` needs no states written out.
Nested terms such as `.step st (ih h2)` build a whole run at once. Placeholders:
`{α : Type} (r : α → α → Prop) (a b c : α) (hab : r a b) (hbc : Rtc r b c)`.

| Before | After |
|---|---|
| `hab : r a b, hbc : Rtc r b c ⊢ Rtc r a c` | `⊢ Rtc r b c` |
| `⊢ Rtc r a a` | closed by `exact .refl _` |

### Induction on a derivation

**R2 · `induction h with | refl x => … | step hab hbc ih => …`** changes the **goal list**: one goal per
rule. Each goal gets the rule's fields; for each field that is itself a derivation (`hbc : Rtc r b c`)
there is an induction hypothesis `ih`. The pattern names the *explicit* fields, then the IHs, in order.
Implicit fields stay inaccessible (`a✝ b✝ c✝`). This works only when the indices of `h`'s type are
distinct variables. A hypothesis that mentions an index (as `h2 : Star q r` mentions `q` in star_trans)
is carried into every goal and into `ih`. Placeholders: `{α : Type} (r P : α → α → Prop) (a b : α) (h : Rtc r a b)`.
In big_to_small the same move on `h : BigStep c s s'` gives seven goals named after `BigStep`'s rules,
e.g. `| seq h1 h2 ih1 ih2 =>`.

| Before | After |
|---|---|
| `h : Rtc r a b ⊢ P a b` | `x : α ⊢ P x x`, `a✝ b✝ c✝ : α, hab : r a✝ b✝, hbc : Rtc r b✝ c✝, ih : P b✝ c✝ ⊢ P a✝ c✝` |

---

## Part 2 · `star_seq` (milestone)

Statement: a run of `c1` lifts to a run of `seq c1 c2` with the same states. Both indices of
`h : Star (c1, s) (c1', s')` are pairs, so `induction h` fails until they are generalized.

**R3 · `| @step x y z hxy hyz ih => …`** changes the **context**: with `@`, the pattern names *every*
field, implicit ones included, in declaration order (`_` skips one). For `Star.step {p q r}` that is
`p q r`, the step, the rest, the IH: `| @step _ q' _ st _ ih` names the middle configuration `q'`.
Placeholders as R2.

| Before | After |
|---|---|
| `h : Rtc r a b ⊢ P a b` | `x : α ⊢ P x x`, `x y z : α, hxy : r x y, hyz : Rtc r y z, ih : P y z ⊢ P x z` |

**R4 · `generalize hp : (a, b) = p at h`** changes the **context**: every `(a, b)` in `h` becomes a fresh
variable `p`, and `hp` records the equation. Do it once per compound index (source, then target).
Placeholders: `{α β : Type} (r : α × β → α × β → Prop) (a : α) (b b' : β)`.

| Before | After |
|---|---|
| `h : Rtc r (a, b) (a, b')`<br>`⊢ P` | `hp : (a, b) = p`<br>`h : Rtc r p (a, b')`<br>`p : α × β ⊢ P` |

**R5 · `induction h generalizing a b with …`** changes the **context**: the hypotheses `hp` (and `hq`) mention
the indices, so they are carried into each goal and become premises of `ih`. `generalizing a b` makes `ih`
hold for *all* `a b`, which is what lets it apply at the middle point `y = (c, t)`, not at the start
`(a, b)`. Without it, `ih` only speaks about the original `(a, b)`. Placeholders:
`{α β : Type} (r : α × β → α × β → Prop) (P : α → β → Prop) (p q : α × β) {a : α} {b : β}`.

| Before | After |
|---|---|
| `hp : (a, b) = p`<br>`h : Rtc r p q ⊢ P a b` | `hp : (a, b) = x`<br>`x : α × β ⊢ P a b`, `ih : ∀ {a : α} {b : β}, (a, b) = y → P a b`<br>`hp : (a, b) = x`<br>`hxy : r x y, hyz : Rtc r y z ⊢ P a b` |

### Cleaning up equations between pairs

**R6 · `subst hp`** (or `cases hp`) with `hp : e = x` and `x` a variable changes the **context**: `x` is
replaced by `e` everywhere and `hp` disappears. Placeholders:
`{α β : Type} (r : α × β → α × β → Prop) (a : α) (b : β) (x y : α × β)`.

| Before | After |
|---|---|
| `hp : (a, b) = x`<br>`hxy : r x y ⊢ P x` | `hxy : r (a, b) y`<br>`⊢ P (a, b)` |

**R7 · `cases h`** with `h : (a, b) = (a', b')` changes the **context**: `Prod.mk` is a constructor, so the
pair equation splits into `a = a'` and `b = b'`, and both are substituted (here `a' b'` disappear). A
component that is a constructor application (`Com.assign x a = c`) is substituted the same way; two
different constructors (`Com.skip = Com.seq …`) close the goal as impossible. In step_then_big,
`hp : (c, s) = (Com.assign x✝ a✝, s✝)` replaces `c` by `Com.assign x✝ a✝` and `s` by `s✝`. Placeholders:
`{α β : Type} (a a' : α) (b b' : β)`.

| Before | After |
|---|---|
| `h : (a, b) = (a', b')`<br>`hP : P a b ⊢ P a' b'` | `hP : P a b ⊢ P a b` |

**R8 · `obtain ⟨x, y⟩ := q`** changes the **context**: the pair variable `q` is replaced by `(x, y)` in every
hypothesis and the goal. Needed so that `ih`'s premise `(a, b) = q'` can become `(a, b) = (c, t)`.
Placeholders: `{α β : Type} (r : α × β → α × β → Prop) (p q : α × β)`.

| Before | After |
|---|---|
| `hpq : r p q ⊢ P q` | `hpq : r p (x, y)`<br>`x : α, y : β ⊢ P (x, y)` |

**R9 · `ih rfl`** discharges an equation premise of `ih`: the implicit `a b` of `ih` are solved by
unifying `(?a, ?b) = (x, y)`, and `rfl` proves it. In the exercise: `ih rfl hq` (the target equation `hq`
is passed through unchanged). Placeholders: `{α β : Type} (P : α → β → Prop) (x : α) (y : β)`.

| Before | After `have h := ih rfl` |
|---|---|
| `⊢ P x y` (with `ih : ∀ {a : α} {b : β}, (a, b) = (x, y) → P a b`) | `h : P x y ⊢ P x y` |

---

## Part 3 · `step_then_big` (milestone)

Statement: `SmallStep (c, s) (c', s') → BigStep c' s' t → BigStep c s t`: a big-step run survives adding one
small step in front. Generalize (R4), induction on the step generalizing `c c' s s' t` (R5), `cases hp;
cases hq` (R7 twice: after the induction both sides of `hp`, `hq` are pairs), then *invert* `h2`.
The `seqStep` goal right after the induction (copied from Lean); note that `ih` takes a big-step run
*first*, then the two equations:

```
ih : ∀ {c c' : Com} {s s' t : State}, BigStep c' s' t → (c, s) = (c1✝, s✝) → (c', s') = (c1'✝, s'✝) → BigStep c s t
h2 : BigStep c' s' t
hp : (c, s) = (c1✝.seq c2✝, s✝)
hq : (c', s') = (c1'✝.seq c2✝, s'✝)
⊢ BigStep c s t
```

### Inversion: `cases` on a derivation whose index is a constructor

`cases h` on a derivation `h` keeps only the rules whose conclusion can match `h`'s indices, and
substitutes what the match forces. This is how you learn what `BigStep (c1.seq c2) s t` must have come from.

**R10 · `cases h`, one rule fits, no premises** changes the **context**: `h` disappears and the index it
fixed is substituted (`v := n`). In the exercise: `cases h2` on `h2 : BigStep Com.skip s t` replaces `t` by `s`.
Placeholders: `(P : Nat → Prop) (n v : Nat)`.

| Before | After |
|---|---|
| `h : Ev (Tm.lit n) v, hP : P n ⊢ P v` | `hP : P n ⊢ P n` |

**R11 · `cases h with | add ha hb => …`** changes the **context**: only `Ev.add` fits the index `.add a b`;
its premises arrive as `ha hb`, and the value becomes `m✝ + n✝`. In the exercise: `cases h2 with | seq h21
h22 => …` on `h2 : BigStep (c1.seq c2) s t`. Placeholders: `(P : Nat → Prop) (a b : Tm) (v : Nat)`.

| Before | After |
|---|---|
| `h : Ev (a.add b) v ⊢ P v` | `m✝ n✝ : Nat, ha : Ev a m✝, hb : Ev b n✝ ⊢ P (m✝ + n✝)` |

**R12 · `cases h with | pickL h => … | pickR h => …`** changes the **goal list**: two rules fit, one goal
each. In the exercise: `h2 : BigStep (Com.ite b …) s t` splits into `iteT` and `iteF`. Placeholders as R11.

| Before | After |
|---|---|
| `h : Ev (a.pick b) v ⊢ P v` | `h : Ev a v ⊢ P v`, `h : Ev b v ⊢ P v` |

**W1: inversion twice, then compute** (R11, R10, R10) on `h : Ev (.add (.lit 1) (.lit 2)) v`:

```lean-goal
⊢ v = 3
⊢ m✝ + n✝ = 3
⊢ 1 + n✝ = 3
⊢ 1 + 2 = 3
```

**W2: the shape of step_then_big on `Tm`.** `Step t t' → Ev t' v → Ev t v` by
`induction hs generalizing v` (R2): `v` must be general because stepping inside `add` changes the value of
the operand. The two goals:

```lean-goal
⊢ Ev ((Tm.lit m✝).add (Tm.lit n✝)) v
⊢ Ev (a✝¹.add b✝) v
```

The first: `cases he` (R10), then `exact .add .lit .lit` (R1). The second has
`ih : ∀ {v : Nat}, Ev a'✝ v → Ev a✝¹ v`: `cases he with | add ha hb` (R11), then `.add (ih ha) hb` (R1).
The exercise's `whileUnfold` case is R12 followed by R11 or R10.

---

## Part 4 · `big_to_small`

Statement: `BigStep c s s' → Star (c, s) (Com.skip, s')`. Induction on `h` (R2); every case is a term built
from rules (R1) and the milestones. The `whileT` goal, as Lean shows it:

```
ih1 : Star (c✝, s✝) (Com.skip, s'✝)
ih2 : Star (Com.while b✝ c✝, s'✝) (Com.skip, s''✝)
⊢ Star (Com.while b✝ c✝, s✝) (Com.skip, s''✝)
```

`whileUnfold` turns `Com.while b c` into `Com.ite b (c.seq (Com.while b c)) Com.skip`; `iteT hb` picks
the first branch; then `c` runs inside `seq _ (Com.while b c)` (star_seq ih1), `seqSkip` drops the finished
`skip`, and `ih2` finishes. star_trans joins the two runs.

---

## Part 5 · `small_to_big`

Statement: `Star (c, s) (Com.skip, s') → BigStep c s s'`. Same opening as star_seq: R4 twice (write
`Com.skip` in the target), R5 with R3. The step case after `subst hp; obtain ⟨c', t⟩ := q'` (R6, R8):

```
ih : ∀ {c : Com} {s : State}, (c, s) = (c', t) → (Com.skip, s') = r✝ → BigStep c s s'
st : SmallStep (c, s) (c', t)
⊢ BigStep c s s'
```

`ih rfl hq : BigStep c' t s'` (R9), and step_then_big puts `st` in front.

**W3: the whole pattern on `Inc`** (`Rtc Inc (n, m) (n', m') → m' = m`): R4 twice, R5 with R3, then refl
by R6 and R7, step by R6, R8, inversion `cases hxy` (R10), and `ih rfl hq` (R9). The step goal right after
the induction:

```
ih : ∀ {n m : Nat}, (n, m) = y → (n', m') = z → m' = m
hp : (n, m) = x
hq : (n', m') = z
⊢ m' = m
```

---

## Traps

- `induction h` with `h : Star (c, s) (Com.skip, s')` fails: "Index in target's type is not a variable".
  Generalizing only one side still fails on the other (R4 twice).
- Inside `generalize`, write `Com.skip`, not `.skip`: `generalize` elaborates `(…, s')` with no expected
  type, so `.skip` gives "Invalid dotted identifier notation: The expected type of `.skip` could not be
  determined".
- Forgetting `generalizing c s` leaves `ih : (c, s) = q' → …` about the *starting* configuration; it can
  never be applied at the middle one.
- In step_then_big, generalize `t` (and `c' s'`) too: in `seqStep` the IH is used with a different `h2`.
- `ih` needs `q'` split first (R8): `ih rfl` cannot prove `(c, s) = q'` for a variable `q'`.
- In step_then_big's `seqStep` case, `ih rfl rfl h21` fails: the run comes first, `ih h21 rfl rfl`.
- The holes of big_to_small and small_to_big come right after `:=` (a term is expected): start with
  `by` to use tactics.
- Inaccessible names (`a✝`) cannot be typed: name fields in the pattern, with `@` for implicit ones (R3).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| use one rule | `exact .step st rest`, `refine .step st ?_`, `exact .refl _` | R1 |
| induction on a run with variable indices | `induction h with \| refl x => … \| step h1 h2 ih => …` | R2 |
| name implicit fields | `\| @step _ q' _ st _ ih => …` | R3 |
| pair index → variable | `generalize hp : (c, s) = p at h` | R4 |
| IH for every start | `induction h generalizing c s` | R5 |
| `hp : e = x` → substitute | `subst hp` / `cases hp` | R6 |
| `(a, b) = (a', b')` → substitute both | `cases h` | R7 |
| split a pair variable | `obtain ⟨c, t⟩ := q` | R8 |
| equation premise of `ih` | `ih rfl hq` | R9 |
| invert a run, one rule fits | `cases h2` | R10 |
| invert, name the premises | `cases h2 with \| seq h1 h2 => …` | R11 |
| invert, several rules fit | `cases h2 with \| iteT hb h => … \| iteF hb h => …` | R12 |
| join two runs | `star_trans h1 h2` | milestone |
| see the state | infoview | |
