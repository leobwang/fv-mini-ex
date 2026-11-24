# M005 · Reflexive-transitive closure: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `inductive`, `theorem`, `intro`, `exact`, `have`, `rw`,
`induction`/`cases` on `Nat`, `omega`, `∧`/`∨`/`¬`/`↔`. **New here:** an *inductive relation*
(`inductive … : α → α → Prop` whose constructors are inference rules), building derivations from
constructors, induction on a *derivation*, automatic generalization of hypotheses into the induction
hypothesis (IH), relations written as `fun`, `subst`, `by_cases`. Core Lean only, no Mathlib.

## The objects

- **`Star R a b`** (spec), for `R : α → α → Prop` (a binary relation on a type `α`). Write `a → b` for
  `R a b`. Two rules:
  - `Star.refl (a : α) : Star R a a`: the empty path (zero steps);
  - `Star.step : R a b → Star R b c → Star R a c`: one step `a → b` in FRONT of a path from `b`.

  So `Star R a b` says `a → x₁ → … → xₖ → b` for some `k ≥ 0`: the *reflexive-transitive closure* of `R`.
  `R` is a **parameter** (fixed, written before the `:`); the two points after the `:` are **indices**
  (they vary between rules), which is why induction on a derivation replaces them.
- **Holes:** `star_single` (`R a b → Star R a b`), `star_trans` (paths compose), `star_succ_iff`
  (for `R n m := m = n + 1`, `Star R a b ↔ a ≤ b`).
- The guide teaches on a toy relation that is **not** `Star`:

```lean
inductive EvenPath {α : Type} (r : α → α → Prop) : α → α → Prop   -- a reaches d in an EVEN number of steps
  | nil (a : α) : EvenPath r a a
  | two {a b c d : α} : r a b → r b c → EvenPath r c d → EvenPath r a d
```

## How to read an entry

Each entry is one tactic or one term-building move. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change. `∅`
  means no goal is left.
- `P`, `Q`, `G` are "the rest of your goal": `Q : α → Prop`, `P : Nat → Prop`, or `G : Prop`.
- Placeholders are written as Lean binders: `{α : Type}` is any type; `(r : α → α → Prop)` is a binary
  relation; `(A B G : Prop)` are propositions; `(p : EvenPath r a b)` is a derivation.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Star R a b` | a derivation of `a →* b`: `.refl a` (then `b` is `a`) or `.step h p` with `h : R a x`, `p : Star R x b` |
| `.refl a`, `.step h p` | `Star.refl a`, `Star.step h p`: a leading `.` takes the constructor from the expected type |
| `{a b c : α}` in a constructor | implicit arguments: Lean infers them; you never write them |
| `(fun n m => m = n + 1) a b` | the relation applied to `a`, `b`: it means `b = a + 1` (β-reduction). Hypotheses are usually printed reduced (`hab : b✝ = a✝¹ + 1`) |
| `a✝`, `b✝¹`, `a_ih✝` | names Lean invented (after `induction`, for implicit points or a skipped `_`); you cannot type them. The superscript tells apart several with the same base name (`a✝`, `a✝¹`, …). Name them with `with` (R4) or `next` (R3) |
| `ih : Star R c✝ c → Star R b✝ c` | an IH with a premise: a generalized hypothesis (here `h2`) became its argument (R3, R5) |
| `case refl`, `case step` | the goal for one constructor; `case mp.step` = direction `mp` of `↔`, then constructor `step` |
| `case mp`, `case mpr` | the `→` and `←` directions of an `↔` after `constructor` (R6) |
| `case pos`, `case neg` | the two goals of `by_cases`: the fact holds / does not hold (R10) |
| `¬a = b + 1` | `a = b + 1 → False` (printed without a space after `¬`) |

---

## Part 1 · `star_single`

Statement: `R a b → Star R a b`. One step `h`, then the empty path at `b`: a term built from two
constructors (R2 with R1 as its last argument).

**R1 · `exact .nil a`** **closes** the goal with the constructor that has no premise. `.nil a` means
`EvenPath.nil a`; `a` is an explicit argument (written `( )` in the constructor), so give it or write `_`.
Placeholders: `{α : Type} (r : α → α → Prop) (a : α)`. For `Star` the same move is `.refl a`.

| Before | After |
|---|---|
| `⊢ EvenPath r a a` | `∅` |

**R2 · `exact .two s t p`** **closes** the goal with a constructor that has premises. The constructor is a
function from its premises to its conclusion; the points `{a b c d}` are implicit and read off the
arguments. Arguments nest: `.two s t (.nil c)` is a path of exactly two steps. Placeholders:
`(a b c d : α) (s : r a b) (t : r b c) (p : EvenPath r c d)`. For `Star`: `.step h p`.

| Before | After |
|---|---|
| `p : EvenPath r c d ⊢ EvenPath r a d` | `∅` |
| `t : r b c ⊢ EvenPath r a c` | `∅` |

---

## Part 2 · `star_trans` (milestone)

Statement: `Star R a b → Star R b c → Star R a c`. Induct on the first derivation `h1` (R3, R4). In
`refl` the second path is already the goal. In `step` the IH takes `h2` and returns a path from the
middle point; put the step in front (R5, R2). `star_succ_iff` uses this lemma.

**R3 · `induction p`** (`p : EvenPath r a b`) changes the **goal list and the context**: one goal per
constructor, with the indices `a`, `b` replaced by that constructor's pattern. A hypothesis that mentions
an index (`hb : Q b`) is **generalized**: it reappears in each goal with the new index, and in the IH as a
premise. Placeholders: `(Q : α → Prop) (a b : α) (p : EvenPath r a b) (hb : Q b)`. The `✝` names cannot
be typed; the guide reaches them with `next x₁ … xₖ => tac`, which works on the first goal and names its
last `k` inaccessible variables. R4 (`with`) is the usual way.

| Before | After |
|---|---|
| `hb : Q b ⊢ Q a` | `hb : Q a✝ ⊢ Q a✝`, `a_ih✝ : Q d✝ → Q c✝, hb : Q d✝ ⊢ Q a✝³` |

**R4 · `induction p with | nil x => ?_ | two s t q ih => ?_`** does the same with names. After the
constructor name come, in order, its **explicit** arguments (`nil x`: the point; `two s t q`: the three
premises; the implicit points keep `✝` names), then one IH per premise of the relation's own type.
`_` skips a name. In practice a tactic block follows `=>` instead of `?_`.

| Before | After |
|---|---|
| `hb : Q b ⊢ Q a` | `x : α, hb : Q x ⊢ Q x`, `q : EvenPath r c✝ d✝, ih : Q d✝ → Q c✝, hb : Q d✝ ⊢ Q a✝` |

**R5 · `ih h`** uses an IH with a premise: `ih : A → B` is a function, `ih h : B`. Here `have hb := ih h`
changes the **context**; in the exercise you pass `ih h2` straight to a constructor. Placeholders:
`(A B G : Prop) (ih : A → B) (h : A)`.

| Before | After |
|---|---|
| `ih : A → B, h : A ⊢ G` | `hb : B ⊢ G` |

**W1** in the guide composes two `EvenPath`s exactly this way (induct on the first path, the second rides
along into `ih`, close with R2 and R5).

---

## Part 3 · `star_succ_iff`

Statement: for the successor relation `R n m := m = n + 1`, `Star R a b ↔ a ≤ b`.

- **→** induct on the derivation (R4); each case is arithmetic (R7): `refl` gives `a✝ ≤ a✝`; `step`
  gives `hab : b✝ = a✝¹ + 1`, `ih : b✝ ≤ c✝`, goal `a✝¹ ≤ c✝`.
- **←** there is no derivation to induct on, so induct on the number `b` (R8); `h : a ≤ b` moves into
  the IH. `zero`: `a = 0` (R7), `subst` (R9), `refl` (R1). `succ`: `by_cases` on `a = b + 1` (R10);
  equal: `subst`, `refl`; not equal: `star_trans` of `ih` fed `a ≤ b` (R5, R12) and the one-step path
  `star_single` whose premise is `rfl` (R11).

**R6 · `constructor`** on `A ↔ B` changes the **goal list**: one goal per direction, cases `mp` (`→`) and
`mpr` (`←`). Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R7 · `omega`** **closes** a goal of linear arithmetic over `Nat` or `Int` (`+`, `-`, `*` by a literal,
`=`, `≤`, `<`, `≠`, `¬`, `∧`, `∨`), using the hypotheses in the context. A hypothesis given as
`(fun n m => m = n + 2) y z` is printed (and used) as `z = y + 2`. Placeholders: `(x y z : Nat)`.

| Before | After |
|---|---|
| `s : z = y + 2, h : x ≤ y ⊢ x ≤ z` | `∅` |

**R8 · `induction b`** on a number, with `h : a ≤ b` in the context, changes the **goal list and the
context**. As in R3, `h` is generalized: `zero` gets `h : a ≤ 0`; `succ` gets `h : a ≤ n✝ + 1` and an IH
that first needs `a ≤ n✝`. Name them with `induction b with | zero => … | succ n ih => …`. Placeholders:
`(Q : Nat → Prop) (a b : Nat) (h : a ≤ b)`.

| Before | After |
|---|---|
| `h : a ≤ b ⊢ Q b` | `h : a ≤ 0 ⊢ Q 0`, `a✝ : a ≤ n✝ → Q n✝, h : a ≤ n✝ + 1 ⊢ Q (n✝ + 1)` |

**R9 · `subst h`** (`h : x = t` or `h : t = x`, with `x` a local variable not occurring in `t`) changes the
**context and the goal**: `x` and `h` disappear, every `x` becomes `t`. Placeholders:
`(P : Nat → Prop) (x : Nat) (h : x = 0)`.

| Before | After |
|---|---|
| `h : x = 0 ⊢ P x` | `⊢ P 0` |

**R10 · `by_cases h : A`** changes the **goal list**: two copies of the goal, `pos` with `h : A` and `neg`
with `h : ¬A`. Placeholders: `(A G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h : A ⊢ G`, `h : ¬A ⊢ G` |

**R11 · `rfl`** **closes** `(fun n m => m = n + 2) x (x + 2)`: substituting `x`, `x + 2` into the body
(β-reduction, which Lean does silently) gives `x + 2 = x + 2`. So `rfl` is one step of such a relation,
usable as a constructor argument: `.two rfl rfl (.nil (x + 4))`. Placeholders: `(x : Nat)`.

| Before | After |
|---|---|
| `⊢ (fun n m => m = n + 2) x (x + 2)` | `∅` |

**R12 · `f (by omega)`** **closes** the goal `B` with `f : a ≤ n → B`, proving the premise `a ≤ n` inline:
`(by tac)` is a term elaborated against the premise's type, here from `h : a ≤ n + 1` and
`hne : ¬a = n + 1`. Placeholders: `(B : Prop) (a n : Nat)`.

| Before | After |
|---|---|
| `h : a ≤ n + 1, hne : ¬a = n + 1, f : a ≤ n → B ⊢ B` | `∅` |

**W2–W4** in the guide: a `+ 1` path only goes up (R4, R7); the concrete path
`.two rfl rfl (.nil 2) : EvenPath (fun n m => m = n + 1) 0 2` (R2, R11, R1); and reusing the W1 lemma as a
function with a freshly built path as one argument.

---

## Traps

- Induct on the derivation `h1`, not on a point: `Star` has no structure on `α` to induct on. Induction
  works because the indices of `h1` are plain variables; a hypothesis mentioning them (`h2`) is
  generalized for you; no `revert` needed. Induct on `h1`, not `h2`: `step` adds steps at the front, so
  inducting on `h2` leaves you appending one step at the END of `h1`, which needs another lemma.
- In `←` there is no derivation yet: induct on the number `b`, the end point of the path you build.
- `ih` in `←, succ` has a premise: `ih : a ≤ b → Star … a b`. Feed it `(by omega)` (R12); `exact ih` fails.
- `subst` needs a variable on one side: `subst this` with `this : a = 0` works, `h : a + 1 = 1` does not.
  State the fact as `a = 0` first (R7).
- `.refl` takes the point explicitly: `.refl 0` or `.refl _`, never bare `.refl`.
- `t1 ; t2` runs `t2` on the first goal only. Use `with | … => …` or `·` per goal after `induction`,
  `constructor`, `by_cases`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| the empty path | `.refl a` / `.refl _` | R1 |
| one step in front of a path | `.step h p` | R2 |
| induct on a derivation | `induction h1 with \| refl _ => … \| step hab _ ih => …` | R3, R4 |
| use an IH with a premise | `ih h2`, `ih (by omega)` | R5, R12 |
| split `A ↔ B` | `constructor` | R6 |
| linear `Nat` arithmetic | `omega` | R7 |
| induct on a number, hypothesis along | `induction b with \| zero => … \| succ b ih => …` | R8 |
| replace a variable by its value | `subst h` | R9 |
| case split on a fact | `by_cases hab : a = b + 1` | R10 |
| one step of a `fun` relation | `rfl` | R11 |
| compose lemmas | `star_trans p q`, `star_single h` | R2, R5 |
| see the state | infoview | |
