# H021 · IMP big-step semantics: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `intro` on a `¬` goal (E008), `cases` with
named alternatives (E016, E018), `injection` and constructor clashes (E029), `simp_all`, `<;>`.
No Mathlib, no imports. **New here:** inductive *relations* (an `inductive … : A → B → C → Prop`
whose constructors are inference rules), induction on a derivation (*rule induction*), `generalizing`,
inversion with `cases`, `generalize … at`, `subst`, and `h ▸ e`.

The guide's entries run on a toy language, not on `Com`/`BigStep`:

```lean
inductive Op where | done | bump (n : Nat) | then_ (p q : Op) | spin (p : Op)
inductive Run : Op → Nat → Nat → Prop      -- Run p x y : program p takes counter x to y
  | done  : Run .done x x
  | bump  : Run (.bump n) x (x + n)
  | then_ : Run p x y → Run q y z → Run (.then_ p q) x z
  | spin  : Run p x y → Run (.spin p) y z → Run (.spin p) x z   -- loops forever, like `while true`
```

`Run ↔ BigStep`, `Op.then_ ↔ Com.seq` / `Com.ite`, `Op.spin ↔ Com.while`, counter `Nat ↔ State`.

## How to read an entry

Each entry is one tactic (or the term `h ▸ e`). It says what changes (**goal**, **context**, or **goal
list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`, `P : Op → Nat → Nat → Prop`, …). `H` is a
  hypothesis that only finishes the example.
- A *derivation* `h : Run p x y` is a proof built from the constructors (rules) of `Run`; `p x y` are
  its *indices*. Induction and `cases` on `h` go over the rules that could have built it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `State` | `Nat → Int`: variable number `x` ↦ its value `s x` |
| `BigStep c s s'` | running command `c` from state `s` terminates in state `s'` |
| `.skip`, `.seq c1 c2` | `Com.skip`, `Com.seq c1 c2`: the type is known, so the prefix is dropped |
| `c1.seq c2`, `p.spin` | field notation: `Com.seq c1 c2`, `Op.spin p` (the first explicit argument, which has type `Com`/`Op`, moved in front) |
| `Com.while BExp.tt c`, `Com.ite b c1 c2`, `Com.assign 0 (AExp.num 1)` | printed in full: the first explicit argument is a `BExp` or a `Nat`, not a `Com`, so no field notation |
| `hb a✝ : beval s✝ b✝ = false` | two hypotheses `hb` and `a✝` with the same type, printed on one line |
| `(AExp.var 0).plus (AExp.num 1)` | `AExp.plus (AExp.var 0) (AExp.num 1)`, i.e. `x0 + 1` |
| `s✝`, `c1✝`, `a✝¹`, `y✝` | *inaccessible* names Lean invented; you cannot type them. Name them with `with \| rule h1 h2 =>` |
| `a_ih✝`, `a_ih✝¹` | unnamed induction hypotheses; `✝¹` is older than `✝` |
| `case seq`, `case iteT.iteF` | goal tags: rule `seq`; outer case `iteT`, inner `cases` case `iteF` |
| `∀ {s2 : State}, BigStep c s s2 → …` | a generalized IH: `ih h'` fills `s2` from the type of `h'` |
| `beval s b = true` | a `Bool` equation (not a `Prop`): the guard `b` evaluates to `true` in `s` |
| `decide (a ≤ b)`, `!b`, `b1 && b2` | `Bool` versions of `≤`, `¬`, `∧` |
| `update s x v` | the state `s` with variable `x` set to `v` |
| `h ▸ e` | `e` with its type rewritten by the equation `h` |

---

## Part 1 · `bigstep_det`

Statement: if `c` runs from `s` to `s1` and also from `s` to `s2`, then `s1 = s2`: evaluation is
deterministic. Induct on the first derivation; in each rule, invert the second one.

**R1 · `induction h`** changes the **goal list**: one goal per constructor (rule) of `Run`, with the rule's
indices in place of `p x y`. Each premise of the rule that is itself a `Run` derivation gets an induction
hypothesis (`a_ih✝`). The indices of `h` must be variables (R7 otherwise). Placeholders:
`(P : Op → Nat → Nat → Prop) {p : Op} {x y : Nat} (h : Run p x y)`.

| Before | After |
|---|---|
| `h : Run p x y ⊢ P p x y` | `⊢ P Op.done x✝ x✝`, `⊢ P (Op.bump n✝) x✝ (x✝ + n✝)`, `a_ih✝¹ : P p✝ x✝ y✝, a_ih✝ : P q✝ y✝ z✝ ⊢ P (p✝.then_ q✝) x✝ z✝`, `a_ih✝¹ : P p✝ x✝ y✝, a_ih✝ : P p✝.spin y✝ z✝ ⊢ P p✝.spin x✝ z✝` |

Name the pieces with `induction h with | then_ h1 h2 ih1 ih2 => …`: the rule's premises first (all of
them, `Bool` guards included), then one IH per `Run` premise. Implicit arguments `{…}` get no name.

**R2 · `induction h generalizing z`** changes the **goal list** as R1, but every IH is quantified over `z`
(and over hypotheses that mention `z`, such as `h2`). Without it, the IH speaks only about the one `z`
you started with, which is useless once the middle value changes. Placeholders:
`(P : Nat → Nat → Prop) {p : Op} {x y z : Nat} (h : Run p x y) (h2 : Run p x z)`.

| Before | After (case `then_`) |
|---|---|
| `h : Run p x y, h2 : Run p x z ⊢ P y z` | `h2 : Run (p✝.then_ q✝) x✝ z ⊢ P z✝ z` |

with the two IHs `a_ih✝¹ : ∀ {z : Nat}, Run p✝ x✝ z → P y✝ z` and
`a_ih✝ : ∀ {z : Nat}, Run q✝ y✝ z → P z✝ z`. The other cases: `h2 : Run Op.done x✝ z ⊢ P x✝ z` and
`h2 : Run (Op.bump n✝) x✝ z ⊢ P (x✝ + n✝) z`. Without `generalizing z` the `then_` IH is
`a_ih✝¹ : Run p✝ x✝ z → P y✝ z` for the fixed `z`.

**R3 · `cases h` (inversion)** changes the **goal list and the goal**. `h`'s program is a constructor
(`.bump n`), so only the rules whose conclusion can match survive, here one, and Lean unifies the
indices: `y` becomes `x + n` everywhere. Placeholders: `(P : Nat → Prop) {n x y : Nat}
(h : Run (.bump n) x y)`.

| Before | After |
|---|---|
| `h : Run (Op.bump n) x y ⊢ P y` | `⊢ P (x + n)` |

In `bigstep_det`, after `induction h1`, the second derivation `h2 : BigStep (…) s s2` has a constructor
as its command in every case, so `cases h2` leaves one case (`skip`, `assign`, `seq`) or two (`ite …`:
`iteT` and `iteF`; `while …`: `whileF` and `whileT`). In `skip` and `assign` the goal becomes `a = a`:
`rfl`.

**R4 · `cases h` on a rule with premises** changes the **context**: `h` is replaced by the rule's premises
and the middle value `y✝` they share. Write `cases h with | then_ h1 h2 => …` to name them.
Placeholders: `(P : Nat → Prop) {p q : Op} {x z : Nat} (h : Run (.then_ p q) x z)`.

| Before | After |
|---|---|
| `h : Run (p.then_ q) x z ⊢ P z` | `y✝ : Nat, a✝¹ : Run p x y✝, a✝ : Run q y✝ z ⊢ P z` |

**R5 · `h ▸ e`** is a **term** that closes the goal: if `h : a = b` and `e : P a`, then `h ▸ e : P b`. Lean
rewrites the type of `e` with `h` in whichever direction matches the expected type, so the expected type
must be known (use it after `exact`, or as an argument). Placeholders: `(P : Nat → Prop) {a b : Nat}`.

| Before | After |
|---|---|
| `h : a = b, e : P a ⊢ P b` | no goals |

In the `seq` case, `ih1 h1'` is an equation between the two middle states, and
`ih1 h1' ▸ h2'` turns `h2'` (which starts at the second middle state) into a derivation from the first,
which `ih2` accepts. `whileT` is the same.

**R6 · `simp_all`** **closes** the goal when two hypotheses say `f x = true` and `f x = false`: it rewrites
one with the other to `true = false`, i.e. `False`. Placeholders: `(P : Prop) (f : Nat → Bool) (x : Nat)`.

| Before | After |
|---|---|
| `h1 : f x = true, h2 : f x = false ⊢ P` | no goals |

This is how `cases h2` cases with the wrong branch end (`iteT` against `iteF`, `whileF` against `whileT`):
`hb : beval s✝ b✝ = true` and `hb' : beval s✝ b✝ = false`.

### Worked combinations

**W1** (R1): `induction h with | then_ _ _ ih1 ih2 => omega | …` proves `Run p x y → x ≤ y`.
**W2** (R4, R5): two runs of `.then_ p q` from `x`: `cases` both, then `hq a2 (hp a1 b1 ▸ b2)`.

---

## Part 2 · `while_true_diverges`

Statement: no derivation `BigStep (.while .tt c) s s'` exists: `while true do c` never terminates. `¬ A`
is `A → False`, so `intro h` first (E008). The proof is an induction on `h`, but its command is not a
variable.

**R7 · `generalize hw : e = w at h`** changes the **context**: the expression `e` inside `h` is replaced by a
new variable `w`, and `hw : e = w` remembers it. Plain `induction h` on `h : Run (.spin p) x y` fails with
"Index in target's type is not a variable". Placeholders: `(p : Op) {x y : Nat}
(h : Run (.spin p) x y)`. In the problem write the command in full: `Com.while BExp.tt c`.

| Before | After |
|---|---|
| `h : Run p.spin x y ⊢ False` | `w : Op, hw : p.spin = w, h : Run w x y ⊢ False` |

**R8 · `induction h` with `hw : e = w` in the context** changes the **goal list**: Lean takes `hw` along
into every case (with `w` replaced by that rule's program) and into every IH as a premise
`e = … → …`. Placeholders: `(P : Prop) (p w : Op) {x y : Nat} (h : Run w x y) (hw : Op.spin p = w)`.

| Before | After |
|---|---|
| `h : Run w x y, hw : p.spin = w ⊢ P` | `hw : p.spin = Op.done ⊢ P`, `hw : p.spin = Op.bump n✝ ⊢ P`, `a_ih✝ : p.spin = q✝ → P, hw : p.spin = p✝.then_ q✝ ⊢ P`, `a_ih✝ : p.spin = p✝.spin → P, hw : p.spin = p✝.spin ⊢ P` |

So in the problem: in `skip`, `assign`, `seq`, `iteT`, `iteF` the `hw` is a clash (R12); in `whileT` the
last IH takes `hw` itself (`exact ih2 hw`); in `whileF` the guard must be `BExp.tt` (R9–R11). Write
`induction h with | whileF hb => … | whileT _ _ _ _ ih2 => … | _ => …`: `| _ =>` covers every rule
not listed.

**R9 · `injection hw with h1 h2`** changes the **context**: an equation between the same constructor
becomes equations between the arguments (E029). Placeholders: `(p q p' q' : Op)`.

| Before | After |
|---|---|
| `hw : p.then_ q = p'.then_ q' ⊢ P` | `h1 : p = p', h2 : q = q' ⊢ P` |

**R10 · `subst h1`** changes the **context**: for `h1 : a = b` with `b` a local variable, `b` is replaced by
`a` in every hypothesis and the goal, and `b` and `h1` disappear. Here it turns the guard `b✝` into
`BExp.tt` inside `hb`. Placeholders: `(P : Op → Prop) (a b : Op)`.

| Before | After |
|---|---|
| `h1 : a = b, hb : P b ⊢ P a` | `hb : P a ⊢ P a` |

**R11 · `simp [f] at hb`** **closes** the goal when `hb` simplifies to `False`: `simp` unfolds `f`, computes
`isDone Op.done` to `true`, and `true = false` is `False`. In the problem, `simp [beval] at hb` on
`hb : beval s✝ BExp.tt = false`. Without `[beval]` it fails ("`simp` made no progress"). Placeholders: `(P : Prop)`,
the guide's `isDone : Op → Bool`.

| Before | After |
|---|---|
| `hb : isDone Op.done = false ⊢ P` | no goals |

**R12 · `cases hw`** **closes** the goal when `hw` equates two different constructors: no case survives.
(`nomatch hw` and `simp at hw` work too.) Placeholders: `(P : Prop) (p : Op) (n : Nat)`.

| Before | After |
|---|---|
| `hw : p.spin = Op.bump n ⊢ P` | no goals |

**W3** (R7, R8, R12): `¬ Run (.spin p) x y` by `generalize`, `induction h with`, `exact ih2 hw`,
`| _ => cases hw`. The exercise adds the `whileF` case, which `Op.spin` has no analogue of.

---

## Part 3 · `prog_result`

Statement: `prog` is `x0 := 1; x1 := x0 + 1`. Whenever it terminates in `s'`, `s' 1 = 2`. No induction:
invert the derivation three times, then compute.

**R13 · `cases h` with `h : Run d x y` for a defined name `d`** changes the **context**: `cases` unfolds `d`
to its constructor (`twoBumps` is `.then_ (.bump 1) (.bump 1)`) and inverts as in R4. Placeholders:
`(P : Nat → Prop) {x y : Nat}`, `def twoBumps : Op`.

| Before | After |
|---|---|
| `h : Run twoBumps x y ⊢ P y` | `y✝ : Nat, a✝¹ : Run (Op.bump 1) x y✝, a✝ : Run (Op.bump 1) y✝ y ⊢ P y` |

Then `cases` on each premise is R3: the `assign` rule fixes the final state, so after
`cases h with | seq h1 h2 => cases h1; cases h2` the goal is `update (update s 0 …) 1 (…) 1 = 2` with
only `s` left in the context.

**R14 · `simp` on `(fun y => if y = k then v else f y) n`** changes the **goal**: `simp` substitutes `n` for
`y` (β-reduction) and decides the numeral equation `n = k`, picking a branch. `simp [update, aeval]` first
unfolds `update s x v` to exactly such a `fun` and `aeval` on `.num`, `.var`, `.plus` to numbers, then
does the arithmetic. Placeholders: `(P : Int → Prop) (f : Nat → Int) (v : Int)`.

| Before | After |
|---|---|
| `⊢ P ((fun y => if y = 0 then v else f y) 1)` | `⊢ P (f 1)` |

**W4** (R13, R3): `Run twoBumps x y → y = x + 2` by `cases h with | then_ h1 h2 => cases h1; cases h2; rfl`.

---

## Traps

- `induction h` on `h : BigStep (.while .tt c) s s'` fails ("Index in target's type is not a variable").
  `generalize` the command first (R7); `cases` does not need this, induction does.
- Forgetting `generalizing s2` (R2): the `seq` and `whileT` IHs then talk about the original `s2` and
  cannot be applied to the middle state.
- In `cases h2 with`, list exactly the rules that survive inversion. A rule that cannot produce the
  command is an error ("Alternative `assign` is not needed"), and so is a missing one ("Alternative
  `iteF` has not been provided").
- Alternative patterns name explicit premises in order, then the IHs: `whileT` has 3 premises
  (`hb`, the body run, the loop run) and 2 IHs, hence `| whileT _ _ _ _ ih2`.
- `subst h1` needs a local variable on one side (`BExp.tt = b✝` is fine; `BExp.tt = BExp.ff` is not:
  that is a clash, R12).
- `h ▸ e` needs a known expected type. As the argument of `ih2` it has one.
- Use `<;>` or `all_goals` after a tactic that leaves several goals; `;` runs only on the first.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induct on a derivation | `induction h with \| rule h1 ih1 => …` | R1 |
| IH for every end state | `induction h1 generalizing s2 with …` | R2 |
| invert a derivation of a fixed command | `cases h2` / `cases h2 with \| rule h1 h2 => …` | R3, R4 |
| use `a = b` to retype a proof | `h ▸ e` | R5 |
| close `b = true` vs `b = false` | `simp_all` | R6 |
| induct when the command is not a variable | `generalize hw : Com.while BExp.tt c = w at h` | R7 |
| what `hw` looks like in each case | `induction h with \| r … => … \| _ => …` | R8 |
| equal constructors → equal arguments | `injection hw with h1 h2` | R9 |
| eliminate `h : a = x` (`x` a variable) | `subst h` | R10 |
| a hypothesis that computes to `False` | `simp [f] at hb` | R11 |
| `hw` equates different constructors | `cases hw` | R12 |
| invert a named program | `cases h` (unfolds the name) | R13 |
| evaluate `update`/`aeval` on numerals | `simp [update, aeval]` | R14 |
| `¬ A` goal | `intro h` | E008 |
| see the state | infoview | |
